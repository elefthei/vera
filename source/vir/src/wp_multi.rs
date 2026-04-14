//! Multi-process weakest precondition for async Rust.
//!
//! This module defines the multi-process configuration `C = (P, σ, i)` and
//! the `MultiProcessWp` trait that extends `SingleProcessWp` with async/await.
//!
//! The two-layer wp/WP architecture:
//! - `SingleProcessWp` (`wp`): sequential Rust (assignment, let, if, while, call)
//! - `MultiProcessWp` (`WP`): extends with async/await (process dictionary, cooperative scheduling)
//!
//! Programs without async/await reduce to single-process wp:
//!   `WP({0 → t}, σ, 0, φ) = wp(t, φ) σ`

use crate::ast::Fun;
use crate::context::Ctx;
use crate::sst::{Exp, Pars};
use crate::wp_context::{Proposition, SpawnedClosureSpec, SpawnedProcess, extract_callee_temporal_ensures, decompose_temporal};
use std::sync::Arc;

/// Process identifier.
pub type PID = u64;

/// Multi-process configuration `C = (P, σ, i)`.
///
/// - `P`: process map — spawned processes with their temporal contracts
/// - `σ`: shared mutable state (implicit — tracked by AIR variables)
/// - `i`: currently active (scheduled) process
pub struct Configuration {
    /// Spawned processes with their temporal contracts.
    pub processes: Vec<SpawnedProcess>,
}

impl Configuration {
    /// Create an empty configuration.
    pub fn new() -> Self {
        Configuration { processes: Vec::new() }
    }

    /// Spawn an async process. Records its function name, parameters,
    /// temporal propositions, and relies for rely-guarantee checking.
    pub fn spawn(&mut self, fun: Fun, pars: Pars, propositions: Vec<Proposition>, relies: Vec<Exp>) -> PID {
        let pid = self.processes.len() as PID;
        self.processes.push(SpawnedProcess { fun, pars, propositions, relies });
        pid
    }

    /// Number of spawned processes.
    pub fn len(&self) -> usize {
        self.processes.len()
    }

    /// Is the configuration empty?
    pub fn is_empty(&self) -> bool {
        self.processes.is_empty()
    }
}

/// Multi-process weakest precondition trait.
///
/// Extends `SingleProcessWp` with spawn detection and rely-guarantee checking.
/// The trait operates on a `Configuration` tracking all spawned processes.
///
/// Cooperative scheduling model:
/// - Each process runs until it hits `.await`, then yields
/// - The scheduler picks the next process from the ready set
/// - Temporal formulas φ are over shared state σ
pub trait MultiProcessWp {
    /// Get the multi-process configuration.
    fn configuration(&self) -> &Configuration;

    /// Get mutable access to the configuration.
    fn configuration_mut(&mut self) -> &mut Configuration;

    /// WP for `exec.spawn(async_fn(args))`: record the spawned process.
    /// Returns the PID of the new process.
    fn wp_spawn(&mut self, ctx: &Ctx, fun: &Fun) -> PID {
        if let Some(callee_sst) = ctx.func_sst_map.get(fun) {
            let props = extract_callee_temporal_ensures(callee_sst);
            let relies: Vec<Exp> = callee_sst.x.decl.reqs.to_vec();
            if !props.is_empty() {
                return self.configuration_mut().spawn(
                    fun.clone(),
                    callee_sst.x.pars.clone(),
                    props,
                    relies,
                );
            }
            return self.configuration_mut().spawn(
                fun.clone(),
                Arc::new(vec![]),
                vec![],
                relies,
            );
        }
        // No func_sst_map entry — still record for tracking
        self.configuration_mut().spawn(
            fun.clone(),
            Arc::new(vec![]),
            vec![],
            vec![],
        )
    }

    /// WP for `exec.spawn(async requires R ensures G { body })`.
    /// Extract temporal propositions from the inline ensures and add to config.
    fn wp_spawn_closure(&mut self, spec: &SpawnedClosureSpec) -> PID {
        let mut props = Vec::new();
        for ens in spec.ensures.iter() {
            extract_temporal_from_exp(ens, &mut props);
        }
        let synthetic_fun = Arc::new(crate::ast::FunX {
            path: Arc::new(crate::ast::PathX {
                krate: None,
                segments: Arc::new(vec![Arc::new("__async_block".to_string())]),
            }),
        });
        self.configuration_mut().spawn(
            synthetic_fun,
            Arc::new(vec![]),
            props,
            spec.requires.clone(), // relies stored directly from the async block's requires
        )
    }
}

/// Extract temporal propositions from a raw SST ensures expression.
fn extract_temporal_from_exp(exp: &Exp, obligations: &mut Vec<Proposition>) {
    use crate::sst::ExpX;
    match &exp.x {
        ExpX::Temporal(op, prop, path_prop) => {
            decompose_temporal(op, prop, path_prop, false, obligations);
        }
        ExpX::Binary(crate::ast::BinaryOp::Implies, _, rhs) => {
            extract_temporal_from_exp(rhs, obligations);
        }
        ExpX::Bind(_, body) => {
            extract_temporal_from_exp(body, obligations);
        }
        _ => {}
    }
}

/// Check if a function call is to Executor::block_on.
pub fn is_block_on(fun: &Fun) -> bool {
    fun.path.segments.iter().any(|seg| seg.as_str() == "block_on")
        && (fun.path.krate.as_ref().map_or(false, |k| k.as_str() == "vstd")
            || crate::def::fun_to_string(fun).contains("Executor"))
}
