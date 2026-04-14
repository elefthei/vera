//! Temporal verification context for TICL-based weakest preconditions.
//!
//! This module defines the temporal proposition types and context used by
//! Vera's VCGen to track temporal obligations from `ensures` clauses.
//! It also provides helpers for decomposing temporal expressions into
//! flat leaf obligations.

use crate::ast::Ident;
use crate::sst::{Exp, ExpX, FunctionSst};

/// Whether a temporal goal is a state predicate (Now) or termination condition (Done).
/// - `Now`: the goal is checked at the state where it first holds; it is NOT checked at return.
/// - `Done`: the goal is checked at function return (termination postcondition).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum GoalKind {
    /// State predicate — goal reached when the condition first holds (not checked at return).
    Now,
    /// Termination condition — goal is checked at function return.
    Done,
}

/// A leaf temporal obligation decomposed from `ensures` clauses.
///
/// Each variant describes a temporal property over computation traces:
/// - **Always**: Holds at every state forever (AG). Requires infinite loop.
/// - **Until**: Holds along a path until a goal is reached (AU). Requires progress.
///   `af(Q)` desugars to `Until(true, Q)`.
#[derive(Clone, Debug)]
pub enum Proposition {
    /// AG(φ): φ must hold at every state of an infinite computation.
    Always {
        property: Exp,
        /// True when nested inside an outer AG (coinductive invariance).
        requires_invariance: bool,
    },
    /// AU(φ, ψ): path property φ holds at every state until goal ψ is reached.
    /// af(Q) desugars to AU(true, Q).
    Until {
        path: Exp,
        goal: Exp,
        /// Whether the goal is a state predicate (Now) or termination condition (Done).
        goal_kind: GoalKind,
        /// True when nested inside an outer AG (coinductive invariance).
        requires_invariance: bool,
    },
}

impl Proposition {
    pub fn is_always(&self) -> bool {
        matches!(self, Proposition::Always { .. })
    }

    pub fn is_until(&self) -> bool {
        matches!(self, Proposition::Until { .. })
    }

    pub fn requires_invariance(&self) -> bool {
        match self {
            Proposition::Always { requires_invariance, .. }
            | Proposition::Until { requires_invariance, .. } => *requires_invariance,
        }
    }
}

/// Collection of temporal obligations for the current function.
///
/// Contains the propositions decomposed from the function's `ensures` clause.
/// Each proposition drives a different verification obligation:
/// - `Always { property }`: requires an infinite loop whose invariant implies the property.
/// - `Until { path, goal }`: requires a terminating loop that makes progress toward the goal.
#[derive(Clone, Debug, Default)]
pub struct PropositionContext {
    pub propositions: Vec<Proposition>,
}

impl PropositionContext {
    /// Returns `true` when the context contains an Always obligation or any
    /// obligation nested inside an outer AG (i.e., `requires_invariance`).
    pub fn has_always(&self) -> bool {
        self.propositions.iter().any(|o| o.is_always() || o.requires_invariance())
    }

    /// Returns `true` when the context contains any Until obligation
    /// (including `af(Q)` which desugars to `Until(true, Q)`).
    pub fn has_until(&self) -> bool {
        self.propositions.iter().any(|o| o.is_until())
    }

    /// Returns `true` when the context contains an Until obligation nested
    /// inside an outer AG (i.e., `requires_invariance` is true).
    /// This detects AG(AF(Q)) and AG(AU(P,Q)) compositions which require
    /// decreases for liveness progress.
    pub fn has_invariance_until(&self) -> bool {
        self.propositions.iter().any(|o| o.is_until() && o.requires_invariance())
    }
}

/// Temporal verification state threaded through wp.
///
/// Tracks the temporal obligations derived from the function's `ensures` clause
/// and the verification state as we traverse the function body.
pub struct WpContext {
    /// Temporal obligations from ensures clauses.
    pub temporal_context: PropositionContext,
    /// Set to true when any loop discharges temporal obligations.
    pub temporal_discharged: bool,
    /// Set to true when a loop without decreases exists (AG = infinite loop).
    pub has_infinite_temporal_loop: bool,
    /// Properties that must hold at every intermediate state in prefix code
    /// before the temporal loop. AG(φ) → [φ], AU(path, goal) → [path].
    pub temporal_prefix_obligations: Vec<Exp>,
    /// Depth counter for loop nesting — prefix assertions only fire outside all loops.
    pub in_loop_depth: u32,
    /// AG(φ) properties asserted at every intermediate state inside an AG loop body.
    pub ag_state_obligations: Vec<Exp>,
    /// AU(φ,ψ) path+goal pairs asserted at every intermediate state inside AU loops.
    pub au_path_obligations: Vec<(Exp, Exp)>,
    /// Ghost accumulators for now() goals in AG(AF) loops.
    /// Each entry is (goal_expr, accumulator_air_ident).
    pub now_goal_accumulators: Vec<(Exp, Ident)>,
    /// Counter for generating unique snapshot names for now() goal accumulators.
    pub now_acc_snapshot_counter: u32,
    /// Monotonically increasing counter for unique now_reached variable names.
    pub now_reached_counter: u32,
    /// Multi-process configuration tracking spawned async processes.
    /// Populated by MultiProcessWp::wp_spawn, checked by emit_rely_guarantee_checks.
    pub config: crate::wp_multi::Configuration,
}

/// A spawned process's identity and temporal contract.
pub struct SpawnedProcess {
    /// The spawned async function's name.
    pub fun: crate::ast::Fun,
    /// The callee's parameters (for Havoc+Assume binding at check time).
    pub pars: crate::sst::Pars,
    /// The temporal propositions extracted from the function's ensures.
    pub propositions: Vec<Proposition>,
    /// The process's rely conditions (requires). Stored directly so R-G checks
    /// work for both named functions and anonymous async blocks.
    pub relies: Vec<Exp>,
}

/// Specs from an inline async block passed to spawn.
/// Carries the SST-level requires/ensures for R-G checking.
#[derive(Clone, Debug)]
pub struct SpawnedClosureSpec {
    pub requires: Vec<Exp>,
    pub ensures: Vec<Exp>,
}

impl crate::printer::ToDebugSNode for SpawnedClosureSpec {
    fn to_node(&self, _opts: &crate::printer::ToDebugSNodeOpts) -> sise::Node {
        sise::Node::Atom(format!("SpawnedClosureSpec(reqs={}, ens={})", self.requires.len(), self.ensures.len()))
    }
}

impl WpContext {
    pub fn new(
        temporal_context: PropositionContext,
        temporal_prefix_obligations: Vec<Exp>,
    ) -> Self {
        WpContext {
            temporal_context,
            temporal_discharged: false,
            has_infinite_temporal_loop: false,
            temporal_prefix_obligations,
            in_loop_depth: 0,
            ag_state_obligations: Vec::new(),
            au_path_obligations: Vec::new(),
            now_goal_accumulators: Vec::new(),
            now_acc_snapshot_counter: 0,
            now_reached_counter: 0,
            config: crate::wp_multi::Configuration::new(),
        }
    }
}

// ---------------------------------------------------------------------------
// Temporal decomposition helpers
// ---------------------------------------------------------------------------

/// Decompose a temporal ensures expression into Proposition obligations.
/// Recursively unwraps nested temporal operators (e.g., AG(AF(Q))) into
/// leaf obligations (Always/Until) that the VCGen can process.
pub fn decompose_temporal(
    op: &crate::ast::TemporalOp,
    prop: &Exp,
    path_prop: &Option<Exp>,
    inside_ag: bool,
    obligations: &mut Vec<Proposition>,
) {
    let inside_ag =
        inside_ag || matches!(op, crate::ast::TemporalOp::AG | crate::ast::TemporalOp::EG);
    match &prop.x {
        ExpX::Temporal(inner_op, inner_prop, inner_path) => {
            decompose_temporal(inner_op, inner_prop, inner_path, inside_ag, obligations);
        }
        _ => {
            let obligation = match op {
                crate::ast::TemporalOp::AG | crate::ast::TemporalOp::EG => Proposition::Always {
                    property: prop.clone(),
                    requires_invariance: inside_ag,
                },
                crate::ast::TemporalOp::AU
                | crate::ast::TemporalOp::EU
                | crate::ast::TemporalOp::AN
                | crate::ast::TemporalOp::EN => {
                    let raw_goal =
                        path_prop.clone().expect("AU/EU/AN/EN requires a goal (second argument)");
                    let (goal, goal_kind) = extract_goal_kind(raw_goal);
                    Proposition::Until {
                        path: prop.clone(),
                        goal,
                        goal_kind,
                        requires_invariance: inside_ag,
                    }
                }
            };
            obligations.push(obligation);
        }
    }
}

/// Extract the goal kind (Now vs Done) from a temporal goal expression.
/// Strips the Now/Done wrapper if present; defaults to Done for backward compatibility.
pub fn extract_goal_kind(raw_goal: Exp) -> (Exp, GoalKind) {
    match &raw_goal.x {
        ExpX::Now(inner) => (inner.clone(), GoalKind::Now),
        ExpX::Done(inner) => (inner.clone(), GoalKind::Done),
        _ => (raw_goal, GoalKind::Done),
    }
}

/// Extract temporal ensures from a callee's SST function declaration.
/// Walks the callee's ensures expressions to find ExpX::Temporal nodes
/// and decomposes them into Proposition objects.
/// For async functions, temporal expressions may be nested inside
/// Binary(Implies, awaited(), ...) wrappers — we walk through these.
pub fn extract_callee_temporal_ensures(func: &FunctionSst) -> Vec<Proposition> {
    fn find_temporal(exp: &Exp, obligations: &mut Vec<Proposition>) {
        match &exp.x {
            ExpX::Temporal(op, prop, path_prop) => {
                decompose_temporal(op, prop, path_prop, false, obligations);
            }
            // Walk through Binary(Implies, ...) wrappers (from async ensures rewriting)
            ExpX::Binary(crate::ast::BinaryOp::Implies, _, rhs) => {
                find_temporal(rhs, obligations);
            }
            // Walk through Bind/Let wrappers
            ExpX::Bind(_, body) => {
                find_temporal(body, obligations);
            }
            _ => {}
        }
    }
    let mut obligations = Vec::new();
    for ens in func.x.decl.enss.0.iter().chain(func.x.decl.enss.1.iter()) {
        find_temporal(ens, &mut obligations);
    }
    obligations
}

/// Check if a callee's AST ensures contain temporal operators.
/// Returns true if any ensure is an ExprX::Temporal expression.
pub fn callee_has_temporal_ensures(func: &crate::ast::Function) -> bool {
    let (regular, defaults) = &func.x.ensure;
    regular.iter().chain(defaults.iter()).any(|e| matches!(&e.x, crate::ast::ExprX::Temporal(..)))
}
