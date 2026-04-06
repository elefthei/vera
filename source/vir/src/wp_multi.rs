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

use crate::ast::VirErr;
use crate::context::Ctx;
use crate::sst::Stm;
use air::ast::Stmt;
use std::collections::HashMap;
use std::sync::Arc;

/// Process identifier.
pub type PID = u64;

/// Process dictionary: maps PIDs to suspended Rust terms.
///
/// Each entry represents an async process (future) with its current
/// program term. The active process runs until it hits `.await`,
/// then the scheduler picks the next ready process.
pub struct ProcessDict {
    processes: HashMap<PID, Arc<Stm>>,
    next_pid: PID,
}

impl ProcessDict {
    /// Create a new process dictionary with a single main process.
    pub fn new(main_body: Arc<Stm>) -> Self {
        let mut processes = HashMap::new();
        processes.insert(0, main_body);
        ProcessDict { processes, next_pid: 1 }
    }

    /// Spawn a new process with the given body. Returns the fresh PID.
    pub fn spawn(&mut self, body: Arc<Stm>) -> PID {
        let pid = self.next_pid;
        self.next_pid += 1;
        self.processes.insert(pid, body);
        pid
    }

    /// Look up a process's current term.
    pub fn get(&self, pid: PID) -> Option<&Arc<Stm>> {
        self.processes.get(&pid)
    }

    /// Update a process's term (e.g., after partial execution or resumption).
    pub fn update(&mut self, pid: PID, new_body: Arc<Stm>) {
        self.processes.insert(pid, new_body);
    }
}

/// Multi-process configuration `C = (P, σ, i)`.
///
/// - `P`: process dictionary mapping PIDs to Rust terms
/// - `σ`: shared mutable state (implicit — tracked by AIR variables)
/// - `i`: currently active (scheduled) process
pub struct Configuration {
    pub processes: ProcessDict,
    pub active: PID,
}

impl Configuration {
    /// Create a configuration with a single main process.
    pub fn new(main_body: Arc<Stm>) -> Self {
        Configuration {
            processes: ProcessDict::new(main_body),
            active: 0,
        }
    }

    /// Spawn an async process. Returns the PID of the new process.
    /// The active process is unchanged.
    pub fn spawn(&mut self, body: Arc<Stm>) -> PID {
        self.processes.spawn(body)
    }

    /// Switch the active process to `pid`.
    pub fn switch_to(&mut self, pid: PID) {
        self.active = pid;
    }

    /// Get the active process's current term.
    pub fn active_term(&self) -> Option<&Arc<Stm>> {
        self.processes.get(self.active)
    }
}

/// Multi-process weakest precondition trait.
///
/// Extends `SingleProcessWp` with async/await constructs.
/// The `WP` operates on a `Configuration` and delegates sequential
/// steps to the single-process `wp`.
///
/// Cooperative scheduling model:
/// - Each process runs until it hits `.await`, then yields
/// - The scheduler picks the next process from the ready set
/// - Temporal formulas φ are over shared state σ
pub trait MultiProcessWp {
    /// WP for a sequential step: delegate to single-process wp.
    ///
    /// When `P(i)` is a non-async construct, `WP(C, φ) = wp(P(i), φ) σ`.
    fn wp_sequential(&mut self, ctx: &Ctx, stm: &Stm) -> Result<Vec<Stmt>, VirErr>;

    /// WP for `async { e }`: spawn a future, extend P.
    ///
    /// `WP((P, σ, i), φ) = WP((P[p ↦ e], σ, i), φ)`
    ///
    /// Creates new process `p` with body `e` (suspended).
    /// Active process `i` continues running unchanged.
    /// No state change, no scheduling — futures are lazy.
    fn wp_async(&mut self, ctx: &Ctx, body: &Stm) -> Result<(PID, Vec<Stmt>), VirErr>;

    /// WP for `p.await` (AU callee — terminating):
    ///
    /// `WP((P, σ, i), φ AU φ') =`
    ///   `WP((P, σ, p), φ AU done R)`
    ///   `∧ ∀x, σ'. R x σ' → WP((P[i ↦ k[x]], σ', i), φ AU φ')`
    ///
    /// Switch active to `p`, run it maintaining `φ`, get result, resume `i`.
    fn wp_await_au(
        &mut self,
        ctx: &Ctx,
        future_pid: PID,
        continuation: &Stm,
    ) -> Result<Vec<Stmt>, VirErr>;

    /// WP for `p.await` (AG callee — diverging):
    ///
    /// `WP((P, σ, i), AG φ) = wp(P(p), AG φ) σ`
    ///
    /// Reduces to single-process wp on callee's body.
    /// Process `p` runs forever; continuation is unreachable.
    fn wp_await_ag(&mut self, ctx: &Ctx, future_pid: PID) -> Result<Vec<Stmt>, VirErr>;
}
