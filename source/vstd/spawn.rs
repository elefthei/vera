#![allow(unused_imports)]

use super::prelude::*;
use core::future::*;
verus! {

/// Process identifier for spawned async tasks.
pub type PID = u64;

/// A spawned process's rely-guarantee contract.
///
/// - `rely`: state predicate that other processes must maintain.
///   "If the shared state satisfies my rely when I'm scheduled, I guarantee my temporal property."
/// - `guarantee`: state predicate that this process maintains (the inner property of AG/AF/AU).
///
/// The verifier checks pairwise compatibility: each process's guarantee
/// implies every other process's rely.
pub ghost struct ProcessContract {
    /// Rely condition: what this process assumes about shared state.
    pub rely: spec_fn(int) -> bool,
    /// Guarantee condition: what this process maintains on shared state.
    pub guarantee: spec_fn(int) -> bool,
}

/// Trait for async executors (schedulers) that can spawn verified processes.
///
/// Types implementing `Executor` carry a ghost process map that tracks
/// all spawned processes and their rely-guarantee contracts.
///
/// # Cooperative Scheduling
///
/// Each process runs until it hits `.await`, then yields.
/// The scheduler picks the next ready process. No preemption.
/// Temporal formulas are over shared state.
pub trait Executor {
    /// Ghost view: map of spawned processes and their contracts.
    #[verifier::prophetic]
    spec fn view(&self) -> Map<PID, ProcessContract>;

    /// Number of spawned processes.
    spec fn num_processes(&self) -> nat;

    /// Spawn a future with temporal contract.
    /// Returns the PID of the spawned process.
    fn spawn<F: Future>(&mut self, future: F) -> (pid: PID)
        ensures
            self@.contains_key(pid),
            self.num_processes() == old(self).num_processes() + 1,
    ;
}

} // verus!
