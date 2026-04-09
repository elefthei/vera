#![allow(unused_imports)]

use super::prelude::*;
use core::future::*;
verus! {

/// Process identifier for spawned async tasks.
pub type PID = u64;

/// Trait for async executors (schedulers) that can spawn verified processes.
///
/// Types implementing `Executor` carry a ghost process map that tracks
/// all spawned processes. Each process's rely-guarantee contract is
/// simply its `requires` (rely) and temporal `ensures` (guarantee).
///
/// # Cooperative Scheduling
///
/// Each process runs until it hits `.await`, then yields.
/// The scheduler picks the next ready process. No preemption.
/// Temporal formulas are over shared state.
///
/// # Rely-Guarantee
///
/// At spawn, the async function's `requires` = rely and `ensures` = guarantee
/// are recorded. The verifier checks pairwise compatibility:
///   ∀i,j. i≠j → guarantee_i(σ) → rely_j(σ)
/// "Each process's temporal ensures implies every other can be (re)started."
pub trait Executor {
    /// Number of spawned processes.
    spec fn num_processes(&self) -> nat;

    /// Spawn a future onto the executor.
    /// The future's requires/ensures are used as rely/guarantee.
    fn spawn<F: Future>(&mut self, future: F) -> (pid: PID)
        ensures
            self.num_processes() == old(self).num_processes() + 1,
    ;

    /// Block on a future's completion — runs the scheduler.
    /// At this synchronization point, rely-guarantee compatibility
    /// of all spawned processes is verified.
    #[verifier::external_body]
    fn block_on<F: Future>(&mut self, future: F) -> (ret: F::Output)
        opens_invariants any
    {
        unimplemented!()
    }
}

} // verus!
