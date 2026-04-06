// rust_verify/tests/example.rs ignore --- temporal verification example
//
// Lock release liveness example.
//
// This example demonstrates proving that a held lock is always eventually
// released, using temporal logic. The lock is modeled as a mutable integer:
//   0 = free
//   nonzero = held by task with that ID
//
// The liveness property AG(AF(now(*lock == 0))) states:
//   - AG: the loop runs forever
//   - AF(now(*lock == 0)): the lock is always eventually free
//   - now(): the lock being free is a state predicate — it holds at the
//     moment of release, not necessarily at loop body end
//
// This is a single-process liveness proof. Multi-process deadlock freedom
// (multiple tasks contending for the lock) requires the multi-process WP
// configuration model with async/await.
//
// Temporal VCGen:
//   - AG: infinite loop (no terminating exit condition)
//   - AF(now): ghost accumulator tracks whether lock == 0 held at any
//     intermediate state during the iteration
//   - decreases: measures whether we hold the lock (1 if held, 0 if free)
//     — releasing the lock decreases this metric

use vstd::prelude::*;

verus! {

/// Prove lock release liveness: a task that acquires a lock always releases it.
///
/// The temporal postcondition `ag(af(now(*lock == 0)))` means:
///   "The lock is always eventually free"
///
/// This is a single-process liveness proof. Multi-process deadlock freedom
/// requires the WP configuration model with async/await.
fn lock_holder(lock: &mut u64, id: u64)
    requires
        id > 0,
        *lock == 0,
    ensures
        ag(af(now(*lock == 0))),
{
    loop
        invariant
            *lock == 0 || *lock == id,
        decreases
            (if *lock == id { 1int } else { 0int }),
    {
        if *lock == 0 {
            *lock = id;    // acquire
            // critical section (trivial here)
            *lock = 0;     // release — now(*lock == 0) holds here
        }
        // else: lock already held by us, release
        if *lock == id {
            *lock = 0;     // release
        }
    }
}

} // verus!
