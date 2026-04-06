// rust_verify/tests/example.rs ignore --- temporal verification example
//
// Lock deadlock-freedom example.
//
// This example demonstrates proving deadlock freedom for a simple lock
// using temporal logic. The lock is modeled as a mutable integer:
//   0 = free
//   nonzero = held by task with that ID
//
// The liveness property AG(AF(now(*lock == 0))) states:
//   - AG: the loop runs forever
//   - AF(now(*lock == 0)): the lock is always eventually free
//   - now(): the lock being free is a state predicate — it holds at the
//     moment of release, not necessarily at loop body end
//
// This proves deadlock freedom: no task holds the lock forever.
// In each iteration, if the task holds the lock, it releases it (progress).
// If the lock is free, the task acquires and releases it in one step.
//
// Temporal VCGen:
//   - AG: infinite loop (no terminating exit condition)
//   - AF(now): ghost accumulator tracks whether lock == 0 held at any
//     intermediate state during the iteration
//   - decreases: measures whether we hold the lock (1 if held, 0 if free)
//     — releasing the lock decreases this metric

use vstd::prelude::*;

verus! {

/// Prove deadlock freedom: a task that acquires a lock always releases it.
///
/// The temporal postcondition `ag(af(now(*lock == 0)))` means:
///   "The lock is always eventually free"
///
/// This is the simplest form of deadlock freedom — a single task that
/// acquires and releases a lock in a loop. The proof extends to
/// multi-process scenarios via the WP configuration model.
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
