// rust_verify/tests/example.rs ignore --- temporal verification example
//
// Async lock deadlock-freedom example.
//
// Two async tasks share a lock (modeled as &mut u64, 0=free, 1/2=held).
// Each task acquires the lock, does work, and releases it.
//
// The temporal postcondition AG(AF(now(*lock == 0))) on each task means:
//   "The lock is always eventually free"
//
// This demonstrates rely-guarantee reasoning for async processes:
// - Each task RELIES on the lock starting in a valid state
// - Each task GUARANTEES it always eventually releases (ag(af(now(*lock == 0))))
//
// The individual async functions are verified with single-process temporal
// logic. The multi-process rely-guarantee composition (checking that each
// task's guarantee implies the other's rely) will be checked by the
// Executor::spawn VCGen once wired in.

use vstd::prelude::*;

verus! {

/// Async task 1: acquires lock with id=1, always eventually releases.
async fn task1(lock: &mut u64) -> (ret: ())
    requires *lock == 0,
    ensures ag(af(now(*lock == 0))),
{
    loop
        invariant *lock == 0 || *lock == 1,
        decreases (if *lock == 1 { 1int } else { 0int }),
    {
        if *lock == 0 {
            *lock = 1;   // acquire
            *lock = 0;   // release
        }
        if *lock == 1 {
            *lock = 0;   // release
        }
    }
}

/// Async task 2: acquires lock with id=2, always eventually releases.
async fn task2(lock: &mut u64) -> (ret: ())
    requires *lock == 0,
    ensures ag(af(now(*lock == 0))),
{
    loop
        invariant *lock == 0 || *lock == 2,
        decreases (if *lock == 2 { 1int } else { 0int }),
    {
        if *lock == 0 {
            *lock = 2;   // acquire
            *lock = 0;   // release
        }
        if *lock == 2 {
            *lock = 0;   // release
        }
    }
}

// In the full multi-process model, the system entry point would be:
//
//   fn system(exec: &mut impl Executor, lock: &mut u64)
//       requires *lock == 0,
//       ensures ag(af(now(*lock == 0))),
//   {
//       exec.spawn(task1(lock));
//       exec.spawn(task2(lock));
//   }
//
// The Executor::spawn VCGen would check rely-guarantee compatibility:
//   guarantee_1 → rely_2 and guarantee_2 → rely_1
//
// For now, each task is independently verified with temporal logic.

} // verus!
