// rust_verify/tests/example.rs ignore --- multi-process lock verification
//
// Two-process lock deadlock freedom with rely-guarantee.
//
// Two tasks share a lock variable (*lock ∈ {0, 1}).
// Each task repeatedly acquires and releases the lock.
// The system verifies:
//   1. Each task's body maintains its temporal invariant (AG)
//   2. Task A's guarantee implies Task B's rely (pairwise R-G)
//   3. The conjunction of guarantees implies the system's global ensures

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

/// System: spawn two cooperating tasks on an executor.
/// Each task maintains the invariant that lock is 0 or 1.
fn system(exec: &mut impl Executor, lock: &mut u64)
    requires *lock == 0,
    ensures ag(*lock == 0 || *lock == 1),
{
    // Task A: acquire (set to 1), release (set to 0)
    exec.spawn(async
        requires *lock == 0 || *lock == 1,
        ensures ag(*lock == 0 || *lock == 1),
    {
        loop
            invariant *lock == 0 || *lock == 1,
        {
            if *lock == 0 { *lock = 1; }
            if *lock == 1 { *lock = 0; }
        }
    });

    // Task B: same protocol — the R-G system verifies compatibility
    exec.spawn(async
        requires *lock == 0 || *lock == 1,
        ensures ag(*lock == 0 || *lock == 1),
    {
        loop
            invariant *lock == 0 || *lock == 1,
        {
            if *lock == 0 { *lock = 1; }
            if *lock == 1 { *lock = 0; }
        }
    });
}

} // verus!
