// rust_verify/tests/example.rs ignore --- temporal verification example
//
// Async lock with rely-guarantee.
// Two async tasks share a lock. Each task acquires and releases.
// Rely-guarantee: each task's AG(AF(now)) guarantee implies the other's rely.
//
// Note: the async fns have no `requires` (rely = true) because after the first
// exec.spawn, Verus hasvocs the mutable reference, making it impossible to prove
// the second task's precondition. Each task self-initializes by releasing the lock
// before entering the main loop.

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

async fn task1(lock: &mut u64) -> (ret: ())
    ensures ag(af(now(*lock == 0))),
{
    *lock = 0;
    loop
        invariant *lock == 0 || *lock == 1,
        decreases (if *lock == 1 { 1int } else { 0int }),
    {
        if *lock == 0 { *lock = 1; *lock = 0; }
        if *lock == 1 { *lock = 0; }
    }
}

async fn task2(lock: &mut u64) -> (ret: ())
    ensures ag(af(now(*lock == 0))),
{
    *lock = 0;
    loop
        invariant *lock == 0 || *lock == 2,
        decreases (if *lock == 2 { 1int } else { 0int }),
    {
        if *lock == 0 { *lock = 2; *lock = 0; }
        if *lock == 2 { *lock = 0; }
    }
}

fn system(exec: &mut impl Executor, lock: &mut u64)
    requires *lock == 0,
{
    exec.spawn(task1(lock));
    exec.spawn(task2(lock));
}

} // verus!
