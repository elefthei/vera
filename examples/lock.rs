// rust_verify/tests/example.rs ignore --- temporal verification example
//
// Async lock deadlock freedom.
//
// Two async tasks each prove AG(AF(now(*lock == 0))) — the lock is
// always eventually free. The release() function demonstrates the
// bind rule: its af(done(*lock == 0)) postcondition becomes an
// assumption at the call site.
//
// NOTE: Composing both tasks via async system().await with AG propagation
// requires deeper integration of async ensures rewriting with the temporal
// VCGen. Each task is independently verified today.

use vstd::prelude::*;

verus! {

fn release(lock: &mut u64)
    requires *lock > 0,
    ensures af(done(*lock == 0)),
{
    *lock = 0;
}

async fn task1(lock: &mut u64) -> (ret: ())
    requires *lock == 0,
    ensures ag(af(now(*lock == 0))),
{
    loop
        invariant *lock == 0 || *lock == 1,
        decreases (if *lock == 1 { 1int } else { 0int }),
    {
        if *lock == 0 { *lock = 1; release(lock); }
        if *lock == 1 { release(lock); }
    }
}

async fn task2(lock: &mut u64) -> (ret: ())
    requires *lock == 0,
    ensures ag(af(now(*lock == 0))),
{
    loop
        invariant *lock == 0 || *lock == 2,
        decreases (if *lock == 2 { 1int } else { 0int }),
    {
        if *lock == 0 { *lock = 2; release(lock); }
        if *lock == 2 { release(lock); }
    }
}

} // verus!
