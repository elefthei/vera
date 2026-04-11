// rust_verify/tests/example.rs ignore --- temporal verification example
//
// Async lock deadlock freedom with await-AG propagation.
//
// system() calls task1(lock).await with ensures ag(af(now(*lock == 0))).
// The callee's AG temporal ensures discharge the caller's AG obligation
// via temporal implication checking at the call site.

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

async fn system(lock: &mut u64) -> (ret: ())
    requires *lock == 0,
    ensures ag(af(now(*lock == 0))),
{
    task1(lock).await
}

} // verus!
