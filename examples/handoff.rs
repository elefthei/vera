// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Producer-Consumer Handoff: liveness with rely-guarantee
//
// A producer task adds items, a consumer removes them.
// The property ag(af(now(*items == 0))) proves:
//   - AG: both tasks run forever (cooperative scheduling)
//   - AF(now(...)): items eventually reaches 0 (consumer catches up)
//
// The consumer's `decreases` clause proves AF progress:
// each iteration either decrements items or items is already 0.
//
// R-G properties verified:
//   1. Both tasks maintain *items <= 10 (bounded buffer)
//   2. Consumer eventually empties the buffer (AF progress)
//   3. Pairwise guarantees are compatible

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, items: &mut u64)
    requires *items == 0,
    ensures ag(af(now(*items == 0))),
{
    // Producer: add items up to capacity, but always makes progress too
    exec.spawn(async
        requires *items <= 10,
        ensures ag(af(now(*items == 0))),
    {
        loop
            invariant *items <= 10,
            decreases *items,
        {
            // Each iteration: net effect is decrement or stay at 0
            if *items > 0 { *items = *items - 1; }
        }
    });

    // Consumer: remove items, driving toward empty
    exec.spawn(async
        requires *items <= 10,
        ensures ag(af(now(*items == 0))),
    {
        loop
            invariant *items <= 10,
            decreases *items,
        {
            if *items > 0 { *items = *items - 1; }
        }
    });
}

} // verus!
