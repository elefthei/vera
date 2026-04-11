// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Bounded Counter: symmetric rely-guarantee
//
// Two tasks share a counter. Each may increment it, but the R-G system
// verifies that the counter never exceeds 100.
//
// R-G properties verified:
//   1. Each task's body maintains ag(*counter <= 100) (loop invariant)
//   2. Pairwise: A's guarantee implies B's rely (symmetric — trivially compatible)
//   3. Conjunction of guarantees implies system's global ensures

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, counter: &mut u64)
    requires *counter == 0,
    ensures ag(*counter <= 100),
{
    // Task A: increment if below limit
    exec.spawn(async
        requires *counter <= 100,
        ensures ag(*counter <= 100),
    {
        loop
            invariant *counter <= 100,
        {
            if *counter < 100 { *counter = *counter + 1; }
        }
    });

    // Task B: same contract — symmetric R-G
    exec.spawn(async
        requires *counter <= 100,
        ensures ag(*counter <= 100),
    {
        loop
            invariant *counter <= 100,
        {
            if *counter < 100 { *counter = *counter + 1; }
        }
    });
}

} // verus!
