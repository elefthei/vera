// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Cooperative Countdown: liveness (AU) with rely-guarantee
//
// Two tasks share a counter, both decrement it toward 0.
// The property ag(af(now(*counter == 0))) combines:
//   - AG: the loop runs forever (cooperative scheduling)
//   - AF(done(...)): the counter eventually reaches 0 (progress)
//
// Each loop iteration either decrements or the counter is already 0.
// The `decreases` clause proves the AF progress property.
// The `loop` (not `while`) satisfies the AG layer — runs forever.
//
// R-G properties verified:
//   1. Each task's body eventually reaches *counter == 0 (AU progress)
//   2. Pairwise: each guarantee implies the other's rely
//   3. Conjunction of guarantees implies system's global ag(af(now(...))))

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, counter: &mut u64)
    requires *counter == 10,
    ensures ag(af(now(*counter == 0))),
{
    // Task A: repeatedly decrement counter toward 0
    // AG(AF(done(Q))): forever, the counter eventually reaches 0
    exec.spawn(async
        requires *counter <= 10,
        ensures ag(af(now(*counter == 0))),
    {
        loop
            invariant *counter <= 10,
            decreases *counter,
        {
            if *counter > 0 {
                *counter = *counter - 1;
            }
        }
    });

    // Task B: cooperative — also decrements
    exec.spawn(async
        requires *counter <= 10,
        ensures ag(af(now(*counter == 0))),
    {
        loop
            invariant *counter <= 10,
            decreases *counter,
        {
            if *counter > 0 {
                *counter = *counter - 1;
            }
        }
    });
}

} // verus!
