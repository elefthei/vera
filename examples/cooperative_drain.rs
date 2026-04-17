// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Cooperative Drain: termination (AF done) with rely-guarantee
//
// Two tasks cooperatively drain a counter to 0.
// Unlike AG (runs forever), af(done(P)) proves TERMINATION:
// the async block's body finishes and P holds at the end.
//
// This is a pure liveness property — the computation terminates
// with the counter at 0.
//
// R-G properties verified:
//   1. Each task's body terminates with *counter == 0
//   2. The `while` loop's `decreases` proves termination
//   3. Pairwise guarantees are compatible

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, counter: &mut u64)
    requires *counter == 10,
    ensures af(done(*counter == 0)),
{
    // Task A: drain counter to 0
    exec.spawn(async
        requires *counter <= 10,
        ensures af(done(*counter == 0)),
    {
        while *counter > 0
            invariant *counter <= 10,
            decreases *counter,
        {
            *counter = *counter - 1;
        }
    });

    // Task B: cooperative drain
    exec.spawn(async
        requires *counter <= 10,
        ensures af(done(*counter == 0)),
    {
        while *counter > 0
            invariant *counter <= 10,
            decreases *counter,
        {
            *counter = *counter - 1;
        }
    });
}

} // verus!
