// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Terminating Election: af(done) with rely-guarantee
//
// Two candidates compete to become leader. Once elected, the task terminates.
// af(done(*elected > 0)) proves the election TERMINATES with a winner.
//
// This is different from the AG election example: there, the system runs
// forever. Here, it terminates once a leader is found.
//
// R-G properties verified:
//   1. Each task terminates with *elected > 0 (leader found)
//   2. The `while` loop's `decreases` proves termination
//   3. Pairwise: both candidates are compatible

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, elected: &mut u64)
    requires *elected == 0,
    ensures af(done(*elected > 0)),
{
    // Candidate A: try to become leader, then stop
    exec.spawn(async
        requires *elected <= 2,
        ensures af(done(*elected > 0)),
    {
        while *elected == 0
            invariant *elected <= 2,
            decreases (if *elected > 0 { 0int } else { 1int }),
        {
            *elected = 1;
        }
    });

    // Candidate B: try to become leader, then stop
    exec.spawn(async
        requires *elected <= 2,
        ensures af(done(*elected > 0)),
    {
        while *elected == 0
            invariant *elected <= 2,
            decreases (if *elected > 0 { 0int } else { 1int }),
        {
            *elected = 2;
        }
    });
}

} // verus!
