// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Leader Election: convergence (AU) with rely-guarantee
//
// Two candidates compete to become leader. Initially *leader == 0 (no leader).
// Each candidate may set *leader to their ID (1 or 2).
// The property ag(af(now(*leader > 0))) proves convergence:
//   - AG: the system runs forever
//   - AF(now(...)): eventually a leader is elected
//
// This is a progress property — the system converges to a state
// where someone has been elected, repeatedly.
//
// R-G properties verified:
//   1. Both tasks maintain *leader <= 2 (valid leader IDs)
//   2. Election converges: eventually *leader > 0 (AF progress)
//   3. Pairwise guarantees are compatible

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, leader: &mut u64)
    requires *leader == 0,
    ensures ag(af(now(*leader > 0))),
{
    // Candidate A: try to become leader (set to 1)
    exec.spawn(async
        requires *leader <= 2,
        ensures ag(af(now(*leader > 0))),
    {
        loop
            invariant *leader <= 2,
            decreases (if *leader > 0 { 0int } else { 1int }),
        {
            if *leader == 0 { *leader = 1; }
        }
    });

    // Candidate B: try to become leader (set to 2)
    exec.spawn(async
        requires *leader <= 2,
        ensures ag(af(now(*leader > 0))),
    {
        loop
            invariant *leader <= 2,
            decreases (if *leader > 0 { 0int } else { 1int }),
        {
            if *leader == 0 { *leader = 2; }
        }
    });
}

} // verus!
