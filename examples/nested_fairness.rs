// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Nested Fairness: ag(af(now)) with progress cycle
//
// Two tasks run a batch processor:
//   - Loop runs forever (AG layer)
//   - Each iteration drains batch toward 0 (AF layer)
//   - When batch hits 0 (now goal), it refills for next cycle
//
// The property ag(af(now(*batch == 0))) proves:
//   - AG: the system runs forever
//   - AF(now(...)): each batch is eventually drained to 0
//
// This demonstrates REPEATED progress: drain → refill → drain → ...
// The decreases *batch proves the AF progress property.
//
// R-G properties verified:
//   1. Each task's outer loop runs forever (AG)
//   2. Each inner loop drains the batch (AF progress via decreases)
//   3. Pairwise guarantees are compatible

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, batch: &mut u64)
    requires *batch == 0,
    ensures ag(af(now(*batch == 0))),
{
    // Task A: process batches repeatedly
    exec.spawn(async
        requires *batch <= 10,
        ensures ag(af(now(*batch == 0))),
    {
        loop
            invariant *batch <= 10,
            decreases *batch,
        {
            // Drain current batch toward 0
            if *batch > 0 {
                *batch = *batch - 1;
            }
            // When *batch == 0: AF(now) goal reached, then refill
            if *batch == 0 {
                *batch = 10;
            }
        }
    });

    // Task B: same batch processing
    exec.spawn(async
        requires *batch <= 10,
        ensures ag(af(now(*batch == 0))),
    {
        loop
            invariant *batch <= 10,
            decreases *batch,
        {
            if *batch > 0 {
                *batch = *batch - 1;
            }
            if *batch == 0 {
                *batch = 10;
            }
        }
    });
}

} // verus!
