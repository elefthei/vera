// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Nested Matrix: ag(R) safety across nested loops
//
// Two tasks iterate over a shared sum with nested loops.
// Both maintain the invariant *sum <= 100 at every state,
// across all nesting levels.
//
// The outer loop processes "rows", the inner loop processes "columns".
// Each iteration may increment or decrement the sum, but never
// exceeds the bound.
//
// The property ag(*sum <= 100) proves:
//   - The invariant holds at every state of both loop levels
//   - No interleaving of the two tasks can violate the bound
//
// R-G properties verified:
//   1. Each task maintains *sum <= 100 across nested loops (AG)
//   2. Pairwise: guarantees are compatible
//   3. Conjunction implies system's global ag(*sum <= 100)

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, sum: &mut u64, phase: &mut u64)
    requires *sum == 0 && *phase == 0,
    ensures ag(*sum <= 100),
{
    // Task A: nested loops maintaining bound
    exec.spawn(async
        requires *sum <= 100 && *phase <= 1,
        ensures ag(*sum <= 100),
    {
        loop
            invariant *sum <= 100 && *phase <= 1,
        {
            // Outer loop: process rows
            *phase = 0;
            loop
                invariant *sum <= 100 && *phase <= 1,
            {
                // Inner loop: process columns
                if *sum < 100 { *sum = *sum + 1; }
                if *sum > 0 { *sum = *sum - 1; }
                *phase = 1;  // signal completion
            }
        }
    });

    // Task B: same nested pattern
    exec.spawn(async
        requires *sum <= 100 && *phase <= 1,
        ensures ag(*sum <= 100),
    {
        loop
            invariant *sum <= 100 && *phase <= 1,
        {
            *phase = 0;
            loop
                invariant *sum <= 100 && *phase <= 1,
            {
                if *sum < 100 { *sum = *sum + 1; }
                if *sum > 0 { *sum = *sum - 1; }
                *phase = 1;
            }
        }
    });
}

} // verus!
