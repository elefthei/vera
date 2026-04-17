// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Nested Drain: af(done) termination with nested loops
//
// Two tasks cooperatively drain a 2D counter: outer counts rows,
// inner counts columns per row. Each row resets the column counter.
// The property af(done(*rows == 0)) proves termination:
// both nested loops eventually complete.
//
// Nested decreases measures:
//   - Outer while: decreases *rows (row count → 0)
//   - Inner while: decreases *cols (column count → 0 per row)
//
// R-G properties verified:
//   1. Each task terminates with *rows == 0
//   2. Nested loops make progress via independent decreases measures
//   3. Pairwise guarantees are compatible

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, rows: &mut u64, cols: &mut u64)
    requires *rows == 3 && *cols == 0,
    ensures af(done(*rows == 0)),
{
    // Task A: drain rows, each row drains columns
    exec.spawn(async
        requires *rows <= 3 && *cols <= 4,
        ensures af(done(*rows == 0)),
    {
        while *rows > 0
            invariant
                *rows <= 3 && *cols <= 4,
            decreases
                *rows,
        {
            *cols = 4;  // each row has 4 columns
            while *cols > 0
                invariant
                    *rows <= 3 && *cols <= 4,
                decreases
                    *cols,
            {
                *cols = *cols - 1;
            }
            // all columns drained for this row
            *rows = *rows - 1;
        }
    });

    // Task B: same cooperative drain
    exec.spawn(async
        requires *rows <= 3 && *cols <= 4,
        ensures af(done(*rows == 0)),
    {
        while *rows > 0
            invariant
                *rows <= 3 && *cols <= 4,
            decreases
                *rows,
        {
            *cols = 4;
            while *cols > 0
                invariant
                    *rows <= 3 && *cols <= 4,
                decreases
                    *cols,
            {
                *cols = *cols - 1;
            }
            *rows = *rows - 1;
        }
    });
}

} // verus!
