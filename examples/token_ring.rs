// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Token Ring: mutual exclusion via token passing
//
// Two tasks share a token variable (*token ∈ {0, 1}).
// Task A works when *token == 0, then passes to B by setting *token = 1.
// Task B works when *token == 1, then passes to A by setting *token = 0.
// Only the token holder modifies shared data — mutual exclusion by construction.
//
// R-G properties verified:
//   1. Both tasks maintain ag(*token == 0 || *token == 1)
//   2. Each task only modifies data when holding the token
//   3. Token invariant is preserved across all transitions

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, token: &mut u64, data: &mut u64)
    requires *token == 0 && *data == 0,
    ensures ag(*token == 0 || *token == 1),
{
    // Task A: work when holding token (token == 0), then pass to B
    exec.spawn(async
        requires *token == 0 || *token == 1,
        ensures ag(*token == 0 || *token == 1),
    {
        loop
            invariant *token == 0 || *token == 1,
        {
            if *token == 0 {
                // A holds the token — safe to modify data
                if *data < 1000 { *data = *data + 1; }
                // Pass token to B
                *token = 1;
            }
        }
    });

    // Task B: work when holding token (token == 1), then pass to A
    exec.spawn(async
        requires *token == 0 || *token == 1,
        ensures ag(*token == 0 || *token == 1),
    {
        loop
            invariant *token == 0 || *token == 1,
        {
            if *token == 1 {
                // B holds the token — safe to modify data
                if *data < 1000 { *data = *data + 1; }
                // Pass token to A
                *token = 0;
            }
        }
    });
}

} // verus!
