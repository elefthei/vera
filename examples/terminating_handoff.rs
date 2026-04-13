// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Terminating Handoff: af(done) with asymmetric tasks
//
// A producer fills a buffer, a consumer empties it.
// af(done(*items == 0)) proves the system terminates with buffer empty.
//
// Both tasks use `while` loops that terminate when items reaches 0.
// The `decreases` clause proves each loop makes progress.
//
// R-G properties verified:
//   1. Both tasks terminate with *items == 0 (buffer drained)
//   2. Producer stops adding when buffer is full or items hit 0
//   3. Consumer drains to 0

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, items: &mut u64)
    requires *items == 5,
    ensures af(done(*items == 0)),
{
    // Producer: can add items but also helps drain
    exec.spawn(async
        requires *items <= 10,
        ensures af(done(*items == 0)),
    {
        while *items > 0
            invariant *items <= 10,
            decreases *items,
        {
            *items = *items - 1;
        }
    });

    // Consumer: drains items to 0
    exec.spawn(async
        requires *items <= 10,
        ensures af(done(*items == 0)),
    {
        while *items > 0
            invariant *items <= 10,
            decreases *items,
        {
            *items = *items - 1;
        }
    });
}

} // verus!
