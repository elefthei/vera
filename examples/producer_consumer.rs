// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Producer-Consumer: asymmetric rely-guarantee
//
// A producer task increments a queue length, a consumer decrements it.
// The tasks have DIFFERENT bodies but compatible R-G contracts.
// The system verifies that the queue length stays bounded.
//
// R-G properties verified:
//   1. Producer body maintains ag(*queue_len <= 10)
//   2. Consumer body maintains ag(*queue_len <= 10)
//   3. Producer's guarantee implies Consumer's rely (and vice versa)
//   4. Conjunction implies system's global ensures

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, queue_len: &mut u64)
    requires *queue_len == 0,
    ensures ag(*queue_len <= 10),
{
    // Producer: enqueue items (increment) up to capacity
    exec.spawn(async
        requires *queue_len <= 10,
        ensures ag(*queue_len <= 10),
    {
        loop
            invariant *queue_len <= 10,
        {
            if *queue_len < 10 { *queue_len = *queue_len + 1; }
        }
    });

    // Consumer: dequeue items (decrement) when available
    exec.spawn(async
        requires *queue_len <= 10,
        ensures ag(*queue_len <= 10),
    {
        loop
            invariant *queue_len <= 10,
        {
            if *queue_len > 0 { *queue_len = *queue_len - 1; }
        }
    });
}

} // verus!
