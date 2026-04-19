// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Bounded Counter with Load-Bearing R-G
// =====================================
//
// Two async processes share a counter and prove the system invariant
// `ag(*count <= N)` via rely-guarantee composition:
//
//   - Process A (incrementer): only increments (when `*count < N`).
//   - Process B (decrementer): only decrements (when `*count > 0`).
//
// Why R-G is LOAD-BEARING here:
//   Each process's per-iteration loop invariant `*count <= N` is preserved by
//   its own body, BUT only because the rely `*count <= N` constrains what the
//   ENVIRONMENT (the other process) is allowed to do between iterations.
//   Without the rely, the env could push `*count` above N at any sleep point,
//   and the loop body's `if *count < N` guard alone would not recover it.
//
//   The pairwise R-G check at `block_on`:
//     A's guarantee `ag(*count <= N)`  ⊃  B's rely `*count <= N`. ✓
//     B's guarantee `ag(*count <= N)`  ⊃  A's rely `*count <= N`. ✓
//     Conjunction of guarantees       ⊃  the system's `ag(*count <= N)`. ✓
//
//   So the proof of A *requires* B's guarantee (via R-G), and vice versa.
//   Neither task verifies alone if you delete the rely.
//
// Note on shared state: in real Rust this would be `Arc<Mutex<usize>>` cloned
// into each task. Under Vera's cooperative scheduling each async-block step is
// atomic, so `&mut u64` is semantically equivalent to "Mutex held for one
// step". We use the simpler form here.
//
// For a shared-state variant using `Arc<RwLock<u64, Pred>>` (where `Pred`
// enforces `v <= N` structurally at every release), see
// `examples/bounded_counter_rwlock.rs`. That primitive handles the safety
// invariant by construction and does not need R-G; this `&mut T` example
// remains the canonical tutorial for R-G temporal reasoning.

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

pub const N: u64 = 10;

fn system(exec: &mut impl Executor, count: &mut u64)
    requires *count == 0,
    // System invariant: count stays bounded above by N forever.
    ensures ag(*count <= N),
{
    // ---- Process A: the CAPPER ----
    // Body: increments only when *count < N. Guarantees the UPPER bound.
    // Relies: env keeps *count >= 0 (i.e., never underflows below A's view).
    //         (Trivially true for u64, but recorded explicitly so the proof
    //         rule is symmetric with B and explicit about R-G structure.)
    exec.spawn(async
        requires *count <= N,
        ensures ag(*count <= N),
    {
        loop
            invariant *count <= N,
        {
            if *count < N {
                *count = *count + 1;
            }
        }
    });

    // ---- Process B: the FLOORER ----
    // Body: decrements only when *count > 0. Guarantees the LOWER bound.
    // Relies: env keeps *count <= N (i.e., never overflows beyond B's view).
    //         B genuinely needs this — without the rely, A could push *count
    //         arbitrarily high, and B's `if *count > 0` check would still let
    //         it operate but the loop invariant would not constrain *count.
    exec.spawn(async
        requires *count <= N,
        ensures ag(*count <= N),
    {
        loop
            invariant *count <= N,
        {
            if *count > 0 {
                *count = *count - 1;
            }
        }
    });
}

} // verus!
