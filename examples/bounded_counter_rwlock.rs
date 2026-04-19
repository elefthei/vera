// rust_verify/tests/example.rs ignore --- N1 evaluation of RwLock<V,Pred> for R-G
//
// Goal: determine whether `Arc<RwLock<u64, BoundedByN>>` supports the
// bounded-counter invariant pattern for two parallel async tasks.
//
// Findings (N1):
//
//   1. Yes — `Arc<RwLock<u64, Pred>>` verifies out of the box with the
//      current spawn infrastructure. Each process clones the Arc and
//      calls helper functions that acquire/release.
//
//   2. Because `Pred::inv` is enforced on every `release_write`, the
//      safety invariant `v <= N` is guaranteed by the lock's own type
//      invariant — no rely/guarantee machinery is needed for bounded-
//      counter-style properties. R-G is only needed for properties that
//      `Pred` cannot express (e.g., progress, ordering, history).
//
//   3. LIMITATION: inlining `.acquire_write()` directly inside an
//      `async move { ... }` body triggers an ICE in `vir/src/modes.rs`
//      (`internal error: missing mode` at line 730). The workaround is
//      to wrap the lock operation in a helper `fn` that takes the Arc
//      by reference — modes are correctly inferred there.
//
//   4. `RwLock<V, Pred>` has no natural "current value" view exposed to
//      temporal logic. Temporal R-G formulas over the lock's current
//      state (`ag(lock@ <= N)`) are not directly expressible with this
//      API. For R-G-style temporal reasoning, the existing `&mut T`
//      pattern in `bounded_counter_rg.rs` remains the idiom.
//
// Bottom line: for bounded-safety properties over shared mutable state,
// the recommended Vera pattern is:
//
//   - Wrap shared state in `Arc<RwLock<V, Pred>>`.
//   - Each async task gets a cloned Arc.
//   - Writes go through helper `fn` that acquires, mutates, and releases
//     (inline acquire_write inside `async move` is not yet supported).
//   - Predicate `Pred::inv` enforces the safety invariant at every write.

use vstd::prelude::*;
use vstd::rwlock::*;
use vstd::spawn::*;
use std::sync::Arc;

verus! {

pub const N: u64 = 10;

struct BoundedByN;

impl RwLockPredicate<u64> for BoundedByN {
    open spec fn inv(self, v: u64) -> bool {
        v <= N
    }
}

/// Increment the counter if below N, otherwise leave it unchanged.
/// `Pred::inv` is re-established at `release_write`.
fn bump_up(lock: &Arc<RwLock<u64, BoundedByN>>) {
    let (v, h) = lock.acquire_write();
    if v < N {
        h.release_write(v + 1);
    } else {
        h.release_write(v);
    }
}

/// Decrement the counter if positive, otherwise leave it unchanged.
fn bump_down(lock: &Arc<RwLock<u64, BoundedByN>>) {
    let (v, h) = lock.acquire_write();
    if v > 0 {
        h.release_write(v - 1);
    } else {
        h.release_write(v);
    }
}

fn system(exec: &mut impl Executor) {
    let lock: Arc<RwLock<u64, BoundedByN>> =
        Arc::new(RwLock::new(0u64, Ghost(BoundedByN)));

    let lock_a = lock.clone();
    exec.spawn(async move {
        bump_up(&lock_a);
    });

    let lock_b = lock.clone();
    exec.spawn(async move {
        bump_down(&lock_b);
    });
}

} // verus!

