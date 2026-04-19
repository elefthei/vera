#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// ============================================================================
// N5 — R-G tests for Arc<RwLock<V, Pred>> as shared-invariant primitive.
//
// These validate that the "bounded counter over shared lock" pattern works:
//   - Two async tasks clone an Arc<RwLock<u64, BoundedByN>>
//   - Each calls a helper fn that acquires the lock, mutates, and releases
//   - Pred::inv (v <= N) is enforced by release_write
//
// Positive: symmetric bump_up/bump_down preserves v <= N.
// Negatives:
//   (a) release_write with a value exceeding N fails.
//   (b) a helper that doesn't re-establish inv on release fails.
// ============================================================================

test_verify_one_file! {
    #[test] arc_rwlock_bounded_counter_positive verus_code! {
        use vstd::prelude::*;
        use vstd::rwlock::*;
        use vstd::spawn::*;
        use std::sync::Arc;

        pub const N: u64 = 10;

        struct BoundedByN;

        impl RwLockPredicate<u64> for BoundedByN {
            open spec fn inv(self, v: u64) -> bool {
                v <= N
            }
        }

        fn bump_up(lock: &Arc<RwLock<u64, BoundedByN>>) {
            let (v, h) = lock.acquire_write();
            if v < N {
                h.release_write(v + 1);
            } else {
                h.release_write(v);
            }
        }

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
    } => Ok(())
}

test_verify_one_file! {
    #[test] arc_rwlock_release_exceeds_bound_fails verus_code! {
        use vstd::prelude::*;
        use vstd::rwlock::*;
        use std::sync::Arc;

        pub const N: u64 = 10;

        struct BoundedByN;

        impl RwLockPredicate<u64> for BoundedByN {
            open spec fn inv(self, v: u64) -> bool {
                v <= N
            }
        }

        // release with N+1 cannot re-establish inv(v) = v <= N.
        fn bad(lock: &Arc<RwLock<u64, BoundedByN>>) {
            let (v, h) = lock.acquire_write();
            h.release_write(N + 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] arc_rwlock_unbounded_increment_fails verus_code! {
        use vstd::prelude::*;
        use vstd::rwlock::*;
        use std::sync::Arc;

        pub const N: u64 = 10;

        struct BoundedByN;

        impl RwLockPredicate<u64> for BoundedByN {
            open spec fn inv(self, v: u64) -> bool {
                v <= N
            }
        }

        // unconditional v+1 is not guaranteed to preserve v <= N
        // when v == N (it becomes N+1, violating inv).
        fn bump_unchecked(lock: &Arc<RwLock<u64, BoundedByN>>) {
            let (v, h) = lock.acquire_write();
            h.release_write(v + 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
