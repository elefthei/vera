#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// ============================================================================
// M1 smoke tests for std::sync::Mutex type specs in vstd::std_specs::sync.
// These validate only:
//   (a) Mutex<T> is recognized as a verified type,
//   (b) Mutex::<T>::new ensures m@ == t,
//   (c) View for Mutex<T> and MutexGuard<'_, T> compiles.
// Full lock()/Deref/DerefMut specs are deferred to M2 per plan.md.
// ============================================================================

test_verify_one_file! {
    #[test] mutex_new_view_roundtrip verus_code! {
        use std::sync::Mutex;
        use vstd::prelude::*;

        fn mk(x: u64) {
            let m = Mutex::new(x);
            assert(m@ == x);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mutex_new_view_mismatch_fails verus_code! {
        use std::sync::Mutex;
        use vstd::prelude::*;

        fn mk(x: u64) {
            let m = Mutex::new(x);
            assert(m@ == (x + 1) as u64); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// ----------------------------------------------------------------------------
// VMutex wrapper tests (vstd::sync::VMutex).
// ----------------------------------------------------------------------------

test_verify_one_file! {
    #[test] vmutex_lock_get_set_commit verus_code! {
        use vstd::sync::VMutex;
        use vstd::prelude::*;

        fn use_it() {
            let m = VMutex::new(5u64);
            assert(m@ == 5);
            let mut g = m.lock();
            assert(g@ == 5);
            g.set(7);
            assert(g@ == 7);
            m.commit(g);
            assert(m@ == 7);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] vmutex_commit_preserves_invariant verus_code! {
        use vstd::sync::VMutex;
        use vstd::prelude::*;

        fn bump(m: &VMutex<u64>)
            requires m@ < 100,
            ensures m@ <= 100,
        {
            let mut g = m.lock();
            let v = *g.get();
            if v < 100 {
                g.set(v + 1);
            }
            m.commit(g);
        }
    } => Ok(())
}

// NOTE: a "negative" test that asserts verification fails after a bogus
// `set`+`commit` is intentionally omitted at this stage. The soundness of
// `commit(&self, …)` mutating `self@` through a shared reference requires
// either (a) a ghost-permission-token model (see `vstd::cell::PCell`) or
// (b) integration with the R-G havoc pass (M3). Until then, negatives will
// live in the R-G test file where interference havoc makes the view's
// mutability explicit to the verifier.
