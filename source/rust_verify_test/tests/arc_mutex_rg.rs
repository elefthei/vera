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
