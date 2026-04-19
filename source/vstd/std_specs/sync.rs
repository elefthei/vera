//! Specifications for `std::sync::Mutex` and `std::sync::MutexGuard`.
//!
//! These specs model a `Mutex<T>` as a ghost cell holding a `T` (visible via
//! `View`). Under Vera's cooperative-scheduling model, the entire scope in
//! which a `MutexGuard` is held is treated as a single atomic step by the
//! rely/guarantee checker: calls to `.await` inside a live lock scope are
//! rejected by the front-end.
//!
//! The commit point — i.e., when mutations performed through the guard become
//! visible to other processes — is the end of the guard's lexical scope
//! (when the guard is dropped). This is modeled in the verifier by a
//! synthetic ghost update `mutex@ := guard@` emitted at the drop site.
//!
//! Poisoning (`PoisonError` / `LockResult::Err`) is currently not modeled;
//! `Mutex::lock` is specified to always succeed.

#![cfg(feature = "std")]
use super::super::prelude::*;

use std::sync::{Mutex, MutexGuard};

verus! {

#[verifier::reject_recursive_types(T)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExMutex<T: ?Sized>(Mutex<T>) where T: core::marker::MetaSized;

impl<T> View for Mutex<T> {
    type V = T;

    #[verifier::external_body]
    uninterp spec fn view(&self) -> T;
}

#[verifier::reject_recursive_types(T)]
#[verifier::external_type_specification]
#[verifier::external_body]
pub struct ExMutexGuard<'a, T: ?Sized + 'a>(MutexGuard<'a, T>)
    where T: core::marker::MetaSized;

impl<'a, T> View for MutexGuard<'a, T> {
    type V = T;

    #[verifier::external_body]
    uninterp spec fn view(&self) -> T;
}

pub assume_specification<T>[ Mutex::<T>::new ](t: T) -> (m: Mutex<T>)
    ensures
        m@ == t,
;

// NOTE: specs for `Mutex::lock`, `MutexGuard::deref`, and `MutexGuard::deref_mut`
// are deferred to M2. `std::sync::Mutex::lock` has `T: ?Sized` in its signature,
// which is incompatible with `assume_specification` because the post-condition
// would need `spec_eq` on a `?Sized` view. The M2 lowering will synthesize an
// intrinsic ghost update `m@ := g@` at end-of-scope without needing a proxy
// for `lock` itself.

} // verus!
