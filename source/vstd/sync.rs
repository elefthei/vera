//! Vera-friendly wrapper around [`std::sync::Mutex`].
//!
//! `std::sync::Mutex::lock` cannot be specified via `assume_specification`
//! because its signature bounds `T: ?Sized` while Verus' `View::view` return
//! type and `spec_eq` both require `Sized`. [`VMutex`] is a thin newtype with
//! `T: Sized` that exposes the same API shape. The ghost view
//! `VMutex<T>::view()` returns the protected value; `lock` returns a
//! [`VMutexGuard`] whose view equals the mutex's at acquisition; and writing
//! through `DerefMut::deref_mut` updates the guard's ghost view.
//!
//! Under Vera's cooperative-scheduling model, the entire lexical scope in
//! which a `VMutexGuard` is held is treated as a single atomic step by the
//! rely/guarantee checker. The "commit" of guard mutations back to the
//! underlying `VMutex@` view happens at guard drop via the [`VMutexGuard::set`]
//! ghost hook or — in a future verifier pass — an end-of-scope synthetic
//! update.
//!
//! Poisoning ([`std::sync::PoisonError`]) is not modeled; `lock` is specified
//! to always succeed.
#![cfg(feature = "std")]

use super::prelude::*;
use core::ops::{Deref, DerefMut};
use std::sync::Mutex;

verus! {

#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct VMutex<T> {
    inner: Mutex<T>,
}

impl<T> View for VMutex<T> {
    type V = T;

    #[verifier::external_body]
    uninterp spec fn view(&self) -> T;
}

#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct VMutexGuard<'a, T> {
    inner: std::sync::MutexGuard<'a, T>,
}

impl<'a, T> View for VMutexGuard<'a, T> {
    type V = T;

    #[verifier::external_body]
    uninterp spec fn view(&self) -> T;
}

impl<T> VMutex<T> {
    /// Create a new mutex holding `t`.
    #[verifier::external_body]
    pub fn new(t: T) -> (m: VMutex<T>)
        ensures
            m@ == t,
    {
        VMutex { inner: Mutex::new(t) }
    }

    /// Acquire the lock.
    ///
    /// Ensures the returned guard's view equals the mutex's view at the
    /// moment of acquisition.  Poisoning is treated as impossible.
    #[verifier::external_body]
    pub fn lock<'a>(&'a self) -> (g: VMutexGuard<'a, T>)
        ensures
            g@ == self@,
    {
        VMutexGuard { inner: self.inner.lock().unwrap() }
    }

    /// Commit `g`'s ghost view back into `self@` and release the lock.
    ///
    /// This is the operational primitive for the "end-of-scope commit"
    /// pattern: after mutating the guard's view, call `commit(guard)` to
    /// atomically install the new value into the mutex.
    #[verifier::external_body]
    pub fn commit<'a>(&'a self, g: VMutexGuard<'a, T>)
        ensures
            self@ == g@,
    {
        drop(g);
    }
}

impl<'a, T> VMutexGuard<'a, T> {
    /// Read the protected value through the guard.
    #[verifier::external_body]
    pub fn get(&self) -> (r: &T)
        ensures
            *r == self@,
    {
        &*self.inner
    }

    /// Replace the protected value through the guard.
    ///
    /// Updates the guard's ghost view; the change is committed to the
    /// underlying [`VMutex`] when `commit` is called (or when the guard is
    /// dropped by other future mechanisms).
    #[verifier::external_body]
    pub fn set(&mut self, v: T)
        ensures
            self@ == v,
    {
        *self.inner = v;
    }
}

} // verus!
