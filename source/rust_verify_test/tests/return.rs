#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        fn test_ret(b: bool) -> (i: u64)
            ensures
                af(done(10 <= i)),
                af(done(20 <= i)),
        {
            if b {
                return 20;
            }
            30
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 verus_code! {
        fn test_ret(b: bool) -> (i: u64)
            ensures
                af(done(10 <= i)),
                af(done(20 <= i)),
        {
            if b {
                return 10; // FAILS
            }
            30
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1_fails2 verus_code! {
        fn test_ret(b: bool) -> (i: u64)
            ensures
                af(done(10 <= i)),
                af(done(20 <= i)), // FAILS
        {
            if b {
                return 20;
            }
            10
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        fn test_ret(b: bool)
            ensures af(done(true))
        {
            if b {
                return;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2_fails verus_code! {
        fn test_ret(b: bool)
            requires b
            ensures af(done(false))
        {
            if b {
                return; // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file_with_options! {
    #[test] test3 ["exec_allows_no_decreases_clause"] => verus_code! {
        fn test_ret(b: bool)
            requires b
            ensures af(done(b))
        {
            while b || !b
                invariant b
            {
                return;
            }
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] test3_fails ["exec_allows_no_decreases_clause"] => verus_code! {
        fn test_ret(b: bool)
            requires b
            ensures af(done(b))
        {
            while b || !b {
                return; // FAILS
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] regression_215 verus_code! {
        fn f() {
            return ();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] returning_named_unit_issue1108 verus_code! {
        proof fn f() -> (n: ())
            ensures af(done(n === ()))
        {
            return ();
        }

        proof fn g() -> (n: ())
            ensures af(done(n === ()))
        {
            return;
        }

        proof fn f2() -> (n: ())
            ensures af(done(n === ()))
        {
            return ();
        }

        proof fn g2() -> (n: ())
            ensures af(done(n === ()))
        {
            return;
        }

        proof fn tests() {
            f();
            g();
            f2();
            g2();
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] return_unit_trait_issue1278 verus_code! {
        pub trait Trait<T> {
            spec fn ok(r: T) -> bool;
            proof fn apply() -> (result: T) ensures af(done(Self::ok(result)));
        }

        pub struct S {
        }

        impl Trait<()> for S {
            open spec fn ok(r: ()) -> bool { true }
            proof fn apply() -> (result: ()) {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_clone_unit_issue1108 verus_code! {
        use vstd::*;
        use vstd::prelude::*;

        pub trait PolyfillClone: View + Sized {
            fn clone(&self) -> (res: Self)
                ensures
                    af(done(res@ == self@));
        }

        impl PolyfillClone for () {
            fn clone(&self) -> Self {
                ()
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trait_impl_return_unit_issue1108 verus_code! {
        trait Tr : Sized {
            fn get() -> (r: Self)
                ensures af(done(r == r));}

        impl Tr for () {
            fn get() -> (r: Self)
            {
            }
        }

        fn main() { }
    } => Ok(())
}

test_verify_one_file! {
    #[test] generic_spec_funs_returning_unit_issue1108 verus_code! {
        trait T {
            spec fn f();
        }

        spec fn g<A: T>() {
            A::f()
        }

        struct X { }

        impl T for X {
            spec fn f() { () }
        }

        proof fn test_generic<S: T>() {
            let x = S::f();
            assert(x == ());
        }

        proof fn test_x() {
            let x = <X as T>::f();
            assert(x == ());
        }

        proof fn test_generic2<S: T>() {
            let x = g::<S>();
            assert(x == ());
        }

        proof fn test_x2() {
            let x = g::<X>();
            assert(x == ());
        }
    } => Ok(())
}
