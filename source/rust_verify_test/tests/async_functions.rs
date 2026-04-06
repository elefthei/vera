#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_basic_async_function_ensures_pass verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                af(done(ret == 1)),
        {
            1
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_basic_async_function_ensures_fail verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                af(done(ret == 2)),  // FAILS
        {
            1
        }
    } => Err(_e) => ()
}

test_verify_one_file! {
    #[test] test_basic_async_function_and_await verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                af(done(ret == 1)),
        {
            1
        }
        async fn bar() {
            let future = foo();
            let ret = future.await;
            assert(ret == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_basic_async_function_util verus_code! {
        use vstd::prelude::*;
        use vstd::future::*;
        async fn foo() -> (ret: usize)
            ensures
                af(done(ret == 1)),
        {
            1
        }
        async fn bar() {
            let future = foo();
            assert(future.awaited() ==> future@ == 1);
            let ret = future.await;
            assert(ret == 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_basic_async_function_lifetime_fail verus_code! {
        use vstd::prelude::*;
        async fn foo(x :&usize) -> (ret: usize)
            ensures
                af(done(ret == 1)),
        {
            1
        }
        async fn bar() {
            let mut x = 233;
            let future = foo(&x);
            x = 2333;
            let ret = future.await;
            x = 2333;
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot assign to `x` because it is borrowed")
}

test_verify_one_file! {
    #[test] test_basic_async_function_nested_pass verus_code! {
        use vstd::prelude::*;
        use core::future::*;
        use vstd::future::*;
        async fn foo() -> (ret: usize)
            ensures
                af(done(ret == 233)),
        {
            233
        }

        async fn foo_of_foo() -> (ret: impl Future<Output = usize>)
            ensures
                af(done(ret.awaited() ==> ret@ == 233)),
        {
            foo()
        }
        async fn bar() {
            let future_of_future = foo_of_foo();
            let ret = future_of_future.await.await;
            assert(ret == 233);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_await_outside_of_async_function_fail verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                af(done(ret == 233)),
        {
            233
        }

        fn bar() {
            let future = foo();
            future.await;
        }
    } => Err(err) => assert_rust_error_msg(err, "`await` is only allowed inside `async` functions and blocks")
}

test_verify_one_file! {
    #[test] test_async_function_external_specification verus_code! {
        use vstd::prelude::*;
        #[verifier(external)]
        async fn negate_bool(b: bool, x: u8) -> bool {
            !b
        }

        #[verifier(external_fn_specification)]
        async fn negate_bool_requires_ensures(b: bool, x: u8) -> (ret_b: bool)
            requires x != 0,
            ensures af(done(ret_b == !b))
        {
            negate_bool(b, x).await
        }

        async fn foo(){
            let future = negate_bool(true, 1);
            let ret = future.await;
            assert(ret == false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_async_function_mut_ref_ok verus_code! {
        use vstd::prelude::*;
        pub async fn bar(x: &mut usize) -> (ret: ())
            ensures
                af(done(*x == 2333)),
        {
            *x = 2333;
        }

        async fn foo(){
            let mut x = 233;
            let future = bar(&mut x);
            future.await;
            assert(x == 2333);
        }
    } => Ok(())
}

// ============================================================================
// Soundness Mutation Tests for Async/Await
// Each test is a mutation of a passing test that MUST be rejected.
// ============================================================================

// Mutation: wrong return value vs ensures
test_verify_one_file! {
    #[test] test_mutation_async_wrong_return verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                af(done(ret == 2)),  // BUG: body returns 1, not 2
        {
            1
        }
    } => Err(_e) => ()
}

// Mutation: wrong ensures breaks caller assertion after await
test_verify_one_file! {
    #[test] test_mutation_async_caller_breaks verus_code! {
        use vstd::prelude::*;
        async fn foo() -> (ret: usize)
            ensures
                af(done(ret == 1)),
        {
            1
        }
        async fn bar() {
            let future = foo();
            let ret = future.await;
            assert(ret == 2);  // BUG: ret is 1, not 2
        }
    } => Err(_e) => ()
}

// Mutation: mut ref ensures doesn't match body
test_verify_one_file! {
    #[test] test_mutation_async_mut_ref_wrong verus_code! {
        use vstd::prelude::*;
        pub async fn bar(x: &mut usize) -> (ret: ())
            ensures
                af(done(*x == 0)),  // BUG: body sets *x = 2333, not 0
        {
            *x = 2333;
        }
    } => Err(_e) => ()
}

// Mutation: nested future inner ensures wrong
test_verify_one_file! {
    #[test] test_mutation_async_nested_wrong verus_code! {
        use vstd::prelude::*;
        use core::future::*;
        use vstd::future::*;
        async fn foo() -> (ret: usize)
            ensures
                af(done(ret == 100)),  // BUG: body returns 233, not 100
        {
            233
        }

        async fn bar() {
            let ret = foo().await;
            assert(ret == 100);  // Will fail: ret is actually 233
        }
    } => Err(_e) => ()
}

// Mutation: temporal view property contradicted
test_verify_one_file! {
    #[test] test_mutation_async_view_wrong verus_code! {
        use vstd::prelude::*;
        use vstd::future::*;
        async fn foo() -> (ret: usize)
            ensures
                af(done(ret == 1)),
        {
            1
        }
        async fn bar() {
            let future = foo();
            assert(future.awaited() ==> future@ == 999);  // BUG: view is 1, not 999
            let ret = future.await;
        }
    } => Err(_e) => ()
}

// Mutation: async function requires not met by caller
test_verify_one_file! {
    #[test] test_mutation_async_requires_violated verus_code! {
        use vstd::prelude::*;
        async fn needs_positive(x: usize) -> (ret: usize)
            requires x > 0,
            ensures af(done(ret == x)),
        {
            x
        }
        async fn bar() {
            let future = needs_positive(0);  // BUG: violates requires x > 0
            let ret = future.await;
        }
    } => Err(_e) => ()
}
