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

// ============================================================================
// Multi-process Rely-Guarantee Tests
// ============================================================================

// Multi-process: two async tasks with compatible rely-guarantee.
// Note: async fns have no requires (rely = true) so the second spawn's
// precondition is trivially met after the first spawn hasvocs x.
// The R-G check (guarantee_i → rely_j) should pass since rely is true.
test_verify_one_file! {
    #[test] test_multiprocess_rg_compatible verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        async fn task_a(x: &mut u64) -> (ret: ())
            ensures ag(*x <= 100),
        {
            *x = 0;
            loop invariant *x <= 100, {
                if *x < 100 { *x = *x + 1; }
                else { *x = 0; }
            }
        }

        async fn task_b(x: &mut u64) -> (ret: ())
            ensures ag(*x <= 100),
        {
            *x = 0;
            loop invariant *x <= 100, {
                if *x > 0 { *x = *x - 1; }
            }
        }

        fn system(exec: &mut impl Executor, x: &mut u64) {
            exec.spawn(task_a(x));
            exec.spawn(task_b(x));
        }
    } => Ok(())
}

// Multi-process: incompatible rely-guarantee — should FAIL
test_verify_one_file! {
    #[test] test_multiprocess_rg_incompatible verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        async fn task_wide(x: &mut u64) -> (ret: ())
            requires *x <= 200,
            ensures ag(*x <= 200),
        {
            loop invariant *x <= 200, {
                if *x < 200 { *x = *x + 1; }
                else { *x = 0; }
            }
        }

        async fn task_narrow(x: &mut u64) -> (ret: ())
            requires *x <= 50,
            ensures ag(*x <= 50),
        {
            loop invariant *x <= 50, {
                if *x > 0 { *x = *x - 1; }
            }
        }

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x == 0,
        {
            exec.spawn(task_wide(x));
            exec.spawn(task_narrow(x));
        }
    } => Err(_err) => ()
}

// System-level ensures: conjunction of guarantees implies global property
test_verify_one_file! {
    #[test] test_multiprocess_system_ensures_pass verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        async fn task_upper(x: &mut u64) -> (ret: ())
            ensures ag(*x <= 100),
        {
            *x = 0; // ensure invariant holds at entry
            loop invariant *x <= 100, {
                if *x < 100 { *x = *x + 1; }
                else { *x = 0; }
            }
        }

        async fn task_lower(x: &mut u64) -> (ret: ())
            ensures ag(*x <= 100),
        {
            *x = 0;
            loop invariant *x <= 100, {
                if *x > 0 { *x = *x - 1; }
            }
        }

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x == 50,
            ensures ag(*x <= 200),
        {
            exec.spawn(task_upper(x));
            exec.spawn(task_lower(x));
            // G_upper = (*x <= 100), G_lower = (*x <= 100)
            // Conjunction: (*x <= 100) ∧ (*x <= 100) → (*x <= 200) ✓
        }
    } => Ok(())
}

// System-level ensures FAIL: conjunction doesn't imply global
test_verify_one_file! {
    #[test] test_multiprocess_system_ensures_fail verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        async fn task_a(x: &mut u64) -> (ret: ())
            requires *x <= 100,
            ensures ag(*x <= 100),
        {
            loop invariant *x <= 100, {
                if *x < 100 { *x = *x + 1; }
                else { *x = 0; }
            }
        }

        async fn task_b(x: &mut u64) -> (ret: ())
            requires *x <= 100,
            ensures ag(*x <= 100),
        {
            loop invariant *x <= 100, {
                if *x > 0 { *x = *x - 1; }
            }
        }

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x == 50,
            ensures ag(*x <= 5),
        {
            exec.spawn(task_a(x));
            exec.spawn(task_b(x));
            // G_a = (*x <= 100), G_b = (*x <= 100)
            // Conjunction: (*x <= 100) → (*x <= 5) ✗ FAILS
        }
    } => Err(_err) => ()
}

// ============================================================================
// Rely-guarantee negative tests (expected failures)
// ============================================================================

// Pairwise R-G fail: task_wide guarantees x<=200, task_strict relies on x<=50
test_verify_one_file! {
    #[test] test_multiprocess_rg_pairwise_fail verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        async fn task_wide(x: &mut u64) -> (ret: ())
            ensures ag(*x <= 200),
        {
            *x = 0;
            loop invariant *x <= 200, {
                if *x < 200 { *x = *x + 1; }
                else { *x = 0; }
            }
        }

        async fn task_strict(x: &mut u64) -> (ret: ())
            requires *x <= 50,
            ensures ag(*x <= 50),
        {
            *x = 0;
            loop invariant *x <= 50, {
                if *x < 50 { *x = *x + 1; }
                else { *x = 0; }
            }
        }

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x == 0,
            ensures ag(*x <= 200),
        {
            exec.spawn(task_wide(x));
            exec.spawn(task_strict(x));
            // G_wide (x<=200) does NOT imply R_strict (x<=50) → FAIL
        }
    } => Err(_err) => ()
}

// Conjunction fail: guarantees too weak for global property
test_verify_one_file! {
    #[test] test_multiprocess_conjunction_too_weak verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        async fn task_a(x: &mut u64) -> (ret: ())
            ensures ag(*x <= 1000),
        {
            *x = 0;
            loop invariant *x <= 1000, {
                if *x < 1000 { *x = *x + 1; }
                else { *x = 0; }
            }
        }

        async fn task_b(x: &mut u64) -> (ret: ())
            ensures ag(*x <= 1000),
        {
            *x = 0;
            loop invariant *x <= 1000, {
                if *x > 0 { *x = *x - 1; }
            }
        }

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x == 0,
            ensures ag(*x <= 5),
        {
            exec.spawn(task_a(x));
            exec.spawn(task_b(x));
            // (x<=1000) ∧ (x<=1000) does NOT imply (x<=5) → FAIL
        }
    } => Err(_err) => ()
}

// Single spawn: guarantee doesn't imply global
test_verify_one_file! {
    #[test] test_multiprocess_single_spawn_fail verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        async fn task(x: &mut u64) -> (ret: ())
            ensures ag(*x <= 100),
        {
            *x = 0;
            loop invariant *x <= 100, {
                if *x < 100 { *x = *x + 1; }
                else { *x = 0; }
            }
        }

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x == 0,
            ensures ag(*x <= 5),
        {
            exec.spawn(task(x));
            // G = (x<=100) does NOT imply (x<=5) → FAIL
        }
    } => Err(_err) => ()
}

// No temporal ensures on tasks → system AG not discharged
test_verify_one_file! {
    #[test] test_multiprocess_no_temporal_guarantees_fail verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        async fn task_plain(x: &mut u64) -> (ret: ())
            ensures af(done(true)),
        {
        }

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x == 0,
            ensures ag(*x <= 100),
        {
            exec.spawn(task_plain(x));
            // task_plain has AF (not AG) → can't discharge system's AG
        }
    } => Err(_err) => ()
}

// === Async Block Syntax Tests ===

test_verify_one_file! {
    #[test] test_async_block_requires_ensures_parse verus_code! {
        use vstd::prelude::*;
        fn test() {
            let _f = async
                requires true,
                ensures true,
            {
            };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_async_block_spawn_rg_pass verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x <= 100,
            ensures ag(*x <= 100),
        {
            exec.spawn(async
                requires *x <= 100,
                ensures ag(*x <= 100),
            {
                loop
                    invariant *x <= 100,
                {
                }
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_async_block_rg_mismatch_fail verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x <= 100,
            ensures ag(*x <= 100),
        {
            exec.spawn(async
                requires *x <= 50,
                ensures ag(*x <= 50),
            {
                loop
                    invariant *x <= 50,
                {
                }
            });
        }
    } => Err(_err) => ()
}

test_verify_one_file! {
    #[test] test_async_block_mixed_spawn verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        async fn named_task(x: &mut u64) -> (ret: ())
            requires *x <= 100,
            ensures ag(*x <= 100),
        {
            loop
                invariant *x <= 100,
            {
            }
        }

        // Test that named fn spawn + async block spawn can coexist
        fn system_named(exec: &mut impl Executor, x: &mut u64)
            requires *x <= 100,
            ensures ag(*x <= 100),
        {
            exec.spawn(named_task(x));
        }

        fn system_inline(exec: &mut impl Executor, x: &mut u64)
            requires *x <= 100,
            ensures ag(*x <= 100),
        {
            exec.spawn(async
                requires *x <= 100,
                ensures ag(*x <= 100),
            {
                loop
                    invariant *x <= 100,
                {
                }
            });
        }
    } => Ok(())
}

// === Gap Regression Tests ===

// Gap 1 regression: async block requires must be used in R-G pairwise checks.
test_verify_one_file! {
    #[test] test_gap1_async_block_relies_in_rg verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x <= 100,
            ensures ag(*x <= 100),
        {
            exec.spawn(async
                requires *x <= 100,
                ensures ag(*x <= 100),
            {
                loop
                    invariant *x <= 100,
                {
                }
            });
        }
    } => Ok(())
}

// Gap 2 regression: async block body must be verified against ensures.
// The body is empty but ensures requires false → should fail.
test_verify_one_file! {
    #[test] test_gap2_async_block_body_violates_ensures verus_code! {
        use vstd::prelude::*;

        fn test() {
            let _f = async
                requires true,
                ensures false,
            {
            };
        }
    } => Err(err) => assert_vir_error_msg(err, "async block ensures not satisfied")
}

// S1 soundness: known limitation — async block body runs inline in enclosing scope.
// With cooperative scheduling, the body's side effects (including infinite loops)
// affect the enclosing function. This is documented as a design limitation.
// Proper isolation requires ownership-based scope separation (future work).

// S2 soundness: AG system with only AF spawned tasks should NOT discharge AG.
test_verify_one_file! {
    #[test] test_soundness_ag_not_discharged_by_af_only verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x == 10,
            ensures ag(*x <= 100),  // AG obligation on system
        {
            // Only AF tasks — can't discharge AG
            exec.spawn(async
                requires *x <= 100,
                ensures af(done(*x == 0)),  // AF, not AG
            {
                while *x > 0
                    invariant *x <= 100,
                    decreases *x,
                {
                    *x = *x - 1;
                }
            });
        }
    } => Err(_err) => ()
}

// Regression: async-move block with a `let` stmt referenced from a nested
// branched block used to ICE in modes.rs ("missing mode") because the outer
// HIR block's `stmts` were silently dropped.
test_verify_one_file! {
    #[test] test_async_move_let_in_nested_if_regression verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        fn system(exec: &mut impl Executor) {
            exec.spawn(async move {
                let h: u64 = 5;
                if true {
                    let _ = h;
                }
            });
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_async_move_let_in_nested_match_regression verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        fn system(exec: &mut impl Executor) {
            exec.spawn(async move {
                let h: u64 = 5;
                match h {
                    0 => {}
                    _ => { let _ = h; }
                }
            });
        }
    } => Ok(())
}
