#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// ============================================================================
// Bounded Counter R-G Tests
// ============================================================================
// Tests for the load-bearing rely-guarantee pattern in
// examples/bounded_counter_rg.rs.
//
// Two async processes share a counter via &mut u64 (semantically equivalent
// to Arc<Mutex<u64>> under cooperative scheduling). Each process verifies
// independently using its own pre+rely; the system invariant
// `ag(*count <= N)` arises from the conjunction of both guarantees.
// ============================================================================

// Positive: symmetric R-G — both processes guarantee `ag(*count <= 10)`,
// each rely is satisfied by the other's guarantee, conjunction implies the
// system's `ag(*count <= 10)`.
test_verify_one_file! {
    #[test] test_bounded_counter_rg_symmetric_pass verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        fn system(exec: &mut impl Executor, count: &mut u64)
            requires *count == 0,
            ensures ag(*count <= 10),
        {
            exec.spawn(async
                requires *count <= 10,
                ensures ag(*count <= 10),
            {
                loop invariant *count <= 10, {
                    if *count < 10 { *count = *count + 1; }
                }
            });

            exec.spawn(async
                requires *count <= 10,
                ensures ag(*count <= 10),
            {
                loop invariant *count <= 10, {
                    if *count > 0 { *count = *count - 1; }
                }
            });
        }
    } => Ok(())
}

// Negative: mismatched bounds — A guarantees `*count <= 200` but B requires
// `*count <= 50`. Pairwise R-G check should fail because A's guarantee does
// not imply B's rely.
test_verify_one_file! {
    #[test] test_bounded_counter_rg_mismatched_rely_fail verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        fn system(exec: &mut impl Executor, count: &mut u64)
            requires *count == 0,
            ensures ag(*count <= 50),
        {
            exec.spawn(async
                requires *count <= 200,
                ensures ag(*count <= 200),
            {
                loop invariant *count <= 200, {
                    if *count < 200 { *count = *count + 1; }
                }
            });

            exec.spawn(async
                requires *count <= 50,
                ensures ag(*count <= 50),
            {
                loop invariant *count <= 50, {
                    if *count > 0 { *count = *count - 1; }
                }
            });
        }
    } => Err(_e) => ()
}

// Negative: A's body removes the upper-bound guard (`if *count < 10`) so it
// can blow past N. A's `ensures ag(*count <= 10)` should fail to verify
// because the body breaks the invariant on overflow.
test_verify_one_file! {
    #[test] test_bounded_counter_rg_unguarded_increment_fail verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        fn system(exec: &mut impl Executor, count: &mut u64)
            requires *count == 0,
            ensures ag(*count <= 10),
        {
            exec.spawn(async
                requires *count <= 10,
                ensures ag(*count <= 10),
            {
                loop invariant *count <= 10, {
                    *count = *count + 1;  // unguarded — breaks inv at *count == 10
                }
            });

            exec.spawn(async
                requires *count <= 10,
                ensures ag(*count <= 10),
            {
                loop invariant *count <= 10, {
                    if *count > 0 { *count = *count - 1; }
                }
            });
        }
    } => Err(_e) => ()
}
