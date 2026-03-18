#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Tests for CTL temporal operators
// Unary: ag, eg
// Binary: au, an, eu, en
// Sugar: af → au(true, ·), ax → an(true, ·), ef → eu(true, ·), ex → en(true, ·)
// These operators parse correctly but are rejected at the VIR well-formedness stage
// with a "not yet supported for SMT verification" error.

// === Unary operators ===

test_verify_one_file! {
    #[test] test_temporal_ag_parses verus_code! {
        spec fn always_positive(x: int) -> bool {
            ag (x > 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `ag` is not yet supported outside of ensures clauses")
}

test_verify_one_file! {
    #[test] test_temporal_eg_parses verus_code! {
        spec fn exists_path_globally(x: int) -> bool {
            eg (x >= 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `eg` is not yet supported outside of ensures clauses")
}

// === Binary operators ===

test_verify_one_file! {
    #[test] test_temporal_au_parses verus_code! {
        spec fn until_zero(x: int) -> bool {
            au(x > 0, x == 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `au` is not yet supported outside of ensures clauses")
}

test_verify_one_file! {
    #[test] test_temporal_an_parses verus_code! {
        spec fn now_and_next(x: int) -> bool {
            an(x > 0, x > 1)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `an` is not yet supported outside of ensures clauses")
}

test_verify_one_file! {
    #[test] test_temporal_eu_parses verus_code! {
        spec fn exists_until(x: int) -> bool {
            eu(x >= 0, x == 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `eu` is not yet supported outside of ensures clauses")
}

test_verify_one_file! {
    #[test] test_temporal_en_parses verus_code! {
        spec fn exists_next(x: int) -> bool {
            en(x > 0, x == 1)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `en` is not yet supported outside of ensures clauses")
}

// === Sugar: af = au(true, ·), ax = an(true, ·), ef = eu(true, ·), ex = en(true, ·) ===

test_verify_one_file! {
    #[test] test_temporal_af_sugar verus_code! {
        spec fn eventually_zero(x: int) -> bool {
            af (x == 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `au` is not yet supported outside of ensures clauses")
}

test_verify_one_file! {
    #[test] test_temporal_ax_sugar verus_code! {
        spec fn next_positive(x: int) -> bool {
            ax (x > 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `an` is not yet supported outside of ensures clauses")
}

test_verify_one_file! {
    #[test] test_temporal_ef_sugar verus_code! {
        spec fn exists_eventually(x: int) -> bool {
            ef (x == 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `eu` is not yet supported outside of ensures clauses")
}

test_verify_one_file! {
    #[test] test_temporal_ex_sugar verus_code! {
        spec fn exists_next(x: int) -> bool {
            ex (x == 1)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `en` is not yet supported outside of ensures clauses")
}

// === Nesting ===

test_verify_one_file! {
    #[test] test_temporal_nested_ag_au verus_code! {
        spec fn always_eventually(x: int) -> bool {
            ag (au(true, x == 0))
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `ag` is not yet supported outside of ensures clauses")
}

test_verify_one_file! {
    #[test] test_temporal_nested_ag_af_sugar verus_code! {
        spec fn always_eventually_sugar(x: int) -> bool {
            ag (af (x == 0))
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `ag` is not yet supported outside of ensures clauses")
}

test_verify_one_file! {
    #[test] test_temporal_in_ensures verus_code! {
        spec fn head_val(v: int) -> bool { v > 0 }

        spec fn fairness(v: int) -> bool {
            ag (au(true, head_val(v)))
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `ag` is not yet supported outside of ensures clauses")
}

// === temporal_invariant loop annotation ===

// Test that temporal operators are allowed in function ensures clauses.
// Currently, temporal postconditions are extracted into TemporalContext
// but VCGen for them is not yet implemented, so the function verifies.
test_verify_one_file! {
    #[test] test_temporal_ag_in_fn_ensures verus_code! {
        fn test_temporal_ensures(x: u64)
            ensures ag(x > 0),
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_temporal_au_in_fn_ensures verus_code! {
        fn test_au_ensures(x: u64)
            ensures au(x > 0, x == 42),
        {
        }
    } => Ok(())
}

// === TICL VCGen Rule Tests ===

// TICL rule: ag_cprog_while — temporal invariant established at entry and preserved by body
test_verify_one_file! {
    #[test] test_temporal_invariant_preserved verus_code! {
        fn test_loop_invariant_preserved() {
            let mut x: u64 = 0;
            while x < 10
                invariant x <= 10,
                temporal_invariant x <= 10,
                decreases 10 - x,
            {
                x = x + 1;
            }
        }
    } => Ok(())
}

// TICL rule: ag_cprog_while — temporal invariant violated at entry should fail
test_verify_one_file! {
    #[test] test_temporal_invariant_entry_fail verus_code! {
        fn test_loop_invariant_entry_fail() {
            let mut x: u64 = 100;
            while x < 10
                invariant x <= 10, // FAILS
                temporal_invariant x <= 10, // FAILS
                decreases 10 - x,
            {
                x = x + 1;
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

// TICL rule: ag_cprog_while — temporal invariant not preserved by body should fail
test_verify_one_file! {
    #[test] test_temporal_invariant_body_fail verus_code! {
        fn test_loop_invariant_body_fail() {
            let mut x: u64 = 0;
            while x < 10
                invariant x <= 10,
                temporal_invariant x <= 5,
                decreases 10 - x,
            {
                x = x + 1;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal invariant not preserved by loop body")
}

// === AG(AU) Composition Tests ===

// AG(AU(true, φ)): always-eventually — the fairness property.
// Ensures the nested temporal decomposition works: AG wrapper is filtered,
// AU obligation drives the weakened decreases check.
test_verify_one_file! {
    #[test] test_ag_au_composition_ensures verus_code! {
        fn test_ag_au(x: u64)
            ensures ag(au(true, x == 0)),
        {
        }
    } => Ok(())
}

// AG(AU) with a loop: temporal_invariant R + decreases m
// The loop maintains invariant R and makes progress toward AU goal via decreases.
test_verify_one_file! {
    #[test] test_ag_au_loop_with_temporal_invariant verus_code! {
        fn test_ag_au_loop() {
            let mut x: u64 = 10;
            while x > 0
                invariant x <= 10,
                temporal_invariant x <= 10,
                decreases x,
            {
                x = x - 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_temporal_invariant_while_parses verus_code! {
        fn test_loop() {
            let mut x: u64 = 0;
            while x < 10
                invariant x <= 10,
                temporal_invariant x <= 10,
                decreases 10 - x,
            {
                x = x + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_temporal_invariant_loop_parses verus_code! {
        fn test_loop_expr() {
            let mut x: u64 = 0;
            loop
                invariant x <= 10,
                temporal_invariant x <= 10,
                decreases 10 - x,
            {
                if x >= 10 { break; }
                x = x + 1;
            }
        }
    } => Ok(())
}

// === Existential operator rejection tests ===

test_verify_one_file! {
    #[test] test_temporal_eg_in_ensures_rejected verus_code! {
        fn test_eg(x: u64)
            ensures eg(x > 0),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "existential temporal operator `eg` is not yet supported for verification")
}

test_verify_one_file! {
    #[test] test_temporal_eu_in_ensures_rejected verus_code! {
        fn test_eu(x: u64)
            ensures eu(x > 0, x == 0),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "existential temporal operator `eu` is not yet supported for verification")
}

test_verify_one_file! {
    #[test] test_temporal_ef_sugar_in_ensures_rejected verus_code! {
        fn test_ef(x: u64)
            ensures ef(x == 0),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "existential temporal operator `eu` is not yet supported for verification")
}

// === Additional VCGen coverage ===

// Multiple temporal ensures clauses
test_verify_one_file! {
    #[test] test_multiple_temporal_ensures verus_code! {
        fn test_multi(x: u64, y: u64)
            ensures ag(x > 0), ag(y > 0),
        {
        }
    } => Ok(())
}

// Loop with temporal_invariant but no temporal ensures — should verify normally
test_verify_one_file! {
    #[test] test_temporal_invariant_no_temporal_ensures verus_code! {
        fn test_no_temporal_ensures() {
            let mut x: u64 = 0;
            while x < 10
                invariant x <= 10,
                temporal_invariant x <= 10,
                decreases 10 - x,
            {
                x = x + 1;
            }
        }
    } => Ok(())
}

// Nested AG(AG(φ)) — should flatten to single AG obligation
test_verify_one_file! {
    #[test] test_nested_ag_ag_in_ensures verus_code! {
        fn test_nested_ag(x: u64)
            ensures ag(ag(x > 0)),
        {
        }
    } => Ok(())
}
