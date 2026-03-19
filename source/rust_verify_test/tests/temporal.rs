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

// === temporal invariant loop annotation ===

// Test that temporal operators in function ensures clauses are properly verified.
// AG postconditions require temporal invariant on a loop — empty bodies get R6 error.
test_verify_one_file! {
    #[test] test_temporal_ag_in_fn_ensures verus_code! {
        fn test_temporal_ensures(x: u64)
            ensures ag(x > 0),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal postcondition AG(...) requires at least one loop with an invariant")
}

test_verify_one_file! {
    #[test] test_temporal_au_in_fn_ensures verus_code! {
        fn test_au_ensures(x: u64)
            ensures au(x > 0, x == 42),
        {
        }
    } => Ok(()) // AU without AG doesn't require temporal invariant; no loop = no checks
}

// === TICL VCGen Rule Tests ===

// TICL rule: ag_cprog_while — invariant = temporal refinement R, established at entry and preserved by body
test_verify_one_file! {
    #[test] test_temporal_inv_preserved verus_code! {
        fn test_loop_invariant_preserved(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x <= 10),
        {
            loop
                invariant *x <= 10,
            {
                if *x < 10 {
                    *x = *x + 1;
                } else {
                    *x = 0;
                }
            }
        }
    } => Ok(())
}

// TICL rule: ag_cprog_while — invariant violated at entry should fail
test_verify_one_file! {
    #[test] test_temporal_inv_entry_fail verus_code! {
        fn test_loop_invariant_entry_fail(x: &mut u64)
            requires *old(x) == 100,
            ensures ag(*x <= 10),
        {
            loop
                invariant *x <= 10, // FAILS
            {
                *x = 0;
            }
        }
    } => Err(err) => assert_fails(err, 1)
}

// TICL rule: ag_cprog_while — invariant (= R) does not imply AG property φ
test_verify_one_file! {
    #[test] test_temporal_inv_body_fail verus_code! {
        fn test_loop_invariant_body_fail(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x > 100),
        {
            loop
                invariant *x <= 10,
            {
                if *x < 10 {
                    *x = *x + 1;
                } else {
                    *x = 0;
                }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal invariant does not imply AG postcondition property")
}

// === AG(AU) Composition Tests ===

// AG(AU(true, φ)): always-eventually — requires temporal invariant on a loop.
// Empty body with AG nesting gets R6 error.
test_verify_one_file! {
    #[test] test_ag_au_composition_ensures verus_code! {
        fn test_ag_au(x: u64)
            ensures ag(au(true, x == 0)),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal postcondition AG(...) requires at least one loop with an invariant")
}

// AG(AU) with a loop: loop invariant R + decreases m
// The loop maintains invariant R and makes progress toward AU goal via decreases.
test_verify_one_file! {
    #[test] test_ag_au_loop_with_temporal_inv verus_code! {
        fn test_ag_au_loop() {
            let mut x: u64 = 10;
            while x > 0
                invariant x <= 10,
                decreases x,
            {
                x = x - 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_temporal_inv_while_parses verus_code! {
        fn test_loop() {
            let mut x: u64 = 0;
            while x < 10
                invariant x <= 10,
                decreases 10 - x,
            {
                x = x + 1;
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_temporal_inv_loop_parses verus_code! {
        fn test_loop_expr() {
            let mut x: u64 = 0;
            loop
                invariant x <= 10,
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

// Multiple temporal ensures clauses — AG requires temporal invariant
test_verify_one_file! {
    #[test] test_multiple_temporal_ensures verus_code! {
        fn test_multi(x: u64, y: u64)
            ensures ag(x > 0), ag(y > 0),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal postcondition AG(...) requires at least one loop with an invariant")
}

// Loop with temporal invariant but no temporal ensures — should verify normally
test_verify_one_file! {
    #[test] test_temporal_inv_no_temporal_ensures verus_code! {
        fn test_no_temporal_ensures() {
            let mut x: u64 = 0;
            while x < 10
                invariant x <= 10,
                decreases 10 - x,
            {
                x = x + 1;
            }
        }
    } => Ok(())
}

// Nested AG(AG(φ)) — should flatten to single AG obligation, still requires temporal invariant
test_verify_one_file! {
    #[test] test_nested_ag_ag_in_ensures verus_code! {
        fn test_nested_ag(x: u64)
            ensures ag(ag(x > 0)),
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal postcondition AG(...) requires at least one loop with an invariant")
}

// === I4: Function calls inside loops with temporal invariant ===

// Function call preserving temporal invariant — caught by loop-end R check
test_verify_one_file! {
    #[test] test_call_in_loop_preserves_temporal_inv verus_code! {
        fn increment(x: &mut u64)
            requires *old(x) < 10,
            ensures *x == *old(x) + 1,
        {
            *x = *x + 1;
        }

        fn test_call_preserves() {
            let mut x: u64 = 0;
            while x < 10
                invariant x <= 10,
                decreases 10 - x,
            {
                if x < 10 {
                    increment(&mut x);
                }
            }
        }
    } => Ok(())
}

// Function call breaking temporal invariant (R = loop invariant) — detected at loop-end assert R
test_verify_one_file! {
    #[test] test_call_in_loop_breaks_temporal_inv verus_code! {
        fn add_hundred(x: &mut u64)
            requires *old(x) <= 10,
            ensures *x == *old(x) + 100,
        {
            *x = *x + 100;
        }

        fn test_call_breaks(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x <= 10),
        {
            loop
                invariant *x <= 10,
            {
                add_hundred(x); // Breaks invariant: 0 + 100 > 10
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "invariant not satisfied at end of loop body")
}

// === I7: Explicit R → φ implication tests ===

// AG with terminating while loop — fails (no temporal loop found, utility loop only)
test_verify_one_file! {
    #[test] test_temporal_inv_does_not_imply_postcondition verus_code! {
        fn test_r_not_implies_phi(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x > 100),
        {
            while *x < 10
                invariant *x <= 10,
                decreases 10 - *x,
            {
                *x = *x + 1;
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "temporal postcondition AG(...) requires at least one loop with an invariant")
}

// loop invariant R implies AG postcondition φ (R ⊆ φ) — should pass
// AG requires an infinite loop (TICL ag_cprog_while: condition always true)
test_verify_one_file! {
    #[test] test_temporal_inv_implies_postcondition verus_code! {
        fn test_r_implies_phi(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x <= 10),
        {
            loop
                invariant *x <= 10,
            {
                // Infinite loop: x oscillates between 0 and 10
                if *x < 10 {
                    *x = *x + 1;
                } else {
                    *x = 0;
                }
            }
        }
    } => Ok(())
}

// === I5: AU path property tests ===

// AF(ψ) = AU(true, ψ): path property is trivially true, only decreases matters.
// Models: while(len > 0) { pop(); } with ensures af(len == 0), decreases len
test_verify_one_file! {
    #[test] test_af_drain_loop verus_code! {
        fn drain(len: &mut u64)
            requires *old(len) > 0,
            ensures af(*len == 0),
        {
            while *len > 0
                invariant true,
                decreases *len,
            {
                *len = (*len - 1) as u64;
            }
        }
    } => Ok(())
}

// AU(φ, ψ) with non-trivial path: φ = (x > 0), ψ = (x == 0).
// "x stays positive UNTIL it reaches zero"
// At the loop boundary: assert ψ ∨ φ = (x == 0) ∨ (x > 0), which holds for x >= 0.
test_verify_one_file! {
    #[test] test_au_nontrivial_path verus_code! {
        fn count_down(x: &mut u64)
            requires *old(x) > 0 && *old(x) <= 1000,
            ensures au(*x > 0, *x == 0),
        {
            while *x > 0
                invariant *x <= 1000,
                decreases *x,
            {
                *x = (*x - 1) as u64;
            }
        }
    } => Ok(())
}

// AU(false, ψ): path property is `false` — should fail because before ψ holds,
// we need `ψ ∨ false` = `ψ`, which doesn't hold at the start.
test_verify_one_file! {
    #[test] test_au_false_path_fails verus_code! {
        fn impossible_path(x: &mut u64)
            requires *old(x) > 0 && *old(x) <= 1000,
            ensures au(false, *x == 0),
        {
            while *x > 0
                invariant *x <= 1000,
                decreases *x,
            {
                *x = (*x - 1) as u64;
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "temporal AU: path property violated before goal reached")
}

// === R3: continue must check temporal invariant ===

// Continue skips end-of-body; temporal invariant must be preserved at continue too.
// Uses infinite loop (AG requires non-termination).
test_verify_one_file! {
    #[test] test_continue_breaks_temporal_inv verus_code! {
        fn test_continue(x: &mut u64)
            ensures ag(*x <= 10),
        {
            *x = 0;
            loop
                invariant *x <= 10,
            {
                if *x == 5 {
                    // This continue path must still satisfy temporal invariant.
                    // Since *x == 5 and *x <= 10, it does, so this should pass.
                    *x = 0;
                    continue;
                }
                if *x < 10 {
                    *x = *x + 1;
                } else {
                    *x = 0;
                }
            }
        }
    } => Ok(())
}

// Continue that violates invariant in AG context should fail.
// R = invariant = *x <= 10; continue after setting *x = 50 breaks R.
test_verify_one_file! {
    #[test] test_continue_violates_temporal_inv verus_code! {
        fn test_continue_bad(x: &mut u64)
            ensures ag(*x <= 10),
        {
            *x = 0;
            loop
                invariant *x <= 10,
            {
                if *x == 3 {
                    *x = 50;  // Breaks invariant *x <= 10
                    continue;
                }
                if *x < 10 {
                    *x = *x + 1;
                } else {
                    *x = 0;
                }
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "loop invariant not satisfied")
}

// === R2: AG nesting requires temporal invariant ===

// ag(au(true, φ)) with a terminating while loop → fails (AG requires infinite loop)
test_verify_one_file! {
    #[test] test_ag_au_without_temporal_inv verus_code! {
        fn test_ag_no_inv(x: &mut u64)
            ensures ag(au(true, *x == 0)),
        {
            *x = 10;
            while *x > 0
                invariant *x <= 10,
                decreases *x,
            {
                *x = (*x - 1) as u64;
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "AG temporal property requires an infinite loop")
}

// Plain au(true, φ) without temporal invariant should still work (no AG invariance needed)
test_verify_one_file! {
    #[test] test_plain_au_without_temporal_inv verus_code! {
        fn test_au_no_inv(x: &mut u64)
            requires *old(x) == 10,
            ensures au(true, *x == 0),
        {
            while *x > 0
                invariant *x <= 10,
                decreases *x,
            {
                *x = (*x - 1) as u64;
            }
        }
    } => Ok(())
}

// === S7: AG loops must never exit (TICL ag_cprog_while condition 2) ===

// AG with infinite loop — passes (no exit path)
test_verify_one_file! {
    #[test] test_ag_infinite_loop_pass verus_code! {
        fn test_ag_inf(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x <= 10),
        {
            loop
                invariant *x <= 10,
            {
                if *x < 10 {
                    *x = *x + 1;
                } else {
                    *x = 0;
                }
            }
        }
    } => Ok(())
}

// AG with terminating while loop — fails (loop exits, violating AG non-exit requirement)
test_verify_one_file! {
    #[test] test_ag_terminating_loop_fail verus_code! {
        fn test_ag_term(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x <= 10),
        {
            while *x < 5
                invariant *x <= 10,
                decreases 10 - *x,
            {
                *x = *x + 1;
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "temporal postcondition AG(...) requires at least one loop with an invariant")
}

// === S2: Deferred R6 — utility loops coexist with temporal loops ===

// Function with utility loop + temporal infinite loop — utility loop has no temporal invariant
test_verify_one_file! {
    #[test] test_utility_loop_with_temporal_loop verus_code! {
        fn test_multi_loop(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x <= 20),
        {
            // Utility loop — no temporal invariant needed
            let mut setup: u64 = 5;
            while setup > 0
                invariant setup <= 5,
                decreases setup,
            {
                setup = setup - 1;
            }
            // Main temporal loop (infinite — AG requires non-termination)
            loop
                invariant *x <= 20,
            {
                if *x < 20 {
                    *x = *x + 1;
                } else {
                    *x = 0;
                }
            }
        }
    } => Ok(())
}

// === Temporal operators drive decreases requirements ===

// AG loop without decreases — passes (infinite loop, no termination needed)
test_verify_one_file! {
    #[test] test_ag_no_decreases_pass verus_code! {
        fn test_ag_no_dec(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x <= 10),
        {
            loop
                invariant *x <= 10,
            {
                if *x < 10 {
                    *x = *x + 1;
                } else {
                    *x = 0;
                }
            }
        }
    } => Ok(())
}

// AU loop without decreases — fails (AU needs decreases for progress)
test_verify_one_file! {
    #[test] test_au_no_decreases_fail verus_code! {
        fn test_au_no_dec(x: &mut u64)
            requires *old(x) == 5,
            ensures af(*x == 0),
        {
            loop
                invariant *x <= 5,
            {
                if *x > 0 {
                    *x = *x - 1;
                }
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "AU temporal property requires a decreases clause")
}

// Regular loop without decreases — still fails with standard error
test_verify_one_file! {
    #[test] test_regular_no_decreases_fail verus_code! {
        fn test_no_dec(x: &mut u64) {
            let mut i: u64 = 0;
            while i < 10
                invariant i <= 10,
            {
                i = i + 1;
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "loop must have a decreases clause")
}

// === TICL ag_seq / aul_seq: Prefix temporal obligation tests ===
// These test that the temporal property φ must hold at every intermediate state
// in prefix code before the temporal loop (TICL sequence composition rules).

// Assignment in prefix violates AG property — should fail
test_verify_one_file! {
    #[test] test_prefix_assign_violates_ag verus_code! {
        fn test_prefix_bad(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x <= 20),
        {
            *x = 999; // violates *x <= 20
            *x = 0;
            loop
                invariant *x <= 20,
            {
                if *x < 20 { *x = *x + 1; } else { *x = 0; }
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "temporal property must hold at every step")
}

// Assignment in prefix satisfies AG property — should pass
test_verify_one_file! {
    #[test] test_prefix_assign_clean_ag verus_code! {
        fn test_prefix_ok(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x <= 20),
        {
            *x = 5; // 5 <= 20, OK
            loop
                invariant *x <= 20,
            {
                if *x < 20 { *x = *x + 1; } else { *x = 0; }
            }
        }
    } => Ok(())
}

// Utility loop in prefix violates AG property — should fail
// The utility loop body sets x to 999, violating the AG invariant *x <= 20
// which is added as an additional invariant on the utility loop.
test_verify_one_file! {
    #[test] test_prefix_utility_loop_violates_ag verus_code! {
        fn test_utility_bad(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x <= 20),
        {
            let mut setup: u64 = 5;
            while setup > 0
                invariant setup <= 5,
                decreases setup,
            {
                *x = 999; // breaks the additional invariant *x <= 20 at iteration boundary
                setup = setup - 1;
            }
            loop
                invariant *x <= 20,
            {
                if *x < 20 { *x = *x + 1; } else { *x = 0; }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "invariant not satisfied at end of loop body")
}

// Utility loop in prefix preserves AG property — should pass
// The utility loop body doesn't modify x, so the additional invariant *x <= 20 is preserved.
test_verify_one_file! {
    #[test] test_prefix_utility_loop_preserves_ag verus_code! {
        fn test_utility_ok(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x <= 20),
        {
            let mut setup: u64 = 5;
            while setup > 0
                invariant setup <= 5,
                decreases setup,
            {
                setup = setup - 1;
                // x is not modified — additional invariant *x <= 20 trivially preserved
            }
            loop
                invariant *x <= 20,
            {
                if *x < 20 { *x = *x + 1; } else { *x = 0; }
            }
        }
    } => Ok(())
}

// Function call in prefix violates AG property — should fail
test_verify_one_file! {
    #[test] test_prefix_call_violates_ag verus_code! {
        fn set_high(x: &mut u64)
            ensures *x == 999,
        {
            *x = 999;
        }

        fn test_call_bad(x: &mut u64)
            requires *old(x) == 0,
            ensures ag(*x <= 20),
        {
            set_high(x); // x becomes 999, violating *x <= 20
            loop
                invariant *x <= 20,
            {
                if *x < 20 { *x = *x + 1; } else { *x = 0; }
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "temporal property must hold at every step")
}

// Conditional in prefix — one branch violates AG property — should fail
test_verify_one_file! {
    #[test] test_prefix_conditional_violates_ag verus_code! {
        fn test_cond_bad(x: &mut u64, flag: bool)
            requires *old(x) == 0,
            ensures ag(*x <= 20),
        {
            if flag {
                *x = 5; // OK
            } else {
                *x = 999; // violates *x <= 20
            }
            loop
                invariant *x <= 20,
            {
                if *x < 20 { *x = *x + 1; } else { *x = 0; }
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "temporal property must hold at every step")
}

// AU with non-trivial path property checked in prefix — should fail
// au(*x > 0, *x == 0): path property *x > 0 must hold at every step until *x == 0.
// But prefix sets x to 0 immediately, violating the path property.
test_verify_one_file! {
    #[test] test_prefix_au_path_property_fail verus_code! {
        fn test_au_prefix_bad(x: &mut u64)
            requires *old(x) == 10,
            ensures au(*x > 0, *x == 0),
        {
            *x = 0; // violates path property *x > 0 (and coincidentally reaches goal)
            while *x > 0
                invariant *x <= 10,
                decreases *x,
            {
                *x = (*x - 1) as u64;
            }
        }
    } => Err(err) => assert_any_vir_error_msg(err, "temporal property must hold at every step")
}

// AF (= au(true, ...)) has trivial prefix obligation — should always pass
// The path property is `true`, so no prefix assertions are generated.
test_verify_one_file! {
    #[test] test_prefix_af_trivial verus_code! {
        fn test_af_prefix_ok(x: &mut u64)
            requires *old(x) == 10,
            ensures af(*x == 0),
        {
            *x = 999; // would violate any non-trivial prefix, but AF has ⊤ prefix
            *x = 10;
            while *x > 0
                invariant *x <= 1000,
                decreases *x,
            {
                *x = (*x - 1) as u64;
            }
        }
    } => Ok(())
}
