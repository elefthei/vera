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
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `ag` is not yet supported for SMT verification")
}

test_verify_one_file! {
    #[test] test_temporal_eg_parses verus_code! {
        spec fn exists_path_globally(x: int) -> bool {
            eg (x >= 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `eg` is not yet supported for SMT verification")
}

// === Binary operators ===

test_verify_one_file! {
    #[test] test_temporal_au_parses verus_code! {
        spec fn until_zero(x: int) -> bool {
            au(x > 0, x == 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `au` is not yet supported for SMT verification")
}

test_verify_one_file! {
    #[test] test_temporal_an_parses verus_code! {
        spec fn now_and_next(x: int) -> bool {
            an(x > 0, x > 1)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `an` is not yet supported for SMT verification")
}

test_verify_one_file! {
    #[test] test_temporal_eu_parses verus_code! {
        spec fn exists_until(x: int) -> bool {
            eu(x >= 0, x == 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `eu` is not yet supported for SMT verification")
}

test_verify_one_file! {
    #[test] test_temporal_en_parses verus_code! {
        spec fn exists_next(x: int) -> bool {
            en(x > 0, x == 1)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `en` is not yet supported for SMT verification")
}

// === Sugar: af = au(true, ·), ax = an(true, ·), ef = eu(true, ·), ex = en(true, ·) ===

test_verify_one_file! {
    #[test] test_temporal_af_sugar verus_code! {
        spec fn eventually_zero(x: int) -> bool {
            af (x == 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `au` is not yet supported for SMT verification")
}

test_verify_one_file! {
    #[test] test_temporal_ax_sugar verus_code! {
        spec fn next_positive(x: int) -> bool {
            ax (x > 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `an` is not yet supported for SMT verification")
}

test_verify_one_file! {
    #[test] test_temporal_ef_sugar verus_code! {
        spec fn exists_eventually(x: int) -> bool {
            ef (x == 0)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `eu` is not yet supported for SMT verification")
}

test_verify_one_file! {
    #[test] test_temporal_ex_sugar verus_code! {
        spec fn exists_next(x: int) -> bool {
            ex (x == 1)
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `en` is not yet supported for SMT verification")
}

// === Nesting ===

test_verify_one_file! {
    #[test] test_temporal_nested_ag_au verus_code! {
        spec fn always_eventually(x: int) -> bool {
            ag (au(true, x == 0))
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `ag` is not yet supported for SMT verification")
}

test_verify_one_file! {
    #[test] test_temporal_nested_ag_af_sugar verus_code! {
        spec fn always_eventually_sugar(x: int) -> bool {
            ag (af (x == 0))
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `ag` is not yet supported for SMT verification")
}

test_verify_one_file! {
    #[test] test_temporal_in_ensures verus_code! {
        spec fn head_val(v: int) -> bool { v > 0 }

        spec fn fairness(v: int) -> bool {
            ag (au(true, head_val(v)))
        }
    } => Err(err) => assert_vir_error_msg(err, "temporal operator `ag` is not yet supported for SMT verification")
}
