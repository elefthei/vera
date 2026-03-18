# Copilot Instructions for Verus

Verus is a verification tool for Rust. It proves code correctness at compile time using SMT solvers (Z3, cvc5) instead of runtime checks. The main source lives in `source/`.

## Build & Test

All commands run from the `source/` directory after activating the dev environment:

```sh
cd source
source ../tools/activate    # sets up PATH with vargo (cargo wrapper)
```

### Building

```sh
vargo build --release           # builds Verus + verifies vstd
vargo build --vstd-no-verify    # faster: skips vstd SMT verification
```

### Running the verifier

```sh
vargo run -p rust_verify --release -- ../examples/vectors.rs
# Or directly:
./target-verus/release/verus ../examples/vectors.rs
```

### Testing

```sh
vargo test -p rust_verify_test                           # full suite
vargo test -p rust_verify_test --test basic              # single test file
vargo test -p rust_verify_test --test basic test_name    # single test
vargo test --vstd-no-verify -p rust_verify_test --test basic test_name  # skip vstd verification (faster)
```

`vargo nextest run` is also supported for parallel test execution.

### Formatting

```sh
vargo fmt             # auto-format (rustfmt + verusfmt for vstd)
vargo fmt -- --check  # check only
```

### Inspecting intermediate representations

```sh
VERUS_EXTRA_ARGS="--log-all" vargo test -p rust_verify_test --test refs -- --nocapture --exact test_ref_0
# Logs VIR, AIR, and SMT-LIB to rust_verify_test/.verus-log
```

## Architecture

### Verification pipeline

Verus compiles Rust through a 7-stage pipeline:

```
Rust Source → Rust HIR → VIR-AST → VIR-SST → AIR → SMT-LIB → Z3/cvc5
```

Each stage corresponds to a crate:

| Crate | Role |
|-------|------|
| `builtin_macros` | Parses `verus! { }` syntax, rewrites to standard Rust + attributes |
| `rust_verify` | Rustc driver; converts HIR to VIR, orchestrates verification |
| `vir` | Core intermediate representations (AST and SST) and transformations |
| `air` | Thin layer that encodes VIR-SST into SMT-LIB and manages solver interaction |
| `vstd` | Verified standard library (written in Verus, built and verified separately) |
| `state_machines_macros` | Macro system for concurrent state machine verification |

### Key entry points

- `rust_verify/src/main.rs` → CLI entry point
- `rust_verify/src/verifier.rs` → `Verifier::verify_crate_inner()` orchestrates the full pipeline
- `rust_verify/src/rust_to_vir*.rs` → HIR-to-VIR conversion (types, expressions, functions, traits)
- `vir/src/ast_to_sst*.rs` → VIR-AST to VIR-SST lowering
- `vir/src/sst_to_air*.rs` → VIR-SST to AIR encoding

### Two-pass compilation

When `--compile` is used, Verus runs two rustc passes:
1. **Verification pass**: Full code including ghost/proof
2. **Compilation pass**: Ghost code erased (`Ghost<T>` → `T`, spec/proof blocks removed)

### Parallelization

Functions are grouped into "buckets" for parallel SMT verification. Each bucket gets its own Z3 solver thread. `#[spinoff_prover]` forces a function into its own bucket.

## Key Conventions

### VIR mode system

Every expression and function has a mode: `Spec`, `Proof`, or `Exec`. Mode checking (`vir/src/modes.rs`) enforces that spec code cannot call exec code, proof code can call spec but not exec, etc.

### SMT identifier encoding (`vir/src/def.rs`)

VIR encodes identifiers for SMT with specific prefixes:
- Statement-bound variables: `x@`
- Expression-bound variables: `x$`
- Types: `TYPE%ClassName`
- Snapshots: `snap%name`
- Fuel (termination checking): `fuel%function_name`

### Error handling

All pipeline stages return `Result<T, VirErr>` where `VirErr = Message`. Messages carry severity, description, source spans, and labels. When contributing diagnostics, use `air::messages::Diagnostics` trait methods.

### Test conventions

Tests live in `rust_verify_test/tests/`, one file per feature area. Tests use these macros from `common/mod.rs`:

```rust
test_verify_one_file! {
    #[test] my_test_name code![
        // Verus code to verify
    ] => Ok(())          // expect success
}

test_verify_one_file! {
    #[test] my_test_name code![
        // Verus code that should fail
    ] => Err(err) => assert_one_fails(err)  // expect exactly one verification failure
}
```

Use `VERUS_EXTRA_ARGS` env var to pass additional flags (e.g., `--print-erased-spec`) during test runs.

### vstd conventions

- Lemma names are prefixed with `lemma_` (e.g., `lemma_remove_keys_len`)
- Prefer associated functions for lemmas: `my_map.lemma_remove_keys_len(keys)` over free functions
- Ghost-only imports must be gated: `#[cfg(verus_keep_ghost)] use crate::path::to::item;`
- Format with `verusfmt` (picked up automatically by `vargo fmt`)

### Formatting requirements

All code must pass `rustfmt` (default Rust settings). Code inside `verus! { }` blocks and in `vstd` must additionally pass `verusfmt`.

## Workspace Structure

The workspace is defined in `source/Cargo.toml`. `vstd` is **excluded** from the normal workspace and built separately with verification. The custom `vargo` tool (in `source/tools/vargo/`) wraps cargo to handle this special build process.

Pinned Rust toolchain: see `rust-toolchain.toml` at the project root.

## Further Reading

- `source/CODE.md` — detailed internal architecture and developer workflows
- `CONTRIBUTING.md` — contribution guidelines and testing tips
- `BUILD.md` — build and install instructions
