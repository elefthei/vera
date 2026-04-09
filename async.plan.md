# Async Block Annotation Syntax

## Goal
Support `async requires R ensures G { body }` — annotated async blocks with rely-guarantee contracts.

## Why
Currently, only `async fn` supports `requires`/`ensures`. To spawn inline async blocks with contracts on an Executor, users must wrap every block in a named async fn. Direct annotation is more ergonomic:

```rust
exec.spawn(async
    requires *counter <= 100,
    ensures ag(*counter <= 100),
{
    loop { /* ... */ }
});
```

## Current State
- `async fn` with requires/ensures: ✅ works
- `async { body }` without specs: ✅ works (standard Rust)
- `async requires R ensures G { body }`: ❌ not supported

## Implementation Layers

### Layer 1: Macro (`builtin_macros/src/syntax.rs`)
- Add `handle_async_blocks` to the `visit_expr_mut` visitor
- When visiting `Expr::Async`, check if the block body starts with `requires`/`ensures` header statements
- Extract the specs and attach as `#[verus::internal(async_block_specs)]` attributes
- The verus! macro already parses requires/ensures in function bodies — reuse that infrastructure

**Key reference:** `closure_to_vir` in `rust_to_vir_expr.rs` (line ~3824) already extracts requires/ensures from closures via `vir::headers::read_header`. Async blocks desugar to closures.

### Layer 2: HIR→VIR (`rust_to_vir_expr.rs`)
- In `ExprKind::Closure` handler (line ~3001), detect the `async_block_specs` attribute
- Call `closure_to_vir` which already uses `read_header` to extract requires/ensures
- Produce `ExprX::NonSpecClosure` with the specs (like exec closures already do)

**Alternative:** Add `ExprX::AsyncBlock { requires, ensures, body }` variant to `ast.rs`. Cleaner but more code to add in all visitors.

### Layer 3: SST Lowering (`ast_to_sst.rs`)
- Handle the async block similarly to `ExprX::Await` — the body produces a future
- Record the requires/ensures in the spawned_funs mechanism

### Layer 4: VCGen (`sst_to_air.rs`)
- At spawn detection, extract the async block's specs as (rely, guarantee)
- Existing `process_map` and `emit_rely_guarantee_checks` handle the rest

## Risk
Rust desugars `async { body }` into a closure BEFORE builtin_macros processes it. The attributes may or may not survive this desugaring. If they don't survive, fallback: require users to use `async fn` (which already works) instead of inline blocks.

## Estimated Effort
1-2 days. Most risk is in Layer 1 (macro) and whether attributes survive Rust's async desugaring.

## Dependencies
- Executor trait (`vstd/spawn.rs`): ✅ exists
- Process map infrastructure: ✅ exists
- R-G checking: ✅ exists (needs Tier 2 wiring first)
