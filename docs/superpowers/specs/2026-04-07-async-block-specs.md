# Plan: Annotated Async Blocks — `async requires R ensures G { body }`

**Date**: 2026-04-07
**Status**: Designed, pending implementation
**Branch**: `wp-refactor`

## Summary

Extend Verus syntax to allow `requires`/`ensures` on `async { }` block expressions. These specs serve as the rely-guarantee contract when the block is spawned on an executor. The async block's requires = rely, ensures = guarantee.

## Target Syntax

```rust
exec.spawn(async
    requires *counter <= 100,
    ensures ag(*counter <= 100),
{
    loop
        invariant *counter <= 100,
    {
        if *counter < 100 { *counter += 1; }
    }
});
```

## Implementation Layers

### Layer 1: Macro (`builtin_macros/src/syntax.rs`)

The `verus!{}` macro processes all Verus syntax. Currently `Expr::Async` (from syn) flows through unmodified. 

**Change**: When visiting `Expr::Async`, check if the block body starts with `requires`/`ensures` header statements (using the existing header parsing infrastructure from `headers.rs`). If found:
1. Extract the requires/ensures expressions
2. Rewrite the block to attach them as attributes (or ghost statements)
3. Emit the async block with the specs preserved

Key reference: how `fn` signatures get their requires/ensures parsed (around line 1060-1080 in syntax.rs). The same `take_header` mechanism can be adapted for async blocks.

### Layer 2: HIR→VIR (`rust_to_vir_expr.rs`)

Rustc desugars `async { body }` into `ExprKind::Closure` with `ClosureKind::Async`. The `closure_to_vir` function (line ~3824) converts this to `ExprX::Closure`.

**Change**: When the closure is an async block, check for the attached requires/ensures attributes. Produce an `ExprX::Closure` (or new `ExprX::AsyncBlock`) that carries the spec.

Alternative: create a new `ExprX::AsyncBlock(requires, ensures, body)` variant.

### Layer 3: AST→SST (`ast_to_sst.rs`)

**Change**: Lower `ExprX::AsyncBlock` similarly to `ExprX::Await` — the body is verified as a standalone computation with the declared requires as precondition and ensures as postcondition.

### Layer 4: VCGen (`sst_to_air.rs`)

**Change**: When an async block with specs is encountered as an argument to `Executor::spawn()`:
1. Verify the body satisfies its ensures under the requires assumption
2. Add (requires, ensures) to `state.wp.process_map`
3. Existing `emit_rely_guarantee_checks` handles pairwise checking at function exit

## syn Dependency

`ExprAsync` in our patched syn already has `attrs: Vec<Attribute>` and `block: Block`. The requires/ensures can be:
- Parsed from the block's leading statements (like function body headers)
- Or added as attributes in the attrs field

## Risk: Rust Desugaring

Rust desugars `async { body }` before we see it in HIR. The key question: do the macro-level attributes survive the desugaring? Since `builtin_macros` runs BEFORE rustc's desugaring, we can rewrite the block to preserve the specs as `#[verus_spec(...)]` attributes that survive into HIR.

## Dependencies

- Requires `Executor` trait from `vstd/spawn.rs` ✅ (already exists)
- Requires `process_map` in `WpContext` ✅ (already exists)
- Requires `emit_rely_guarantee_checks` ✅ (already exists)
