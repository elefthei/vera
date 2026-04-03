# Temporal Rules for Function Calls and Async/Await

**Date**: 2026-04-03
**Status**: Design approved, pending implementation

## Summary

Add contract-based temporal obligation checking to function calls (sync and async) in Vera's temporal VCGen. When a function is called inside a temporal context (AG/AU/AF), and the callee has temporal ensures, assert that the callee's temporal ensures *imply* the caller's temporal obligations. This makes calls transparent rather than atomic: the caller's temporal properties are guaranteed to hold at every intermediate state inside the callee.

## Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Async execution model | Lazy Rust futures | `let p = async_fn()` creates a handle; body runs at `p.await` |
| Await atomicity | Transparent (non-atomic) | Caller's AG(φ) must hold inside callee's execution |
| Obligation propagation | Automatic checking | Vera checks callee preserves caller's obligations without explicit annotation |
| Checking strategy | Modular implication | Check callee's temporal ensures ⟹ caller's obligations (no cross-function inlining) |
| Scope of implication check | All calls (sync + async) | Uniform system: both sync and async calls are contract-based |
| Resolution strategy | Ensures-based | Preserve temporal operators in async ensures rewriting; no function resolution needed |

## Formal Rules

### Rule 1: Function Call in Temporal Context (sync and async)

For any call `f(args)` (or `exec_await(p)`) inside a temporal context:

```
{x ← f(args); c}, w |= Φ
─────────────────────────────────────────────
If f has temporal ensures Ψ:
    assert Ψ → Φ    (callee's temporal property implies caller's)
Assume f's first-order ensures R
c[x/ret], w' |= Φ   (continuation maintains Φ)
```

Where Φ is the caller's temporal obligation and Ψ is the callee's temporal ensures.

### Rule 2: Async Bind (lazy future creation)

```
{let p = async_fn(args); c}, w |= Φ
────────────────────────────────────
           c, w |= Φ
```

No state changes at bind time. The future `p` is a handle. The caller's obligation Φ passes to the continuation `c` unchanged. This is already the existing behavior (no change needed).

### Rule 3: Await with AU/AF (terminating callee)

```
{await p; c}, w |= path AU goal
──────────────────────────────────────────────
If P[p] has temporal ensures path' AU goal':
    assert path' → path   (callee's path implies caller's)
    assert goal' → goal   (callee's goal implies caller's)
Assume P[p]'s first-order ensures R
c[ret/R], w' |= path AU goal   (continuation maintains AU)
```

**Special case**: callee ensures `af(done(R))` = `true AU done(R)`:
- `path' = true` → trivially implies any `path`
- `goal' = R` → implication check against caller's `goal`
- This is the standard bind rule, already implemented via `emit_prefix_assertions` etc.

### Rule 4: Await with AG (callee preserves property — diverging)

```
{await p; c}, w |= AG(φ)
──────────────────────────────────
P[p] has AG(ψ):   assert ψ → φ
AG obligation discharged at await point
(c is unreachable — P[p] has infinite loop)
```

If the callee has `AG(ψ)` ensures, the callee runs forever. The await point becomes a divergence point that satisfies the caller's AG obligation. The continuation `c` after await is dead code.

**Scope note**: AG-via-await (Rule 4) is designed but deferred. Phase 1 implements Rules 1-3 (AU/AF only).

## Architecture

### Component 1: Preserve Temporal Structure in Async Ensures

**File**: `source/vir/src/ast_to_sst_func.rs`, function `rewrite_async_ens_vir()`

Currently transforms every ensure `E` uniformly into:
```
awaited(future) ==> (let ret = view(future); E)
```

Change: if `E` is a temporal expression (`ExprX::Temporal(op, prop, path)`), preserve the temporal wrapper:
```
awaited(future) ==> Temporal(op, (let ret = view(future); prop), path')
```

This ensures that when `exec_await`'s ensures are assumed at the call site, the temporal structure is visible to `decompose_temporal`.

### Component 2: Temporal Implication Check at Call Sites

**File**: `source/vir/src/sst_to_air.rs`, `StmX::Call` handler (~line 2190)

After assuming the callee's ensures (step 3 of the existing call handling), add:

```rust
// After assuming callee ensures...

if !state.temporal_context.propositions.is_empty() {
    // Extract temporal ensures from assumed callee ensures
    let callee_temporal_ensures = extract_temporal_from_callee(func);

    if !callee_temporal_ensures.is_empty() {
        for caller_prop in &state.temporal_context.propositions {
            for callee_prop in &callee_temporal_ensures {
                match (caller_prop, callee_prop) {
                    (Proposition::Always { property: phi, .. },
                     Proposition::Always { property: psi, .. }) => {
                        // AG: assert ψ → φ
                        let implication = mk_implies(&psi_expr, &phi_expr);
                        stmts.push(assert(implication,
                            "callee's AG property must imply caller's AG obligation"));
                    }
                    (Proposition::Until { path, goal, .. },
                     Proposition::Until { path: path2, goal: goal2, .. }) => {
                        // AU: assert path' → path ∧ goal' → goal
                        let path_impl = mk_implies(&path2_expr, &path_expr);
                        let goal_impl = mk_implies(&goal2_expr, &goal_expr);
                        stmts.push(assert(mk_and(&[path_impl, goal_impl]),
                            "callee's AU property must imply caller's AU obligation"));
                    }
                    _ => {
                        // Mismatched temporal types:
                        // - Until callee in Always caller: callee terminates → AG continues
                        //   after call via existing prefix/state assertions. No implication needed.
                        // - Always callee in Until caller: callee diverges → AU can never
                        //   reach its goal through this call. This is not an error per se
                        //   (another path may reach the goal), but the call doesn't help.
                        //   No assertion emitted.
                    }
                }
            }
        }
    }
    // If callee has NO temporal ensures:
    // - For AU caller: standard bind rule applies (already works)
    // - For AG caller: call is finite step, AG checked before/after (existing assertions)
}
```

### Component 3: Extract Callee Temporal Ensures

**File**: `source/vir/src/sst_to_air.rs` (new helper function)

```rust
fn extract_temporal_from_callee(func: &FunctionSst) -> Vec<Proposition> {
    let mut obligations = Vec::new();
    for ens in func.x.ensure.iter() {
        match &ens.x {
            ExpX::Temporal(op, prop, path) => {
                decompose_temporal(op, prop, path, false, &mut obligations);
            }
            _ => {} // Non-temporal ensures: skip (handled by standard bind rule)
        }
    }
    obligations
}
```

For async functions via `exec_await`, the future argument's type traces back to the original async function. We look up that function in `ctx.func_map` (not `exec_await` itself) to extract its temporal ensures. For sync calls, `func` is already the callee.

### Component 4: async_functions.rs Tests

**File**: `source/rust_verify_test/tests/async_functions.rs`

New tests:

1. **Async AU/AF through await**: Async function with `af(done(R))`, caller in AU temporal loop uses `await` as progress step. Verifier checks callee's `done(R)` satisfies caller's goal.

2. **Sync call with temporal ensures in temporal context**: Non-async function with `ag(φ)` called inside caller's `ag(ψ)` where `φ → ψ`. Implication check passes.

3. **Sync call temporal mismatch (fail)**: Function with `ag(φ)` called in `ag(ψ)` where `φ` does NOT imply `ψ`. Should fail.

4. **Async + AU implication**: Async function with `au(path', done(goal'))` awaited by caller with `au(path, done(goal))` where `path' → path` and `goal' → goal`.

5. **Standard async (no temporal ensures) in temporal context**: Async function with only `af(done(R))`. Existing bind rule handles it — should pass unchanged.

## Scope

**Phase 1 (this spec)**:
- Temporal implication check for sync calls with temporal ensures
- Temporal implication check for async calls via `exec_await` with AU/AF ensures
- Preserve temporal structure in `rewrite_async_ens_vir`
- Tests for AU/AF cases

**Deferred**:
- AG-via-await as divergence (Rule 4)
- `select!`/`join!` combinators
- Temporal properties across concurrent async tasks
