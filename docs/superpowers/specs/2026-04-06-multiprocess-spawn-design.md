# Multi-Process Vera: Spawn Trait with Rely-Guarantee Reasoning

**Date**: 2026-04-06
**Status**: Design approved, pending implementation
**Branch**: `wp-refactor`

## Summary

Make the multi-process state explicit in Rust code via a `vstd::spawn::Executor` trait. Objects implementing `Executor` carry a ghost process map `P : PID → ProcessContract`. Each spawned async block declares its rely (requires on shared state from other processes) and guarantee (temporal ensures). The verifier checks rely-guarantee compatibility across all processes.

## Decisions

| Decision | Choice | Rationale |
|----------|--------|-----------|
| Trait source | `vstd::spawn::Executor` (our own) | Full control over spec; no dependency on external crates |
| Ghost model | Process Map `Map<PID, ProcessContract>` | Matches formal model `P : PID → Term`; per-process reasoning |
| Process annotation | `ensures` on async block | Verus-idiomatic; no syntax changes needed |
| Composition | Rely-guarantee | Sound for cooperative scheduling; each process has rely + guarantee |
| Scheduling | Cooperative (Rust async model) | No preemption → no interference during a process's turn |

## User-Facing API

### vstd/spawn.rs

```rust
use vstd::prelude::*;

/// Process identifier.
pub type PID = u64;

/// A spawned process's contract: what it relies on and what it guarantees.
pub struct ProcessContract<S> {
    /// Rely: state predicate that other processes must maintain.
    /// "If you give me a state satisfying rely, I guarantee my temporal property."
    pub rely: spec_fn(S) -> bool,
    /// Guarantee: temporal property this process maintains.
    /// Represented as a state predicate (the inner property of AG/AF/AU).
    pub guarantee: spec_fn(S) -> bool,
}

/// External trait specification for executors (schedulers).
/// Types implementing Executor can spawn async processes.
pub trait Executor<S> {
    /// Ghost view: map of spawned processes and their contracts.
    #[verifier::prophetic]
    spec fn view(&self) -> Map<PID, ProcessContract<S>>;

    /// Spawn a future with temporal contract.
    /// The future's requires becomes the rely, ensures becomes the guarantee.
    /// Returns the PID of the spawned process.
    #[verifier::external_body]
    fn spawn<F: Future>(&mut self, future: F) -> (pid: PID)
        ensures
            self@.contains_key(pid),
            // The process map is extended with the new process
    ;
}
```

### Example Usage

```rust
fn system(exec: &mut impl Executor<u64>, shared: &mut u64)
    requires *shared == 0,
    ensures ag(*shared <= 100),
{
    // Process 1: keeps shared <= 50
    exec.spawn(async
        requires *shared <= 50,          // RELY
        ensures ag(*shared <= 50),       // GUARANTEE
    {
        loop
            invariant *shared <= 50,
        {
            if *shared < 50 { *shared = *shared + 1; }
            else { *shared = 0; }
        }
    });

    // Process 2: keeps shared <= 100
    exec.spawn(async
        requires *shared <= 50,          // RELY
        ensures ag(*shared <= 100),      // GUARANTEE
    {
        loop
            invariant *shared <= 100,
        {
            // just observes, doesn't modify
        }
    });
}
```

**Verification obligations:**
1. Process 1 body satisfies `ag(*shared <= 50)` assuming `*shared <= 50` (rely)
2. Process 2 body satisfies `ag(*shared <= 100)` assuming `*shared <= 50` (rely)
3. Guarantee₁ (`*shared <= 50`) implies Rely₂ (`*shared <= 50`) ✓
4. Guarantee₂ (`*shared <= 100`) implies Rely₁ (`*shared <= 50`) ✗ — must strengthen Guarantee₂!
5. Conjunction of guarantees implies global ensures: `(*shared <= 50) ∧ (*shared <= 100) → (*shared <= 100)` ✓

## VCGen Rules

### At Spawn Site

When processing `exec.spawn(async requires R ensures G { body })`:

```
wp(exec.spawn(async requires R ensures G { body }), φ) = λσ.
    (R σ → wp(body, G) σ)          // verify body under rely
    ∧ wp(continuation, φ) σ        // continue with rest of function
```

The process contract `(R, G)` is recorded in `WpContext.process_map`.

### At Function Exit

For each pair of processes `(i, j)` in the process map:

```
assert Gᵢ(σ) → Rⱼ(σ)     // process i's guarantee implies process j's rely
```

For the global property:

```
assert (G₁(σ) ∧ G₂(σ) ∧ ... ∧ Gₙ(σ)) → global_ensures(σ)
```

### Await Rule (unchanged)

`future.await` applies the existing bind rule. The process's guarantee becomes the assumed postcondition after await.

## Implementation Plan

### Phase 1: vstd spawn module
- Create `source/vstd/spawn.rs`
- Define `PID`, `ProcessContract`, `Executor` trait
- Register module in `vstd/vstd.rs`

### Phase 2: VIR AST extension
- Add `ExprX::Spawn(Expr, Expr)` to `ast.rs` (body, contract)
- Handle in `ast_visitor.rs`, `modes.rs`, `early_exit_cf.rs`, `well_formed.rs`
- Add `SpawnItem` to `verus_items.rs`

### Phase 3: HIR → VIR lowering
- In `rust_to_vir_expr.rs`, detect `Executor::spawn()` calls
- Extract the async block's requires/ensures as the process contract
- Lower to `ExprX::Spawn`

### Phase 4: AST → SST lowering
- In `ast_to_sst.rs`, handle `ExprX::Spawn`
- Record the process contract in a context struct
- Lower the async body for separate verification

### Phase 5: VCGen (sst_to_air.rs)
- Extend `WpContext` with `process_map: Vec<(Exp, Exp)>` (rely, guarantee pairs)
- At `StmX::Spawn`: verify body under rely, add to process map
- At function exit: emit pairwise rely-guarantee assertions
- Emit global property composition check

### Phase 6: Tests
- Two-process AG example (shared counter)
- Rely-guarantee compatibility pass/fail
- Deadlock freedom with lock (two tasks, rely-guarantee)
- Mutation tests for soundness

## Risks

1. **Async block ensures syntax**: Verus may not support `ensures` on async blocks directly. May need macro desugaring or a wrapper function pattern.
2. **Shared state modeling**: `&mut` references in Rust can't be shared across async tasks without `Arc<Mutex<>>`. May need ghost/spec-level shared state.
3. **Non-interference during turns**: Cooperative scheduling means no preemption, but the verifier needs to track that processes don't interleave mid-statement.
4. **Process map growth**: Each spawn adds to the map. The pairwise check is O(n²) in the number of processes.
