# wp/WP Trait-Based Refactor of sst_to_air

**Date**: 2026-04-06
**Status**: Design approved, pending implementation
**Branch**: `wp-refactor` (off `main`)

## Summary

Refactor the monolithic 4,336-line `sst_to_air.rs` (with its 1,414-line `stm_to_stmts` function) into a clean trait-based weakest precondition architecture. Two traits mirror the slides:

- **`SingleProcessWp`** — sequential Rust VCGen (assignment, let, if, while, call)
- **`MultiProcessWp`** — extends with async/await (process dictionary, cooperative scheduling)

## Goals

- Clean separation of concerns: temporal logic, AIR emission, wp dispatch
- Extensible: adding new Rust constructs = adding a trait method
- Matches the formal slides: `wp(t, φ)` and `WP(C, φ)` are real code constructs
- All 128 existing tests pass after refactor

## Architecture

### New Files

```
source/vir/src/
├── wp_context.rs      — WpContext, Proposition, PropositionContext, temporal helpers
├── wp.rs              — SingleProcessWp trait + WpState implementation
├── wp_multi.rs        — MultiProcessWp trait + MultiWpState implementation
└── sst_to_air.rs      — slimmed: AirEmitter, exp_to_expr, body_stm_to_air entry point
```

### wp_context.rs — Temporal State

Extracted from the temporal-related fields of `State` and the standalone types:

```rust
/// Temporal goal kind: state predicate (Now) or termination (Done).
pub enum GoalKind { Now, Done }

/// A leaf temporal obligation decomposed from ensures clauses.
pub enum Proposition {
    Always { property: Exp, requires_invariance: bool },
    Until { path: Exp, goal: Exp, goal_kind: GoalKind, requires_invariance: bool },
}

/// Collection of temporal obligations for the current function.
pub struct PropositionContext {
    pub propositions: Vec<Proposition>,
}

/// Temporal verification state threaded through wp.
pub struct WpContext {
    pub temporal_context: PropositionContext,
    pub temporal_discharged: bool,
    pub has_infinite_temporal_loop: bool,
    pub temporal_prefix_obligations: Vec<Exp>,
    pub in_loop_depth: u32,
    pub ag_state_obligations: Vec<Exp>,
    pub au_path_obligations: Vec<(Exp, Exp)>,
    pub now_goal_accumulators: Vec<(Exp, Ident)>,
    pub now_acc_snapshot_counter: u32,
}
```

Also contains: `decompose_temporal()`, `extract_goal_kind()`, `extract_callee_temporal_ensures()`, `callee_has_temporal_ensures()`.

### wp.rs — SingleProcessWp Trait

```rust
/// Single-process weakest precondition.
/// Each method takes a statement and returns AIR assertions.
pub trait SingleProcessWp {
    /// Main dispatcher — matches StmX and delegates.
    fn wp_stm(&mut self, ctx: &Ctx, stm: &Stm) -> Result<Vec<Stmt>, VirErr>;

    // --- Core constructs ---
    fn wp_assign(&mut self, ctx: &Ctx, span: &Span, dest: &UniqueIdent,
                 rhs: &Exp, is_init: bool) -> Result<Vec<Stmt>, VirErr>;
    fn wp_call(&mut self, ctx: &Ctx, stm: &Stm, fun: &Fun, args: &Exps,
               dest: &Option<Dest>, ...) -> Result<Vec<Stmt>, VirErr>;
    fn wp_if(&mut self, ctx: &Ctx, cond: &Stm, then: &Stm,
             else_: &Option<Stm>) -> Result<Vec<Stmt>, VirErr>;
    fn wp_while(&mut self, ctx: &Ctx, cond: &Option<Stm>, body: &Stm,
                invs: &..., decrease: &Exps) -> Result<Vec<Stmt>, VirErr>;
    fn wp_return(&mut self, ctx: &Ctx, ret_exp: &Option<Exp>,
                 ...) -> Result<Vec<Stmt>, VirErr>;
    fn wp_block(&mut self, ctx: &Ctx, stms: &Stms) -> Result<Vec<Stmt>, VirErr>;

    // --- Temporal obligation emission ---
    fn emit_temporal_state_assertions(&mut self, ctx: &Ctx,
                                       span: &Span) -> Result<Vec<Stmt>, VirErr>;
    fn emit_temporal_implication_check(&mut self, ctx: &Ctx, span: &Span,
                                       func: &Function) -> Result<Vec<Stmt>, VirErr>;
}
```

#### WpState — Implementation

```rust
/// Concrete implementation of SingleProcessWp.
pub struct WpState {
    pub wp_ctx: WpContext,       // temporal obligations
    pub air: AirEmitter,        // AIR emission bookkeeping
}

impl SingleProcessWp for WpState {
    fn wp_stm(&mut self, ctx: &Ctx, stm: &Stm) -> Result<Vec<Stmt>, VirErr> {
        match &stm.x {
            StmX::Assign { .. } => self.wp_assign(ctx, ...),
            StmX::Call { .. } => self.wp_call(ctx, ...),
            StmX::If(..) => self.wp_if(ctx, ...),
            StmX::Loop { .. } => self.wp_while(ctx, ...),
            StmX::Return { .. } => self.wp_return(ctx, ...),
            StmX::Block(stms) => self.wp_block(ctx, stms),
            // ... remaining variants
        }
    }
    // Each method is the corresponding match arm from stm_to_stmts,
    // moved to its own focused function.
}
```

### wp_multi.rs — MultiProcessWp Trait

```rust
/// Process identifier.
pub type PID = u64;

/// Process dictionary: maps PIDs to suspended Rust terms.
pub struct ProcessDict {
    processes: HashMap<PID, Stm>,
    next_pid: PID,
}

/// Configuration C = (P, σ, i).
pub struct Configuration {
    pub processes: ProcessDict,
    pub active: PID,
}

/// Multi-process weakest precondition.
/// Extends SingleProcessWp with async/await.
pub trait MultiProcessWp: SingleProcessWp {
    /// WP for sequential step: delegate to single-process wp.
    fn wp_sequential(&mut self, ctx: &Ctx, stm: &Stm) -> Result<Vec<Stmt>, VirErr> {
        self.wp_stm(ctx, stm)  // default: delegate
    }

    /// WP for async { e }: spawn a future, extend P.
    fn wp_async(&mut self, ctx: &Ctx, body: &Stm) -> Result<Vec<Stmt>, VirErr>;

    /// WP for p.await (AU callee): switch active, run, resume.
    fn wp_await_au(&mut self, ctx: &Ctx, future: PID,
                   continuation: &Stm) -> Result<Vec<Stmt>, VirErr>;

    /// WP for p.await (AG callee): divergence.
    fn wp_await_ag(&mut self, ctx: &Ctx, future: PID) -> Result<Vec<Stmt>, VirErr>;
}
```

### sst_to_air.rs — Slimmed Down

Retains:
- `AirEmitter` struct (commands, snapshots, snap_map, etc.)
- `exp_to_expr()` — SST expression to AIR expression conversion (~700 lines)
- `typ_to_air()`, `typ_to_ids()` — type conversion helpers
- `body_stm_to_air()` — entry point that creates `WpState` and calls `wp_stm()`
- Public utility functions (`one_stmt`, `assume_var`, etc.)

Removed from this file:
- `stm_to_stmts()` (1,414 lines) → replaced by `WpState::wp_stm()`
- `State` struct → split into `WpContext` + `AirEmitter`
- Temporal helpers → moved to `wp_context.rs`
- `Proposition`, `PropositionContext`, `GoalKind` → moved to `wp_context.rs`

### AirEmitter

```rust
/// AIR statement emission bookkeeping.
pub struct AirEmitter {
    pub commands: Vec<CommandsWithContext>,
    pub snapshot_count: u32,
    pub sids: Vec<Ident>,
    pub snap_map: Vec<(Span, SnapPos)>,
    pub assign_map: AssignMap,
    pub local_shared: Vec<Decl>,
    pub local_decls_decreases_init: Stms,
    pub unwind: UnwindAir,
    pub post_condition_info: PostConditionInfo,
    pub loop_infos: Vec<LoopInfo>,
    pub static_prelude: Vec<Stmt>,
}
```

## Implementation Plan

### Phase 1: Extract wp_context.rs
- Move `Proposition`, `PropositionContext`, `GoalKind` to new file
- Move `WpContext` fields from `State` to new struct
- Move temporal helpers (`decompose_temporal`, `extract_goal_kind`, etc.)
- `sst_to_air.rs` imports from `wp_context`
- Tests must pass (no behavior change)

### Phase 2: Extract AirEmitter
- Split `State` into `WpContext` + `AirEmitter`
- `body_stm_to_air` creates both, passes to `stm_to_stmts`
- `stm_to_stmts` takes `(&mut WpContext, &mut AirEmitter)` instead of `&mut State`
- Tests must pass

### Phase 3: Define SingleProcessWp trait
- Create `wp.rs` with trait definition
- Create `WpState` struct holding `WpContext` + `AirEmitter`
- Move `stm_to_stmts` match arms to trait methods one by one
- Start with simplest: `wp_block`, `wp_assign`, `wp_assert`
- Then: `wp_if`, `wp_call`, `wp_return`
- Finally: `wp_while` (the largest, ~500 lines for loop handling)
- Tests must pass after each method extraction

### Phase 4: Define MultiProcessWp trait
- Create `wp_multi.rs` with trait + `Configuration` + `ProcessDict`
- Implement `wp_async`, `wp_await_au`, `wp_await_ag`
- Wire into the existing async/await handling
- Add multi-process tests

### Phase 5: Clean up sst_to_air.rs
- Remove dead code (old `stm_to_stmts`, old `State`)
- Update `body_stm_to_air` to use `WpState`
- Final test run

## Risks

1. **The loop handler is ~500 lines** — extracting `wp_while` requires careful handling of loop classification (AG/AU/AG-AF), temporal invariants, now-accumulators
2. **Shared mutable state** — `AirEmitter` is mutated from many places (snapshots, debug info). Need clean borrowing boundaries.
3. **exp_to_expr stays in sst_to_air.rs** — it's called from wp methods. Either pass as closure or keep as module-level function.

## Branch

All work on branch `wp-refactor` off current `main`.
