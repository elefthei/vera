# Multi-Process WP Formal Model

## Goal
Wire the formal multi-process WP model (`wp_multi.rs`) into the VCGen, enabling compositional verification of multiple async processes via the `Executor` trait.

## Why
Currently, individual async tasks verify their temporal properties independently. The rely-guarantee infrastructure (`process_map`, `emit_rely_guarantee_checks`) exists but only checks pairwise compatibility. The full multi-process WP from the slides enables:

1. **System-level ensures**: `fn system(exec) ensures ag(global_property)` verified from composed process guarantees
2. **Await-AU delegation**: `p.await` transfers the process's AU postcondition to the caller
3. **Configuration stepping**: The formal `WP((P, σ, i), φ)` model where P is the process dictionary

## Current State
- `wp_multi.rs`: defines `PID`, `ProcessDict`, `Configuration`, `MultiProcessWp` trait — **NOT wired into VCGen**
- `WpContext.process_map`: populated from `spawned_funs` — **works**
- `emit_rely_guarantee_checks`: pairwise G_i → R_j checks — **works but only fires when caller has temporal context**
- `SingleProcessWp` trait: implemented on `State` — **works**

## Implementation Plan

### Phase 1: Make R-G checks independent of caller's temporal context
Currently `emit_rely_guarantee_checks` only fires at function exit and only when there's a temporal context. It should fire whenever `process_map.len() >= 1` regardless of whether the caller has `ensures ag(...)`.

**File:** `sst_to_air.rs`, `body_stm_to_air` function (~line 3990)
**Change:** Move the R-G check call outside the temporal context block. Call it unconditionally when `spawned_funs` is non-empty.

### Phase 2: System-level ensures composition
When a function spawns processes and has temporal ensures, verify:
```
(G_1 ∧ G_2 ∧ ... ∧ G_n) → global_ensures
```
The conjunction of all process guarantees must imply the function's temporal postcondition.

**File:** `sst_to_air.rs`, after R-G pairwise checks
**Change:** Add a conjunction-implies-global assertion.

### Phase 3: Wire MultiProcessWp trait
Replace the ad-hoc spawn detection with proper `MultiProcessWp` trait dispatch:
- When `Executor::spawn` is detected, call `wp_async` (extend P)
- When `.await` is detected on a spawned future, call `wp_await_au` or `wp_await_ag`
- The `Configuration` struct tracks active process

**File:** `wp_multi.rs` → implement trait on `State`, `sst_to_air.rs` → dispatch through trait
**Effort:** Large — requires rethinking how the VCGen processes async function bodies

### Phase 4: block_on verification
`Executor::block_on(future)` runs the scheduler to completion. At this point:
- All R-G pairwise checks fire
- The global property is verified
- The blocked-on future's postcondition is available to the caller

**File:** `sst_to_air.rs` StmX::Call handler
**Change:** Detect `block_on` calls and emit comprehensive R-G + global checks

## Architecture

```
Current:                          Target:
  spawned_funs → process_map        MultiProcessWp trait
  emit_rely_guarantee_checks()      wp_async() → extend P
  (ad-hoc, fire at exit)           wp_await_au() → switch active
                                    wp_await_ag() → diverge
                                    Configuration { P, active }
```

## Estimated Effort
- Phase 1: 1 hour
- Phase 2: 2-3 hours
- Phase 3: 1-2 days (architectural)
- Phase 4: 1 day

Total: ~1 week

## Dependencies
- Tier 1 soundness fixes: recommended first (nested now/done, spec fn temporal)
- Executor R-G end-to-end (Tier 2 items 4-5): should be done as part of Phase 1-2
