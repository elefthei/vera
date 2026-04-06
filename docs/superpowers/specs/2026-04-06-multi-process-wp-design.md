# Multi-Process Weakest Preconditions for Async Rust

**Date**: 2026-04-06
**Status**: Design approved, pending implementation

## Summary

Extend Vera's wp calculus with a two-layer design:
1. **`wp(t, φ)`** — single-process weakest precondition over a Rust term and shared state (unchanged)
2. **`WP(C, φ)`** — multi-process weakest precondition over a configuration of concurrent futures

## Motivation

The single-process judgment `[t, σ ⊩ φ]` doesn't account for async/await's multi-process nature. The `P[p]` notation in await rules implicitly assumes a process dictionary. Making this explicit enables reasoning about cooperative scheduling and temporal properties across await boundaries.

## Decisions

| Decision | Choice |
|----------|--------|
| Process model | Flat dictionary: `P : PID → Term` |
| Scheduler | Cooperative (run until await, then switch) |
| State model | Shared state σ (heap/mutable refs), no per-process state |
| Rule complexity | Minimal: two-layer wp/WP, most rules unchanged |
| Temporal formulas | Over shared state σ, not per-process |

## Model

### Configuration

A configuration `C = (P, σ, i)` consists of:
- `P : PID → Term` — process dictionary mapping PIDs to Rust terms
- `σ` — shared mutable state (heap, &mut references)
- `i : PID` — the currently active (scheduled) process

### Layer 1: Single-Process wp(t, φ)

Exactly as defined previously. Operates on a single Rust term `t` and state `σ`. Returns `λσ. ...` (state predicate). Covers:
- Assignment, let-binding, conditional, while (AU and AG)
- Sync function calls

No knowledge of P or process scheduling. This is the standard sequential wp.

### Layer 2: Multi-Process WP(C, φ)

Operates on a configuration `C = (P, σ, i)`. Defined by cases on the shape of `P(i)` (the active process's current term):

#### Sequential step
When `P(i)` is a non-async construct (assignment, let, if, while, sync call):

```
WP((P, σ, i), φ) = wp(P(i), φ) σ
```

Delegate to single-process wp. P is unchanged.

#### Async bind
When `P(i) = let p = async f(ē); k`:

```
WP((P, σ, i), Φ) = WP((P[i ↦ k, p ↦ f_body], σ, i), Φ)
```

Creates a new process `p` with body `f_body` in P. Replaces the active process's term with the continuation `k`. The new process is suspended (not active). No state change.

#### Await
When `P(i) = let x = p.await; k`:

```
WP((P, σ, i), φ AU φ') = WP((P, σ, p), φ AU done R)
                         ∧ ∀x, σ'. R x σ' → WP((P[i ↦ k[x]], σ', i), φ AU φ')
```

Switch active process to `p`. Run `p` maintaining path property `φ` until it terminates with `done R`. After `p` finishes with result `x` and state `σ'`, resume process `i` with continuation `k[x]`.

#### Await (AG callee)
When `P(i) = p.await` and `P(p)` satisfies `AG(ψ)`:

```
WP((P, σ, i), AG(φ)) = WP((P, σ, p), AG(ψ)) ∧ (ψ ⟹ φ)
```

Process `p` runs forever. The await diverges. Caller's AG(φ) is satisfied if callee's AG(ψ) implies it.

## Relationship Between Layers

- `wp` is self-contained and usable without `WP`
- `WP` delegates to `wp` for sequential constructs
- Only `async` and `await` require the multi-process layer
- Programs without async/await: `WP((P, σ, 0), φ) = wp(P(0), φ) σ` (reduces to single-process)

## Slide Structure

1. Keep existing "Inference Rules" section (single-process) unchanged
2. Keep existing "Weakest Preconditions" section (single-process wp) unchanged  
3. Add new section: "Multi-Process Configuration" — define C = (P, σ, i)
4. Add new section: "Multi-Process WP" — define WP(C, φ) rules for async bind and await
5. Move async bind / await from inference rules section to multi-process section
