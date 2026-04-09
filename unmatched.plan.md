# Unmatched Temporal Proposition Pairs

## Goal
Handle all combinations of (caller temporal, callee temporal) in `emit_temporal_implication_check`, not just (Always, Always) and (Until, Until).

## Why
Currently, when the caller has `Always` (AG) and the callee has `Until` (AU/AF), or vice versa, the match falls through to `_ => {}` — no check emitted. This is semantically meaningful:

- **Caller AG, Callee AU/AF**: The callee terminates. The caller's AG continues after the call via existing prefix/state assertions. No implication needed — but should the caller's AG check that the callee's ensures don't violate it?
- **Caller AU/AF, Callee AG**: The callee diverges. The caller's AU goal can never be reached through this call. Should this be an error? A warning?

## Current State
```rust
match (caller_prop, callee_prop) {
    (Always, Always) => { /* emit assertion, set ag_discharged */ }
    (Until, Until) if both requires_invariance => { /* emit assertion, set ag_discharged */ }
    _ => {} // SILENT — no check
}
```

## Design Questions (need answers before implementing)

### Q1: Caller AG + Callee AF
```rust
fn callee() ensures af(done(*x == 0)) { *x = 0; }
fn caller() ensures ag(*x <= 10) {
    loop invariant *x <= 10 {
        callee();  // callee sets *x = 0, which satisfies *x <= 10
    }
}
```
This already works via the bind rule (callee's `done(*x == 0)` is assumed, AG check fires after). **No action needed.**

### Q2: Caller AF + Callee AG
```rust
fn callee() ensures ag(*x > 0) { loop { ... } }
fn caller() ensures af(done(*x == 10)) {
    callee();  // callee NEVER RETURNS — AF goal unreachable
}
```
Should this be rejected? The caller claims eventual termination (`af`) but calls a diverging function (`ag`). **Options:**
- **Error**: "calling a diverging function (AG ensures) prevents reaching the AF goal"
- **Warning**: informational only
- **Silent**: let the AF decreases check catch it (it will fail because no progress)

**Recommendation:** Silent — the existing AF/AU decreases checking will reject this because the callee diverges and the metric can't decrease. Adding an explicit error gives a better message but isn't strictly needed.

### Q3: Caller AG + Callee AG with different properties
Already handled — the `(Always, Always)` match arm emits an implication assertion.

### Q4: Mixed nested
```rust
fn callee() ensures ag(af(now(Q))) { ... }  // Decomposes to Until(requires_invariance=true)
fn caller() ensures ag(P) { ... }          // Decomposes to Always
```
Caller Always, callee Until(invariance=true) — currently falls through. **Should emit assertion**: callee's temporal property is AG-based (requires_invariance), and caller has AG. The callee's inner AF goal Q should imply the caller's P at the intermediate states where Q holds.

This is the trickiest case and may need a new match arm.

## Proposed Changes

### Change 1: Error for AF caller + AG callee
In `emit_temporal_implication_check`, add:
```rust
(Proposition::Until { requires_invariance: false, .. },
 Proposition::Always { .. }) => {
    // Callee diverges (AG), caller expects termination (AU/AF).
    // The AU goal is unreachable through this call.
    // Not an error per se — the decreases check will catch it.
    // But we could emit a helpful warning.
}
```
**Decision:** skip (decreases check handles it)

### Change 2: Assert for AG caller + AG(AF) callee
```rust
(Proposition::Always { property: caller_phi, .. },
 Proposition::Until { goal: callee_goal, requires_invariance: true, .. }) => {
    // Callee has AG(AF(goal)). Caller has AG(phi).
    // The callee's goal should imply caller's phi at the intermediate state.
    let callee_g = exp_to_expr(ctx, callee_goal, expr_ctxt)?;
    let phi = exp_to_expr(ctx, caller_phi, expr_ctxt)?;
    let implication = mk_implies(&callee_g, &phi);
    stmts.push(Assert(implication, "callee's AG(AF) goal must imply caller's AG property"));
    ag_discharged = true;
}
```

### Change 3: Assert for AG(AF) caller + AG callee
```rust
(Proposition::Until { requires_invariance: true, .. },
 Proposition::Always { property: callee_psi, .. }) => {
    // Callee has pure AG(psi). Caller has AG(AF(goal)).
    // Callee diverges maintaining psi — discharges caller's AG.
    // Check: psi implies caller's AG(AF) is satisfied.
    ag_discharged = true;  // Callee's AG is stronger than AG(AF)
}
```

## Estimated Effort
2-3 hours including tests. The design questions above should be answered first.

## Dependencies
None — this is independent of other features.
