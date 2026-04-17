# Rely-Guarantee Tutorial Examples Design

## Purpose

Four tutorial examples that teach Vera's async/await rely-guarantee verification,
progressing from simple to complex. Each is a standalone `examples/*.rs` file that
verifies with `vargo run -p rust_verify -- --crate-type=lib`.

All use:
- `Executor::spawn` from `vstd::spawn`
- Inline `async requires R ensures G { body }` syntax
- Temporal operators (`ag`, `af`) in ensures clauses
- Shared mutable state (`&mut u64`) between tasks

## Example 1: `bounded_counter.rs` — Symmetric bounded increment

**Concept**: Two tasks share a counter. Each increments it. The R-G system verifies
that the counter never exceeds a limit.

**Shared state**: `*counter: u64`

**Invariant**: `ag(*counter <= 100)`

**Tasks** (symmetric):
```
Task A: requires *counter <= 100, ensures ag(*counter <= 100)
  body: loop { if *counter < 100 { *counter += 1; } }

Task B: same contract
  body: loop { if *counter < 100 { *counter += 1; } }
```

**R-G verification**:
- Pairwise: A's guarantee `ag(*counter <= 100)` implies B's rely `*counter <= 100` ✓
- Conjunction → global: `ag(*counter <= 100) ∧ ag(*counter <= 100) → ag(*counter <= 100)` ✓

**Teaches**: Basic R-G setup, symmetric tasks, shared counter.

## Example 2: `producer_consumer.rs` — Asymmetric contracts

**Concept**: A producer increments a queue length, a consumer decrements it.
Different contracts per task — the R-G system checks cross-compatibility.

**Shared state**: `*queue_len: u64`

**System ensures**: `ag(*queue_len <= 10)`

**Tasks** (asymmetric):
```
Producer: requires *queue_len <= 10, ensures ag(*queue_len <= 10)
  body: loop { if *queue_len < 10 { *queue_len += 1; } }

Consumer: requires *queue_len <= 10, ensures ag(*queue_len <= 10)
  body: loop { if *queue_len > 0 { *queue_len -= 1; } }
```

**R-G verification**:
- Producer guarantee → Consumer rely: `ag(*queue_len <= 10) → *queue_len <= 10` ✓
- Consumer guarantee → Producer rely: `ag(*queue_len <= 10) → *queue_len <= 10` ✓
- Conjunction → global ✓

**Teaches**: Different task bodies with compatible contracts, asymmetric roles.

## Example 3: `token_ring.rs` — Mutual exclusion via token

**Concept**: Two tasks pass a token. `*token == 0` means Task A holds it,
`*token == 1` means Task B holds it. Each task only modifies state when holding
the token, preserving mutual exclusion.

**Shared state**: `*token: u64`, `*data: u64`

**System ensures**: `ag(*token == 0 || *token == 1)`

**Tasks**:
```
Task A: requires *token == 0 || *token == 1
        ensures ag(*token == 0 || *token == 1)
  body: loop {
    if *token == 0 { *data = *data + 1; *token = 1; }  // work, then pass
  }

Task B: same contract
  body: loop {
    if *token == 1 { *data = *data + 1; *token = 0; }  // work, then pass
  }
```

**R-G verification**:
- Both maintain the token invariant
- Only the holder modifies `data`, so no interference

**Teaches**: Token-based mutual exclusion, asymmetric bodies with symmetric contracts.

## Example 4: `barrier.rs` — Coordination point

**Concept**: Two tasks each set an "arrived" flag, then wait for the other.
The system verifies that once both have arrived, a postcondition holds.

**Shared state**: `*phase: u64` (0=waiting, 1=a_arrived, 2=b_arrived, 3=both_arrived)

**System ensures**: `ag(*phase <= 3)`

**Tasks**:
```
Task A: requires *phase <= 3, ensures ag(*phase <= 3)
  body: loop {
    if *phase == 0 { *phase = 1; }    // A arrives
    if *phase == 2 { *phase = 3; }    // A sees B, both done
  }

Task B: requires *phase <= 3, ensures ag(*phase <= 3)
  body: loop {
    if *phase == 0 { *phase = 2; }    // B arrives
    if *phase == 1 { *phase = 3; }    // B sees A, both done
  }
```

**R-G verification**:
- Both maintain `*phase <= 3`
- Phase transitions are monotonic and non-interfering

**Teaches**: Multi-step coordination, state machine encoding, progress.

## File structure

```
examples/
  lock.rs              — existing (two-process lock)
  lock_await.rs        — existing (single-process await)
  bounded_counter.rs   — new: symmetric bounded increment
  producer_consumer.rs — new: asymmetric producer/consumer
  token_ring.rs        — new: mutual exclusion via token
  barrier.rs           — new: coordination point
```

## Constraints

- Each file is self-contained (no external dependencies beyond vstd)
- Each verifies with `--crate-type=lib`
- Each has a header comment explaining the R-G property being verified
- Loop invariants are plain state predicates (not temporal — temporal goes in ensures)
