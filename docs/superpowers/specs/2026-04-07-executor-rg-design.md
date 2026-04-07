# Plan: vstd Executor/Scheduler with Rely-Guarantee WP

## Design Vision

Model a tokio-like scheduler as a vstd trait with ghost state. The `Scheduler` holds the process map `P : PID → ProcessContract`. The `Executor` trait provides `spawn` (add process) and `block_on` (await termination). Rely-guarantee reasoning happens through the formal WP rules from the slides.

## vstd Types

### Executor Trait

```rust
// vstd/executor.rs

pub type PID = u64;

/// A process's contract: what it assumes (rely) and guarantees.
pub ghost struct ProcessContract {
    pub rely: spec_fn(int) -> bool,
    pub guarantee: spec_fn(int) -> bool,
}

/// The Scheduler is the process map P from the formal model.
/// It models a cooperative async runtime (like tokio).
pub ghost struct Scheduler {
    /// P : PID → ProcessContract
    pub processes: Map<PID, ProcessContract>,
    pub next_pid: PID,
}

/// Executor trait — models tokio::runtime::Handle.
/// Types implementing this can spawn and await async tasks.
pub trait Executor {
    /// Ghost view: the scheduler's process map.
    #[verifier::prophetic]
    spec fn scheduler(&self) -> Scheduler;

    /// Spawn an async task. Adds (rely, guarantee) to the process map.
    /// Returns the PID of the spawned process.
    /// Modeled as: P' = P[pid ↦ (rely, guarantee)]
    fn spawn<F: Future>(&mut self, future: F) -> (pid: Ghost<PID>)
        ensures
            self.scheduler().processes.contains_key(pid@),
            self.scheduler().processes.len() == old(self).scheduler().processes.len() + 1,
    ;

    /// Block on a future's completion (like tokio::runtime::Handle::block_on).
    /// This is the top-level await — runs the scheduler until the future completes.
    /// At this point, rely-guarantee compatibility is checked for all processes.
    fn block_on<F: Future>(&mut self, future: F) -> (ret: F::Output)
        requires
            // All pairwise rely-guarantee compatible
            self.scheduler().rely_guarantee_compatible(),
        ensures
            // The conjunction of all guarantees holds
            self.scheduler().all_guarantees_hold(ret),
    ;
}

impl Scheduler {
    /// Check pairwise rely-guarantee compatibility.
    pub open spec fn rely_guarantee_compatible(&self) -> bool {
        forall |i: PID, j: PID|
            i != j &&
            self.processes.contains_key(i) &&
            self.processes.contains_key(j) ==>
            forall |s: int|
                (self.processes[i].guarantee)(s) ==> (self.processes[j].rely)(s)
    }

    /// Check that all guarantees hold (conjunction).
    pub open spec fn all_guarantees_hold(&self, state: int) -> bool {
        forall |pid: PID|
            self.processes.contains_key(pid) ==>
            (self.processes[pid].guarantee)(state)
    }
}
```

### Connection to WP Rules (from slides.tex)

The Executor trait methods map directly to the WP rules:

**spawn = Async bind rule:**
```
WP((P, σ, i), φ) = WP((P[p ↦ e], σ, i), φ)
```
`spawn` extends P. The active process continues. No state change.

**block_on = Await AU rule + rely-guarantee check:**
```
WP((P, σ, i), φ AU φ') =
    WP((P, σ, p), φ AU done R)
    ∧ ∀x, σ'. R x σ' → WP((P[i ↦ k[x]], σ', i), φ AU φ')
```
Plus: `P.rely_guarantee_compatible()` — all pairs checked.

## Implementation Plan

### Phase A: vstd executor module
1. Replace `vstd/spawn.rs` with `vstd/executor.rs`
2. Define `PID`, `ProcessContract`, `Scheduler`, `Executor` trait
3. Add `rely_guarantee_compatible()` and `all_guarantees_hold()` spec fns

### Phase B: VCGen integration
1. In `sst_to_air.rs`, detect calls to `Executor::spawn`:
   - When `fun` path matches spawn, look up the spawned async fn
   - Extract requires → rely, temporal ensures → guarantee
   - Push to `state.wp.process_map`
   
2. Detect calls to `Executor::block_on`:
   - Emit rely-guarantee pairwise compatibility assertions
   - Apply the await bind rule for the blocked-on future
   - Emit global property assertion (conjunction of guarantees)

3. The existing `emit_rely_guarantee_checks` at function exit handles non-block_on cases.

### Phase C: Lock example
Rewrite `examples/lock.rs`:

```rust
use vstd::prelude::*;
use vstd::executor::*;

async fn incrementer(counter: &mut u32) -> (ret: ())
    requires *counter <= 100,
    ensures ag(*counter <= 100),
{ loop invariant *counter <= 100, { if *counter < 100 { *counter += 1; } } }

async fn decrementer(counter: &mut u32) -> (ret: ())
    requires *counter >= 0,
    ensures ag(*counter >= 0),
{ loop invariant *counter >= 0, { if *counter > 0 { *counter -= 1; } } }

fn system(exec: &mut impl Executor, counter: &mut u32)
    requires *counter == 50,
    ensures ag(0 <= *counter && *counter <= 100),
{
    exec.spawn(incrementer(counter));
    exec.spawn(decrementer(counter));
    // rely-guarantee checked: guarantee_inc → rely_dec AND guarantee_dec → rely_inc
}
```

### Phase D: Tests
- Rely-guarantee compatible (inc/dec with correct bounds) → PASS
- Rely-guarantee incompatible (inc goes to 200, dec relies on ≤ 100) → FAIL
- Three processes with circular rely-guarantee → PASS
- Missing guarantee → FAIL

## Key Insight

The `Scheduler` ghost struct IS the process map `P` from the slides. The `Executor` trait IS the WP layer. `spawn` = extend P, `block_on` = run and check R-G. The formal rules from the slides become executable verification conditions.
