# Multi-Process Async Rely-Guarantee Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox syntax for tracking.

**Goal:** Enable rely-guarantee temporal verification across async processes by wiring Executor::spawn into the VCGen and detecting spawned functions' requires (rely) and temporal ensures (guarantee).

**Architecture:** Detect Executor::spawn calls in the VCGen by path matching. Extract the spawned async function's requires (rely) and temporal ensures (guarantee) from ctx.func_sst_map. Add to WpContext.process_map. Pairwise rely-guarantee checks fire at function exit via existing emit_rely_guarantee_checks. Async blocks with specs deferred to future work — use async fn (which already supports requires/ensures) as the primary spawning pattern.

**Tech Stack:** Verus VIR/SST/AIR pipeline, Z3 via AIR

---

## Key Insight

No new AST node needed. The spawning pattern is:
```rust
exec.spawn(my_async_fn(args));  // my_async_fn has requires/ensures
```
The VCGen detects spawn by path, looks up my_async_fn in func_sst_map, extracts requires (rely) and temporal ensures (guarantee). The existing process_map and emit_rely_guarantee_checks handle the rest.

## Dependency Graph

```
Task 1 (spawn detection) → Task 2 (process map population) → Task 3 (tests)
```

All tasks are sequential. No parallelism needed — this is a focused 3-task plan.

---

### Task 1: Detect Executor::spawn in VCGen

**Files:**
- Modify: `source/vir/src/sst_to_air.rs:2237`

- [ ] **Step 1: Add spawn detection helper**

In `source/vir/src/sst_to_air.rs`, before `stm_to_stmts_inner`, add:

```rust
/// Check if a function call is to Executor::spawn.
fn is_executor_spawn(fun: &Fun) -> bool {
    let s = fun_to_string(fun);
    s.contains("spawn") && s.contains("Executor")
}
```

- [ ] **Step 2: Build to verify it compiles**

Run: `cd source && source ../tools/activate && vargo build --vstd-no-verify 2>&1 | tail -3`
Expected: Build succeeds.

- [ ] **Step 3: Commit**

```bash
git add source/vir/src/sst_to_air.rs
git commit -m "VCGen: add is_executor_spawn helper for spawn detection"
```

---

### Task 2: Populate Process Map at Spawn Sites

**Files:**
- Modify: `source/vir/src/sst_to_air.rs:2590` (after emit_temporal_implication_check in StmX::Call)

- [ ] **Step 1: Add spawn handling in StmX::Call**

In the `StmX::Call` handler, after the line:
```rust
result.extend(emit_temporal_implication_check(ctx, state, &stm.span, expr_ctxt, func)?);
```

Add:

```rust
            // Multi-process: detect Executor::spawn, extract rely/guarantee
            if is_executor_spawn(fun) {
                // The spawned future's creating function is in args.
                // Walk args to find a Call expression → look up that function's specs.
                for arg in args.iter() {
                    if let ExpX::Call(CallFun::Fun(callee_fun, _), _, _) = &arg.x {
                        if let Some(callee_sst) = ctx.func_sst_map.get(callee_fun) {
                            // requires = rely, temporal ensures = guarantee
                            if let (Some(rely), Some(guarantee)) = (
                                callee_sst.x.decl.reqs.first().cloned(),
                                callee_sst.x.decl.enss.0.first().cloned(),
                            ) {
                                state.wp.process_map.push((rely, guarantee));
                            }
                        }
                    }
                }
            }
```

- [ ] **Step 2: Build and run existing tests**

Run: `cd source && source ../tools/activate && vargo build --vstd-no-verify 2>&1 | tail -3`
Expected: Build succeeds.

Run: `vargo test -p rust_verify_test --test temporal 2>&1 | tail -3 && vargo test -p rust_verify_test --test async_functions 2>&1 | tail -3`
Expected: All 156 tests pass (no behavior change — no existing tests use Executor::spawn).

- [ ] **Step 3: Commit**

```bash
git add source/vir/src/sst_to_air.rs
git commit -m "VCGen: detect spawn, extract rely/guarantee from spawned async fn specs"
```

---

### Task 3: Multi-Process Tests + Lock Example

**Files:**
- Modify: `source/rust_verify_test/tests/async_functions.rs`
- Modify: `examples/lock.rs`

- [ ] **Step 1: Write positive test — two compatible async tasks**

Append to `source/rust_verify_test/tests/async_functions.rs`:

```rust
// Multi-process: two async tasks with compatible rely-guarantee
test_verify_one_file! {
    #[test] test_multiprocess_rg_compatible verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        async fn task_a(x: &mut u64) -> (ret: ())
            requires *x <= 100,
            ensures ag(*x <= 100),
        {
            loop invariant *x <= 100, {
                if *x < 100 { *x = *x + 1; }
                else { *x = 0; }
            }
        }

        async fn task_b(x: &mut u64) -> (ret: ())
            requires *x <= 100,
            ensures ag(*x <= 100),
        {
            loop invariant *x <= 100, {
                if *x > 0 { *x = *x - 1; }
            }
        }

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x == 50,
        {
            exec.spawn(task_a(x));
            exec.spawn(task_b(x));
        }
    } => Ok(())
}
```

- [ ] **Step 2: Write negative test — incompatible rely-guarantee**

```rust
// Multi-process: incompatible rely-guarantee — should FAIL
test_verify_one_file! {
    #[test] test_multiprocess_rg_incompatible verus_code! {
        use vstd::prelude::*;
        use vstd::spawn::*;

        async fn task_wide(x: &mut u64) -> (ret: ())
            requires *x <= 200,
            ensures ag(*x <= 200),
        {
            loop invariant *x <= 200, {
                if *x < 200 { *x = *x + 1; }
                else { *x = 0; }
            }
        }

        async fn task_narrow(x: &mut u64) -> (ret: ())
            requires *x <= 50,
            ensures ag(*x <= 50),
        {
            loop invariant *x <= 50, {
                if *x > 0 { *x = *x - 1; }
            }
        }

        fn system(exec: &mut impl Executor, x: &mut u64)
            requires *x == 0,
        {
            exec.spawn(task_wide(x));
            exec.spawn(task_narrow(x));
            // guarantee_wide (x<=200) does NOT imply rely_narrow (x<=50) → FAIL
        }
    } => Err(_err) => ()
}
```

- [ ] **Step 3: Update examples/lock.rs with Executor::spawn**

```rust
use vstd::prelude::*;
use vstd::spawn::*;

verus! {

async fn task1(lock: &mut u64) -> (ret: ())
    requires *lock <= 2,
    ensures ag(af(now(*lock == 0))),
{
    loop
        invariant *lock == 0 || *lock == 1,
        decreases (if *lock == 1 { 1int } else { 0int }),
    {
        if *lock == 0 { *lock = 1; *lock = 0; }
        if *lock == 1 { *lock = 0; }
    }
}

async fn task2(lock: &mut u64) -> (ret: ())
    requires *lock <= 2,
    ensures ag(af(now(*lock == 0))),
{
    loop
        invariant *lock == 0 || *lock == 2,
        decreases (if *lock == 2 { 1int } else { 0int }),
    {
        if *lock == 0 { *lock = 2; *lock = 0; }
        if *lock == 2 { *lock = 0; }
    }
}

fn system(exec: &mut impl Executor, lock: &mut u64)
    requires *lock == 0,
{
    exec.spawn(task1(lock));
    exec.spawn(task2(lock));
    // R-G: guarantee_1 (lock always eventually 0) → rely_2 (lock <= 2) ✓
    // R-G: guarantee_2 (lock always eventually 0) → rely_1 (lock <= 2) ✓
}

} // verus!
```

- [ ] **Step 4: Run multi-process tests**

Run: `cd source && source ../tools/activate && vargo test -p rust_verify_test --test async_functions -- test_multiprocess 2>&1 | tail -10`
Expected: Both tests pass.

- [ ] **Step 5: Verify lock example**

Run: `cd source && source ../tools/activate && vargo run -p rust_verify -- --crate-type=lib ../examples/lock.rs 2>&1 | tail -3`
Expected: `verification results:: N verified, 0 errors`

- [ ] **Step 6: Run full test suite**

Run: `vargo test -p rust_verify_test --test temporal 2>&1 | tail -3 && vargo test -p rust_verify_test --test async_functions 2>&1 | tail -3`
Expected: All tests pass.

- [ ] **Step 7: Commit**

```bash
git add source/rust_verify_test/tests/async_functions.rs examples/lock.rs
git commit -m "Tests: multi-process rely-guarantee pass/fail + async lock with Executor::spawn"
```

---

## Future Work (not in this plan)

- **Annotated async blocks**: `async requires R ensures G { body }` syntax extension in builtin_macros. Deferred because async fn already supports requires/ensures and is the primary spawning pattern.
- **block_on verification**: Currently block_on is external_body. Wire it into VCGen to verify the blocked-on future's temporal properties.
- **Global property composition**: Assert conjunction of all guarantees implies function's temporal ensures.
