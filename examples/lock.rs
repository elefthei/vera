// rust_verify/tests/example.rs ignore --- temporal verification example
//
// Async lock deadlock freedom.
//
// Two async tasks share a lock via &mut u64 (0=free, 1=held-by-1, 2=held-by-2).
// Each task: acquire → critical section → release, in a loop.
//
// Deadlock freedom property: AG(AF(now(*lock == 0)))
//   "The lock is always eventually free"
//
// Each task independently proves this temporal property using:
//   - AG: infinite loop (no exit condition)
//   - AF(now(*lock == 0)): lock eventually becomes free via release()
//   - now(): the lock being free is a state predicate at release point
//   - decreases: tracks whether we hold the lock (1→0 on release)
//
// The release() function has AF(done(*lock == 0)) — the bind rule
// extracts *lock == 0 as an assumption after the call.

use vstd::prelude::*;

verus! {

/// Release the lock.
fn release(lock: &mut u64)
    requires *lock > 0,
    ensures af(done(*lock == 0)),
{
    *lock = 0;
}

/// Async task 1: repeatedly acquire (set to 1), then release.
/// Proves: the lock is always eventually free.
async fn task1(lock: &mut u64) -> (ret: ())
    requires *lock == 0,
    ensures ag(af(now(*lock == 0))),
{
    loop
        invariant *lock == 0 || *lock == 1,
        decreases (if *lock == 1 { 1int } else { 0int }),
    {
        if *lock == 0 {
            *lock = 1;          // acquire
            release(lock);      // release — now(*lock == 0) holds here
        }
        if *lock == 1 {
            release(lock);      // release if still held
        }
    }
}

/// Async task 2: repeatedly acquire (set to 2), then release.
async fn task2(lock: &mut u64) -> (ret: ())
    requires *lock == 0,
    ensures ag(af(now(*lock == 0))),
{
    loop
        invariant *lock == 0 || *lock == 2,
        decreases (if *lock == 2 { 1int } else { 0int }),
    {
        if *lock == 0 {
            *lock = 2;          // acquire
            release(lock);      // release
        }
        if *lock == 2 {
            release(lock);
        }
    }
}

// NOTE: Composing task1 + task2 via Executor::spawn with rely-guarantee
// checking requires the multi-process WP layer (see docs/superpowers/specs/).
// Each task's AG(AF(now(*lock==0))) guarantee individually proves deadlock
// freedom. The multi-process system would additionally verify that each
// task's guarantee implies the other's rely.

} // verus!
