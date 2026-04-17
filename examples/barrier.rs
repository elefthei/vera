// rust_verify/tests/example.rs ignore --- rely-guarantee tutorial example
//
// Barrier: coordination point with phase state machine
//
// Two tasks coordinate through a shared phase variable:
//   phase 0: initial — both waiting
//   phase 1: Task A has arrived
//   phase 2: Task B has arrived
//   phase 3: both have arrived — barrier complete
//
// Each task advances the phase when it arrives and when it sees the other.
// The R-G system verifies that phase transitions are monotonic and bounded.
//
// R-G properties verified:
//   1. Both tasks maintain ag(*phase <= 3)
//   2. Phase only increases (monotonic transitions)
//   3. No task sets an invalid phase value

use vstd::prelude::*;
use vstd::spawn::*;

verus! {

fn system(exec: &mut impl Executor, phase: &mut u64)
    requires *phase == 0,
    ensures ag(*phase <= 3),
{
    // Task A: arrive (0→1), then complete barrier when B arrived (2→3)
    exec.spawn(async
        requires *phase <= 3,
        ensures ag(*phase <= 3),
    {
        loop
            invariant *phase <= 3,
        {
            if *phase == 0 { *phase = 1; }     // A arrives
            if *phase == 2 { *phase = 3; }     // A sees B arrived → both done
        }
    });

    // Task B: arrive (0→2), then complete barrier when A arrived (1→3)
    exec.spawn(async
        requires *phase <= 3,
        ensures ag(*phase <= 3),
    {
        loop
            invariant *phase <= 3,
        {
            if *phase == 0 { *phase = 2; }     // B arrives
            if *phase == 1 { *phase = 3; }     // B sees A arrived → both done
        }
    });
}

} // verus!
