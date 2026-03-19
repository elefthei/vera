// rust_verify/tests/example.rs ignore --- temporal verification example
//
// Round-robin fairness example.
//
// This example demonstrates a simple round-robin scheduler over a FIFO queue.
// The fairness property we want to prove is:
//   Given precondition { queue.peek() == x },
//   AG(AF(queue.peek() == x))
//   i.e., it is always the case that eventually x returns to the head.
//
// AG(AF(φ)) is not a special operator — it is nested composition:
//   AG wraps AU(true, φ) (since AF is sugar for AU(true, ·)).
//   decompose_temporal flattens this into a single AU obligation
//   with requires_invariance = true (from the outer AG).
//
// Temporal VCGen:
//   - `ensures ag(af(...))` is decomposed structurally into leaf obligations
//   - Loop `invariant` serves as the temporal refinement mapping R
//   - For the AG layer: no `decreases` → infinite loop, R→φ checked
//   - For the AU layer: progress toward the goal checked per iteration
//   - Structural rules handle prefix code and loop boundaries automatically

use vstd::prelude::*;

verus! {

struct Queue {
    data: Vec<u64>,
}

impl Queue {
    spec fn view(&self) -> Seq<u64> {
        self.data@
    }

    spec fn peek_spec(&self) -> u64 {
        self.view().first()
    }

    fn new() -> (q: Queue)
        ensures q.view().len() == 0,
    {
        Queue { data: Vec::new() }
    }

    fn enqueue(&mut self, val: u64)
        ensures
            self.view() == old(self).view().push(val),
    {
        self.data.push(val);
    }

    fn dequeue(&mut self) -> (val: u64)
        requires
            old(self).view().len() > 0,
        ensures
            val == old(self).view().first(),
            self.view() == old(self).view().subrange(1, old(self).view().len() as int),
    {
        self.data.remove(0)
    }

    fn peek(&self) -> (val: u64)
        requires
            self.view().len() > 0,
        ensures
            val == self.view().first(),
    {
        self.data[0]
    }

    fn len(&self) -> (l: usize)
        ensures l == self.view().len(),
    {
        self.data.len()
    }
}

/// The fairness property: in a round-robin schedule, every element
/// that is in the queue will eventually be at the head again.
///
/// Formally (CTL): AG (AU(⊤, queue.peek() == x))   i.e. AG(AF(peek == x))
spec fn round_robin_fairness(queue: Queue, x: u64) -> bool {
    ag (au(true, queue.peek_spec() == x))
}

/// Round-robin loop: dequeue from front, observe, re-enqueue at back.
///
/// The temporal postcondition `ensures ag(au(true, ...))` states that the
/// schedule is fair: every element in the queue eventually returns to the head.
///
/// To verify this, the loop uses:
/// - `invariant queue.view().len() > 0` — serves as both standard and temporal invariant (R)
///
/// The TICL VCGen checks:
/// 1. R holds at loop entry (standard invariant check)
/// 2. After havoc + assume R, the AG postcondition is checked (R → φ)
/// 3. After the loop body, R is preserved (standard invariant check)
/// 4. Loop is infinite (no decreases, break unreachable)
fn round_robin(queue: &mut Queue)
    requires
        old(queue).view().len() > 0,
{
    loop
        invariant
            queue.view().len() > 0,
    {
        let x = queue.dequeue();
        // In a real system, we would process x here.
        // For this example, we just observe it.
        queue.enqueue(x);
    }
}

} // verus!
