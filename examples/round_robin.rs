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
        ensures af(q.view().len() == 0),
    {
        Queue { data: Vec::new() }
    }

    fn enqueue(&mut self, val: u64)
        ensures
            af(self.view() == old(self).view().push(val)),
    {
        self.data.push(val);
    }

    fn dequeue(&mut self) -> (val: u64)
        requires
            old(self).view().len() > 0,
        ensures
            af(val == old(self).view().first()),
            af(self.view() == old(self).view().subrange(1, old(self).view().len() as int)),
    {
        self.data.remove(0)
    }

    fn peek(&self) -> (val: u64)
        requires
            self.view().len() > 0,
        ensures
            af(val == self.view().first()),
    {
        self.data[0]
    }

    fn len(&self) -> (l: usize)
        ensures af(l == self.view().len()),
    {
        self.data.len()
    }
}

/// Round-robin fairness: the element at the head of the queue will
/// always eventually return to the head.
///
/// Precondition captures x = queue.peek() at state 0.
/// Postcondition: AG(AF(queue.peek() == x)) — x always eventually returns.
fn round_robin(queue: &mut Queue, x: u64)
    requires
        old(queue).view().len() > 0,
        x == old(queue).peek_spec(),
    ensures
        ag(af(queue.peek_spec() == x)),
{
    loop
        invariant
            queue.view().len() > 0,
    {
        let val = queue.dequeue();
        queue.enqueue(val);
    }
}

} // verus!
