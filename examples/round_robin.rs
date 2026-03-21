// rust_verify/tests/example.rs ignore --- temporal verification example
//
// Round-robin scheduler example.
//
// This example demonstrates a simple round-robin scheduler over a FIFO queue.
// The AG property proven: the queue is always non-empty (AG(len > 0)).
//
// TODO: The full fairness property AG(AF(queue.peek() == x)) requires
// a VCGen that checks the AF goal at the START of each loop iteration
// (where Q holds when x is at the front), not at the END (where x has
// been moved to the back). See the TODO in round_robin() for details.
//
// Temporal VCGen:
//   - `ensures ag(...)` is decomposed into leaf obligations
//   - Loop `invariant` serves as the temporal refinement mapping R
//   - For the AG layer: no `decreases` → infinite loop, R→φ checked
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
        ensures af(done(q.view().len() == 0)),
    {
        Queue { data: Vec::new() }
    }

    fn enqueue(&mut self, val: u64)
        ensures
            af(done(self.view() == old(self).view().push(val))),
    {
        self.data.push(val);
    }

    fn dequeue(&mut self) -> (val: u64)
        requires
            old(self).view().len() > 0,
        ensures
            af(done(val == old(self).view().first())),
            af(done(self.view() == old(self).view().subrange(1, old(self).view().len() as int))),
    {
        self.data.remove(0)
    }

    fn peek(&self) -> (val: u64)
        requires
            self.view().len() > 0,
        ensures
            af(done(val == self.view().first())),
    {
        self.data[0]
    }

    fn len(&self) -> (l: usize)
        ensures af(done(l == self.view().len())),
    {
        self.data.len()
    }
}

/// Round-robin scheduler: continuously dequeue and re-enqueue elements.
///
/// Maintains AG invariant: the queue always has at least one element.
/// Note: requires at least 2 elements so that after dequeue (intermediate
/// state), the queue still has >= 1 element, satisfying AG at all states.
///
/// TODO: The full fairness property AG(AF(queue.peek_spec() == x)) requires
/// a more sophisticated VCGen that checks the AF goal at loop-body START
/// (where Q holds when x is at the front) rather than at loop-body END
/// (where x has been moved to the back). The current weakened decreases
/// check (Q_end ∨ m↓) is too strong for cyclic progress patterns.
fn round_robin(queue: &mut Queue)
    requires
        old(queue).view().len() > 1,
    ensures
        ag(queue.view().len() > 0),
{
    loop
        invariant
            queue.view().len() > 1,
    {
        let val = queue.dequeue();
        queue.enqueue(val);
    }
}

} // verus!
