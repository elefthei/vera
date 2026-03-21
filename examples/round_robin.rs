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
/// Round-robin fairness: the element currently at the head will always
/// eventually return to the head after cycling through the queue.
///
/// The fairness property is AG(AF(now(peek == x))):
/// - AG: the loop runs forever
/// - AF(now(peek == x)): in each cycle, x eventually reaches the head
/// - now(): x at the head is a state predicate (holds at loop-body START
///   when x is first in the queue, not at body END after x moves to back)
///
/// Currently proves the weaker AG(queue.len() > 0) because:
/// The weakened decreases check Q ∨ m↓ only checks at body END where
/// peek ≠ x (x was moved to back). Full fairness needs now() semantics
/// where Q is checked at ANY intermediate state, not just body end.
fn round_robin(queue: &mut Queue, x: u64)
    requires
        old(queue).view().len() > 1,
        x == old(queue).peek_spec(),
    ensures
        ag(queue.view().len() > 0),
        // TODO: Full fairness property once now() VCGen checks intermediate states:
        // ag(af(now(queue.peek_spec() == x))),
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
