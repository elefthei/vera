// rust_verify/tests/example.rs ignore --- temporal verification example
//
// Round-robin scheduler example.
//
// This example demonstrates a simple round-robin scheduler over a FIFO queue.
// It proves the full fairness property AG(AF(now(peek == x))):
//   - AG: the loop runs forever
//   - AF(now(peek == x)): in each cycle, x eventually reaches the head
//   - now(): x at the head is a state predicate — it holds at loop-body START
//     when x is first in the queue, not at body END after x moves to back
//
// The ghost accumulator in VCGen tracks whether Q held at ANY intermediate
// state during the loop body iteration. This allows the weakened decreases
// check (now_reached ∨ m↓) to pass even when Q is false at body end.
//
// Temporal VCGen:
//   - `ensures ag(...)` is decomposed into leaf obligations
//   - Loop `invariant` serves as the temporal refinement mapping R
//   - For the AG layer: no `decreases` → infinite loop, R→φ checked
//   - For AG(AF(now(Q))): ghost accumulator tracks Q at every intermediate state
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
/// The ghost accumulator tracks whether peek == x held at any intermediate
/// state during the loop body. Combined with index_of(x) as decreasing
/// metric, this proves x always eventually reaches the front.
fn round_robin(queue: &mut Queue, Ghost(x): Ghost<u64>)
    requires
        old(queue).view().len() > 1,
        old(queue).view().contains(x),
    ensures
        ag(queue.view().len() > 0),
        ag(af(now(queue.peek_spec() == x))),
{
    loop
        invariant
            queue.view().len() > 1,
            queue.view().contains(x),
        decreases queue.view().index_of(x),
    {
        let ghost old_view = queue.view();
        let ghost old_len = old_view.len() as int;
        let ghost old_idx = old_view.index_of(x) as int;

        let val = queue.dequeue();
        queue.enqueue(val);

        let ghost new_view = queue.view();

        proof {
            // After dequeue(first) + enqueue(first): rotation by 1
            // new_view == old_view.subrange(1, old_len).push(old_view[0])
            let tail = old_view.subrange(1, old_len);

            // Prove new_view == tail.push(val)
            assert(val == old_view.first());
            assert(new_view =~= tail.push(val));

            // Prove len preserved
            assert(new_view.len() == old_len);

            // Prove contains(x) preserved:
            // Case 1: x == val (was at front)
            // Case 2: x != val (was in tail)
            if old_idx == 0 {
                // x was at front, val == x
                assert(val == x);
                // x is pushed at the end of new_view
                assert(new_view[new_view.len() - 1] == x);
            } else {
                // x was in tail at position old_idx - 1
                assert(tail.len() == old_len - 1);
                assert(tail[old_idx - 1] == x);
                // tail.push(val) contains x at same position
                assert(new_view[old_idx - 1] == x);
            }
            // In both cases: new_view.contains(x)
            assert(new_view.contains(x));
        }
    }
}

} // verus!
