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
/// Round-robin fairness proof: AG(AF(now(peek == x)))
///
/// Invariant R: queue is non-empty AND x is either at the head or
///   somewhere in the tail (with a known position via index_of).
///
/// Measure f: index_of(x) in the queue.
///   - When x is NOT at head: index decreases each rotation (progress)
///   - When x IS at head: now(peek == x) holds (AF satisfied immediately)
///
/// The AG rule splits each iteration into two cases:
///   LEFT (h = x): AF(now(peek == x)) holds now — accumulator captures it
///   RIGHT (h ≠ x): index_of(x) decreases — progress toward future satisfaction
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
        decreases ({
            // Use index_of_first for deterministic first-occurrence position
            match queue.view().index_of_first(x) {
                Some(i) => i,
                None => 0int, // unreachable: invariant guarantees contains(x)
            }
        }),
    {
        let ghost old_view = queue.view();
        let ghost old_len = old_view.len() as int;
        proof { old_view.index_of_first_ensures(x); }
        let ghost old_idx = old_view.index_of_first(x).unwrap();

        let val = queue.dequeue();
        queue.enqueue(val);

        proof {
            let tail = old_view.subrange(1, old_len);
            let new_view = tail.push(val);

            assert(queue.view() =~= new_view);
            assert(val == old_view.first());

            // Prove contains(x) preserved
            if old_idx == 0 {
                assert(val == x);
                assert(new_view[new_view.len() - 1] == x);
            } else {
                assert(tail[old_idx - 1] == x);
                assert(new_view[old_idx - 1] == x);
            }
            assert(new_view.contains(x));

            // Prove decreases: index_of_first(x) decreased
            if old_idx > 0 {
                // x was NOT at front, at position old_idx
                // In new_view, x is at position old_idx - 1
                assert(new_view[old_idx - 1] == x);
                // Use index_of_first lemma to bound the first occurrence
                new_view.index_of_first_ensures(x);
                // index_of_first returns first i where new_view[i] == x
                // Since new_view[old_idx - 1] == x, first index <= old_idx - 1
                // Therefore index_of_first(x) < old_idx (strict decrease)
            }
        }
    }
}

} // verus!
