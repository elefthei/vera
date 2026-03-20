// rust_verify/tests/example.rs ignore --- temporal verification example
//
// Queue drain example.
//
// This example demonstrates proving that draining a queue eventually empties it.
// The liveness property is:
//   AF(queue.is_empty())   i.e.  AU(⊤, queue.len() == 0)
//   "eventually, the queue will be empty"
//
// Since AF is equivalent to standard termination + postcondition for sequential
// programs, this is also provable with plain `ensures q.view().len() == 0`.
// The `af(...)` syntax makes the temporal intent explicit.
//
// Temporal VCGen:
//   - `ensures af(...)` declares the temporal postcondition (sugar for au(true, ...))
//   - Loop `invariant` serves as the temporal refinement mapping R
//   - `decreases q.view().len()` provides the well-founded metric for AU progress
//   - TICL structural rules (aul_cprog_while) decompose this into:
//     * R established at loop entry
//     * R preserved by loop body
//     * decreases weakened to ψ ∨ (m decreased) — either the queue is empty
//       or the queue length strictly decreased

use vstd::prelude::*;

verus! {

struct Queue {
    data: Vec<u64>,
}

impl Queue {
    spec fn view(&self) -> Seq<u64> {
        self.data@
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

    fn len(&self) -> (l: usize)
        ensures af(l == self.view().len()),
    {
        self.data.len()
    }

    fn is_empty(&self) -> (b: bool)
        ensures af(b == (self.view().len() == 0)),
    {
        self.data.len() == 0
    }
}

/// Drain every element from the queue.
///
/// The temporal postcondition `ensures af(q.view().len() == 0)` states that
/// the queue will eventually be empty — a liveness / progress property.
///
/// AF(φ) desugars to AU(⊤, φ): "true holds until φ is reached."
/// The `decreases q.view().len()` clause proves progress: the queue length
/// strictly decreases on each iteration (or the goal is already reached).
fn drain(q: &mut Queue)
    requires
        old(q).view().len() > 0,
    ensures
        af(q.view().len() == 0),
{
    while q.len() > 0
        invariant
            q.view().len() >= 0,
        decreases
            q.view().len(),
    {
        let _ = q.dequeue();
    }
}

} // verus!
