// rust_verify/tests/example.rs ignore --- temporal operators not yet supported for SMT verification
//
// Round-robin fairness example.
//
// This example demonstrates a simple round-robin scheduler over a FIFO queue.
// The fairness property we want to prove is:
//   Given precondition { queue.peek() == x },
//   AG (AU(true, queue.peek() == x))   i.e. AG(AF(peek == x))
//   i.e., it is always the case that eventually x returns to the head.
//
// This requires temporal logic support (CTL operators) which is currently
// parse-only. The SMT backend for temporal verification is future work.

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
///
/// This spec function is parse-only; temporal operators are not yet
/// supported for SMT verification.
spec fn round_robin_fairness(queue: Queue, x: u64) -> bool {
    ag (au(true, queue.peek_spec() == x))
}

/// Round-robin loop: dequeue from front, observe, re-enqueue at back.
/// The postcondition expresses that the scheduler is fair.
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
