# <a href="https://verus-lang.github.io/verus/verus/logo.html"><img height="60px" src="https://verus-lang.github.io/verus/verus/assets/verus-color.svg" alt="Verus" /></a> Vera (Verus Always)

**Vera** extends [Verus](https://github.com/verus-lang/verus) with **CTL temporal logic**
to prove **liveness** and **fairness** properties of Rust programs at compile time.

While Verus proves *safety* (something bad never happens), Vera adds the ability to prove
*liveness* (something good eventually happens) — including **always-eventually** (fairness)
properties for infinite-running systems like schedulers, servers, and event loops.

Vera is built on the [TICL](https://github.com/eioannidis/ticl) framework, which provides
sound structural rules for decomposing CTL temporal obligations into standard first-order
verification conditions checked by Z3.

## Temporal Operators

| Operator | Meaning |
|----------|---------|
| `ag(φ)` | **Always globally**: φ holds at every state of an infinite computation |
| `af(φ)` | **Always finally**: φ is eventually reached (sugar for `au(true, φ)`) |
| `au(φ, ψ)` | **Always until**: φ holds at every state until ψ is reached |

Operators compose structurally — `ag(af(φ))`, `au(φ, ag(ψ))`, `ag(ag(φ))`, etc. all
work via recursive decomposition into leaf obligations. For example, `ag(af(φ))` is just
`AG` wrapping `AU(⊤, φ)`: the outer AG requires an infinite loop with invariance, the
inner AU requires progress toward φ on each iteration.

## How It Works

Temporal postconditions in `ensures` clauses are decomposed into standard first-order
verification conditions using TICL structural rules:

- **`ensures ag(φ)`** — the function must contain an infinite loop (`loop` without `decreases`)
  whose invariant R implies φ. The loop may never exit.
- **`ensures af(φ)`** — equivalent to standard termination + postcondition for sequential code.
  The loop needs a `decreases` clause proving progress toward φ.
- **`ensures au(φ, ψ)`** — path property φ holds until goal ψ is reached. Requires `decreases`
  weakened to ψ ∨ (measure decreased).
- **Prefix code** (assignments, calls before the temporal loop) must maintain φ at every step
  (sequence composition rules: `ag_seq`, `aul_seq`).

The key insight: `{P} prog {Q}` in Verus Hoare logic corresponds to `{P} prog {AF(done ∧ Q)}`
in temporal logic. Standard `ensures` + `decreases` already proves `AF(Q)` — temporal operators
add genuinely new capabilities for infinite computations (`AG`) and fairness (`AG(AF)`).

## Example: Round-Robin Fairness

A round-robin scheduler dequeues from the front and re-enqueues at the back.
The fairness property: every element eventually returns to the head.

```rust
use vstd::prelude::*;

verus! {

struct Queue {
    data: Vec<u64>,
}

impl Queue {
    spec fn view(&self) -> Seq<u64> { self.data@ }
    spec fn peek_spec(&self) -> u64  { self.view().first() }

    fn new() -> (q: Queue)
        ensures q.view().len() == 0,
    { Queue { data: Vec::new() } }

    fn enqueue(&mut self, val: u64)
        ensures self.view() == old(self).view().push(val),
    { self.data.push(val); }

    fn dequeue(&mut self) -> (val: u64)
        requires old(self).view().len() > 0,
        ensures
            val == old(self).view().first(),
            self.view() == old(self).view().subrange(1, old(self).view().len() as int),
    { self.data.remove(0) }
}

/// Round-robin loop: AG(AF(peek == x)) fairness postcondition.
/// The loop invariant serves as the temporal refinement mapping R.
/// No `decreases` → AG (infinite loop). R → φ is checked automatically.
fn round_robin(queue: &mut Queue)
    requires old(queue).view().len() > 0,
{
    loop
        invariant queue.view().len() > 0,
    {
        let x = queue.dequeue();
        queue.enqueue(x);
    }
}

} // verus!
```

See also [`examples/drain.rs`](examples/drain.rs) for an `AF` (progress/termination) proof.

## Building

Vera requires a **forked `syn`** crate (vendored in `dependencies/syn/` as `verus_syn`)
that adds temporal keyword parsing. Everything is checked into this branch — no extra
setup beyond Z3.

```sh
# 1. Get Z3
./tools/get-z3.sh           # downloads Z3 4.12.5, sets VERUS_Z3_PATH

# 2. Build (from source/ directory)
cd source
source ../tools/activate     # sets up vargo (cargo wrapper for Verus)
vargo build --vstd-no-verify # fast build, skips vstd SMT verification

# 3. Run examples
./target-verus/release/verus --crate-type=lib ../examples/round_robin.rs
./target-verus/release/verus --crate-type=lib ../examples/drain.rs
```

### Running Tests

```sh
cd source
source ../tools/activate
vargo test -p rust_verify_test --test temporal   # 54 temporal logic tests
vargo test -p rust_verify_test --test loops      # 62 loop regression tests
```

## Examples

 * [`examples/round_robin.rs`](examples/round_robin.rs) — AG(AF) fairness: every element eventually returns to the head
 * [`examples/drain.rs`](examples/drain.rs) — AF progress: draining a queue eventually empties it
 * [More Verus examples](examples) illustrating various features

## Built on Verus

Vera is a fork of [Verus](https://github.com/verus-lang/verus), a tool for verifying
the correctness of Rust code using SMT solvers. All standard Verus features (safety
verification, vstd, state machines, etc.) remain fully functional.

 * [📖 Verus Tutorial and reference](https://verus-lang.github.io/verus/guide/)
 * [📖 vstd API documentation](https://verus-lang.github.io/verus/verusdoc/vstd/)
 * [💬 Verus Zulip](https://verus-lang.zulipchat.com/)
 * [Verus License](LICENSE)
