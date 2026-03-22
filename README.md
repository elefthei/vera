# <a href="https://verus-lang.github.io/verus/verus/logo.html"><img height="60px" src="https://verus-lang.github.io/verus/verus/assets/verus-color.svg" alt="Verus" /></a> Vera (Verus Always)

**Vera** extends [Verus](https://github.com/verus-lang/verus) with **CTL temporal logic**
to prove **liveness** and **fairness** properties of Rust programs at compile time,
built on the [TICL](https://arxiv.org/abs/2410.14906) framework.

## Temporal Operators

| Operator | Meaning |
|----------|---------|
| `ag(φ)` | **Always globally**: φ holds at every state of an infinite computation |
| `af(done(Q))` | **Always finally**: program terminates with postcondition Q |
| `af(now(Q))` | **Always finally**: Q holds at some future state (no termination needed) |
| `au(φ, ψ)` | **Always until**: φ holds at every step until ψ is reached |

Operators compose structurally via [TICL](https://arxiv.org/abs/2410.14906) rules.
`now(Q)` is a state predicate (holds at a single state); `done(Q)` requires termination.
`ag(af(now(Q)))` expresses **fairness** — Q recurrently holds forever.

## Example: Round-Robin Fairness

```rust
use vstd::prelude::*;
verus! {

/// AG(AF(now(peek == x))): every element always eventually returns to the head.
fn round_robin(queue: &mut Queue, Ghost(x): Ghost<u64>)
    requires
        old(queue).view().len() > 1,
        old(queue).view().contains(x),
    ensures
        ag(af(now(queue.peek_spec() == x))),
{
    loop
        invariant
            queue.view().len() > 1,
            queue.view().contains(x),
        decreases queue.view().index_of_first(x),
    {
        let val = queue.dequeue();
        queue.enqueue(val);
    }
}

} // verus!
```

See [`examples/round_robin.rs`](examples/round_robin.rs) for the full proof
and [`examples/drain.rs`](examples/drain.rs) for an `AF(done(Q))` termination proof.

## Building

```sh
./tools/get-z3.sh                         # download Z3 4.12.5
cd source && source ../tools/activate     # set up vargo
vargo build --vstd-no-verify              # build Vera

# Run examples
./target-verus/release/verus --crate-type=lib ../examples/round_robin.rs
./target-verus/release/verus --crate-type=lib ../examples/drain.rs

# Run tests (103 temporal + 62 loop)
vargo test -p rust_verify_test --test temporal
vargo test -p rust_verify_test --test loops
```

## Built on Verus

Vera is a fork of [Verus](https://github.com/verus-lang/verus). All standard
Verus features remain functional.

 * [📖 Verus docs](https://verus-lang.github.io/verus/guide/) · [📖 vstd API](https://verus-lang.github.io/verus/verusdoc/vstd/) · [💬 Zulip](https://verus-lang.zulipchat.com/) · [License](LICENSE)
