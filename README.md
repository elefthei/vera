[![Quick Start](https://img.shields.io/badge/tutorial-quick%20start-informational)](https://verus-lang.github.io/verus/guide/getting_started.html) [![Verus docs](https://img.shields.io/badge/docs-verus-informational)](https://verus-lang.github.io/verus/guide/) [![Library Documentation](https://img.shields.io/badge/docs-vstd-informational)](https://verus-lang.github.io/verus/verusdoc/vstd/) [![project chat](https://img.shields.io/badge/zulip-join_chat-brightgreen.svg)](https://verus-lang.zulipchat.com)

# <a href="https://verus-lang.github.io/verus/verus/logo.html"><img height="60px" src="https://verus-lang.github.io/verus/verus/assets/verus-color.svg" alt="Verus" /></a> <a href="https://github.com/verus-lang/verus"><picture><source media="(prefers-color-scheme: dark)" height="60px" height="60px" srcset="https://verus-lang.github.io/verus/verus/assets/verus-text-dark.svg" /><img height="60px" height="60px" src="https://verus-lang.github.io/verus/verus/assets/verus-text-light.svg" alt="Verus" /></picture></a>

Verus is a tool for verifying the correctness of code written in Rust.
Developers write specifications of what their code should do,
and Verus statically checks that the executable Rust code will always 
satisfy the specifications for all possible executions of the code.
Rather than adding run-time checks, Verus instead relies on powerful solvers to
prove the code is correct.  Verus currently supports a subset of Rust (which we
are working to expand), and in some cases, it allows developers to go beyond
the standard Rust type system and statically check the correctness of code
that, for example, manipulates raw pointers.  

![VS Code Demo](source/docs/verus-demo.png)

## Status

Verus is under *active development*. Features may be broken and/or missing, and
the documentation is still incomplete. If you want to try Verus, please be
prepared to ask for help in the [💬 Zulip](https://verus-lang.zulipchat.com/).

The Verus community has published a number of research papers, and there are a
variety of industry and academic projects using Verus. You can find a list on our
<a href="https://verus-lang.github.io/verus/publications-and-projects/">publications and projects</a> page. 
If you're using Verus please consider adding your project to that page (see the instructions there).

## Try Verus

To try Verus in your browser, please visit the [Verus Playground](https://play.verus-lang.org/).
For more involved development, please follow our [installation instructions](INSTALL.md).
Then you can dive into the documentation below, starting
with the [📖 Tutorial and reference](https://verus-lang.github.io/verus/guide/).
We also support an auto-formatter ([verusfmt](https://github.com/verus-lang/verusfmt)) for your
Verus code.

## Documentation
Our (work-in-progress) documentation resources include:
 * [📖 Tutorial and reference](https://verus-lang.github.io/verus/guide/)
 * [📖 API documentation for Verus's standard library](https://verus-lang.github.io/verus/verusdoc/vstd/)
 * [📖 Guide for verifying concurrent code](https://verus-lang.github.io/verus/state_machines/)
 * [Contributing to Verus](CONTRIBUTING.md)
 * [Best Practices](best-practices-for-publishing-verusverified-code-on-cratesio) for publishing Verus-related crates on [crates.io](crates.io).
 * [Verus License](LICENSE)
 * [Verus Logos](https://verus-lang.github.io/verus/verus/logo.html)

## Temporal Verification (Experimental)

Verus includes experimental support for **CTL temporal logic** operators in postconditions,
enabling verification of **liveness** and **fairness** properties for programs with loops.

### Supported Operators

| Operator | Meaning |
|----------|---------|
| `ag(φ)` | **Always globally**: φ holds at every state of an infinite computation |
| `af(φ)` | **Always finally**: φ is eventually reached (sugar for `au(true, φ)`) |
| `au(φ, ψ)` | **Always until**: φ holds at every state until ψ is reached |
| `ag(af(φ))` | **Fairness**: φ recurrently holds forever (always eventually) |

### How It Works

Temporal postconditions are decomposed into standard first-order verification conditions
using structural rules from the [TICL](https://github.com/eioannidis/ticl) framework:

- **`ensures ag(φ)`** — the function must contain an infinite loop (`loop` without `decreases`)
  whose invariant R implies φ. The loop may never exit.
- **`ensures af(φ)`** — equivalent to standard termination + postcondition for sequential code.
  The loop needs a `decreases` clause proving progress toward φ.
- **`ensures au(φ, ψ)`** — path property φ holds until goal ψ is reached. Requires `decreases`
  weakened to ψ ∨ (measure decreased).
- **Prefix code** (assignments, calls before the temporal loop) must maintain φ at every step
  (sequence composition rules).

### Example: Round-Robin Fairness

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

/// Round-robin loop with AG(AF(peek == x)) fairness postcondition.
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

### Building This Branch

This feature lives on the `ctl-operators-liveness` branch and requires a
**forked `syn`** crate (vendored in `dependencies/syn/` as `verus_syn`) that adds
temporal keyword parsing. To build:

```sh
# 1. Get Z3
./tools/get-z3.sh           # downloads Z3 4.12.5, sets VERUS_Z3_PATH

# 2. Build (from source/ directory)
cd source
source ../tools/activate     # sets up vargo (cargo wrapper for Verus)
vargo build --vstd-no-verify # fast build, skips vstd SMT verification

# 3. Run an example
./target-verus/release/verus --crate-type=lib ../examples/round_robin.rs
./target-verus/release/verus --crate-type=lib ../examples/drain.rs
```

> **Note:** The vendored `dependencies/syn/` is checked into this branch — no
> extra submodule or crate registry setup is needed. The workspace `Cargo.toml`
> references it via local path as `verus_syn`.

## Examples of Using Verus
In addition to the documentation above, it can be helpful to see Verus used in action.  Here are some starting points.
 * [Publications and projects](https://verus-lang.github.io/verus/publications-and-projects/) using Verus.
 * [Videos, slides, and exercises](https://verus-lang.github.io/event-sites/2024-sosp/) from a day-long Verus tutorial.
 * [Standalone examples](https://github.com/secure-foundations/human-eval-verus/) showing Verus in use for small, concrete tasks.
 * [Small and medium-sized examples](examples) illustrating various Verus features
 * [Unit tests](source/rust_verify_test/tests) for Verus, containing examples of Verus syntax and features.

## Getting in touch, reporting issues, and starting discussions

Please report issues or start discussions here on GitHub, or join us on [💬 Zulip](https://verus-lang.zulipchat.com/) for more realtime discussions and if you need help. Thank you for using and contributing to Verus!

We use GitHub discussions for feature requests and more open-ended conversations about
upcoming features, and we reserve GitHub issues for actionable issues (bugs) with
existing features. Don't worry though: if we think an issue should be a discussion (or
vice versa) we can always move it later.

We welcome contributions! If you'd like to contribute code, have a look at the tips in
[Contributing to Verus](CONTRIBUTING.md).

---

[<img src="source/docs/zulip-icon-circle.svg" alt="Zulip" style="height: 1em;"/> Zulip](https://zulip.com/) sponsors free hosting for Verus. Zulip is an open-source modern team chat app designed to keep both live and asynchronous conversations organized.

Special thanks to Johanna Polzin for her contribution to the design of the Verus Logo. The Verus logos (bitmap and vector) are by the <b>Verus Contributors</b> and licensed under the terms of <a href="https://creativecommons.org/licenses/by/4.0/?ref=chooser-v1" target="_blank" rel="license noopener noreferrer">Creative Commons Attribution 4.0 International<img style="height:22px!important;width:22px!important;margin-left:3px;vertical-align:text-bottom;" src="https://mirrors.creativecommons.org/presskit/icons/cc.svg?ref=chooser-v1" alt=""><img style="height:22px!important;width:22px!important;margin-left:3px;vertical-align:text-bottom;" src="https://mirrors.creativecommons.org/presskit/icons/by.svg?ref=chooser-v1" alt=""></a> license.
