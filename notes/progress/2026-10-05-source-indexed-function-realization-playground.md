# HIR-backed Function realization candidate

Date: 2026-10-05
Status: bounded research candidate; no production denotation or implementation authority
Governing direction: [executable inference research playgrounds](../design/2026-10-04-inference-research-playgrounds.md); [source-generated callback theorem](../design/2026-10-04-source-generated-callback-structural-theorems.md) Theorem C; [production endpoint-generation draft](../design/2026-10-04-production-callback-endpoint-generation-draft.md) §§3–4.
Review: compiler_referee and spec_auditor found no blocking or major issues;
the compiler_referee's minor continuation-boundary note is addressed below.
The resumption-transition probe first exposed a major gap (the model ignored
resumed state); it now threads response state/value through the suffix and
body and asserts the exact state-dependent trace. The compiler_referee delta
review found no remaining issue within this bounded probe.

The `cfg(test)`-only module
[`research_function_realization.rs`](../../crates/yu-solver/src/tests/research_function_realization.rs)
starts from actual resolved HIR, collected constraints, admitted Function
facts, provenance, and generalized schemes for:

```text
my id x = x
my zero x = 0
```

It derives `Identity` or `Constant(0)` from each retained HIR body rather than
accepting a body tag, endpoint, selected occurrence, or admission bit as
input. It follows the root-owned positive Function fact and checks the
existing endpoint relationships: `id` shares its negative argument and
positive result variable, `zero` has a distinct result component constrained
to `int`, both have empty argument effects and bottom result effects. The
closed schemes are checked against `('a -> 'a)` and `any -> int`.

From that source artifact it constructs a finite input challenge grammar:
integer inputs `0`/`1`, an empty trace, or one/two ordered `Read`/`Write`
requests, each either completed or suspended. This gives 13 input-history
shapes and 26 complete old tuples per Lambda. Admission is generated from the
selected Int instantiation and the history grammar, independently of any
pending inequality. The candidate source rule applies the HIR-derived body
only after a completed `Force`; suspended histories retain the deferred body
occurrence as a terminal trace token. The approved typed observation
projection erases concrete input and output integers while retaining result
type, typed requests, completion, source occurrences, the actual HIR binder
identity, and one fixed opaque `nu,K,D` assignment. Request origin/continuation
tokens come from the bounded argument-history grammar; they are not extracted
from production HIR.

In the finite lift-set portion above, the suspension token is not an executable
continuation: that portion does not run response/resumption transitions or the
pending argument suffix. It is a finite terminal/suspended trace projection
only, not the request/bind continuation correspondence required by Theorem C
§2.3.

A separate `cfg(test)` transition probe now covers that operational seam for
two explicit two-request histories. It splits `Force(D) >>= B` once after the
first request and once after the second; each response updates the live state
and forced argument value, the suffix request observes the updated state,
and the HIR-derived Identity body returns the resumed argument value. It
preserves the original request origin/continuation, reaches the body only after
the final response, and does not replay receipt or Force. It also keeps the
Pure value's actual role/Value entry separate from the Handler callback view.
This is source-rule characterization for those traces, not production
execution or bound membership evidence; the finite history set in the lift
test above remains terminal/suspended only.

The checked candidate copies each full old tuple and adds one total fresh
coordinate defined from that tuple. For both bodies, the projected actual and
checked observation sets agree on the 26 generated tuples, with 13 distinct
projected observations. This checks the local reconstruction and total-lift
code against the displayed finite grammar.

The model does **not** equate its generated relation with current production
Function-bound denotation. The current code retains HIR and the four-port
Function fact, but does not attach complete value-root, Force/entry/body/result
history membership to that endpoint. It also has no application or callback
invocation HIR node. Thus the bounded transition probe is not driven by
production HIR application nodes, and neither it nor the finite lift test
establishes production actual-side factorization or checked-side embedding.
Those theorems remain open. No source counterexample was found, and no
production behavior changed.

Verification: focused command
`cargo --config 'build.rustc-wrapper=""' test -p yu-solver tests::research_function_realization -- --nocapture`.
The global Cargo config routes rustc through `sccache`, which failed with
`Operation not permitted`; the per-command wrapper override let the same
focused test run directly and pass. Python/script checks and broad suites were
not run for this Rust-only gate.
