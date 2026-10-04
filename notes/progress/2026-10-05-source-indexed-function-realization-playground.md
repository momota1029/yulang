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

## Returned Function through source aliases

The same test module now drives the real parser, HIR resolver, constraint
collector, solver, and closed-scheme generalizer on this supported source
shape:

```text
my id x = x
my wrap ignored = id
my left = wrap
my right = wrap
```

It generates all 24 declaration orders and four pairs of hygienic parameter
renamings (96 complete source modules). For every module, it checks that HIR
resolves `wrap`'s returned Function to the original `id` root and both aliases
to the original `wrap` root; collection retains exactly those three named-use
edges; solver routing consumes each collected use once; and the finalized
schemes have the principal shape `id : 'a -> 'a` and
`wrap/left/right : any -> ('a -> 'a)`, with one shared quantifier across the
nested Function argument/result and the expected pure effect ports. The
production instantiation counter also records three fresh value variables,
one for each polymorphic source use across the returned Function chain.

This characterizes source-root preservation, higher-order scheme
generalization, and distinct closed-use instantiation on the current
application-free HIR fragment. It directly exercises production source and
solver artifacts, but no call is made through the returned Function because
current HIR still has no application lowering. The check therefore does not
establish complete Function-bound membership, callback adequacy, B-step-6
endpoint generation, or principal common-allowance factorization. All 96
generated cases pass; this adds evidence without closing those gates.

## Bounded later invocation through the returned root

A second test-only executable model now composes the HIR-derived wrapper
return with a later call through the returned `id` value. The actual HIR
provides `wrap`'s resolved body root, the original `id` lambda/body/binder
identities, and the two alias-to-wrapper links. The model then runs the
approved Value-entry ordering for the wrapper (receipt, one argument Force,
body, return of the original `id` root), followed by the existing
Pure-value-through-Handler-view invocation model for that root.

The generated space has 73 completely handled wrapper argument histories
(zero, one, or two requests, with two operation labels and all binary values
and resumed states) and 9 future-call histories (zero or one request with the
same response dimensions), for both `left` and `right`: 1,314 composed traces.
Checks keep the wrapper and future-call receipts, Force events, body
occurrence/binder, request origin/continuation, result, and current state
separate. The first future request observes the wrapper's final resumed state;
future use preserves the original Pure/Value entry under a Handler view and
does not replay the wrapper trace.

This is an executable composition of the bounded source rules over actual
resolved HIR identities, not execution of production calls: current HIR still
has no application node, and the wrapper/future invocation transitions are
driven by the test model. It does not establish complete Function-bound
membership, all-history adequacy, or a production endpoint bridge. The finite
probe passed and found no counterexample in its generated space.

The independent compiler-referee review found that the first test draft used
the model's returned state as the expected future state, so a constant-zero
outer-state mutant could pass. It also found that event membership checks
could miss reordered or omitted events. The test now computes the expected
state directly from outer responses and compares complete ordered wrapper and
future traces against independently constructed expectations, including
request identities, body provenance, and exact state transitions. The focused
rerun passes; the concrete checker weakness is retained here as proof-search
evidence rather than hidden as a green-test-only repair. A follow-up review
also aligned the wrapper entry marker with the returned `Name` body occurrence,
matching the future identity function's body-occurrence convention. All
reported findings are closed within this finite handled-history scope.

## Retained Function artifact reconstruction

The `cfg(test)` probe now retains the complete positive Function port tuple,
its `LambdaRecipe`, the body occurrence and binder, the original component
handles, and distinct body/construction effect-row identities. It checks that
the positive result-effect port is the exact body-row handle and that the
source body and construction constraints retain their occurrence, slot,
polarity, and provenance links. Across the existing 96 declaration-order and
renaming variants, these links are carried through generalized schemes and
three fresh closed-use routes; the check preserves the shared diagonal and
distinguishes positive polarized effect leaves from negative ones.

Three local mutations are rejected: replacing the body row with the
construction row, attaching another Lambda's body row, and substituting a
different positive Function result coordinate. The F4 boundary is also
checked: every source Lambda occurrence is present in the public projection,
its internal body occurrence is absent, and its projected effect is
unconditionally checked as `Empty`. The independent compiler-referee review
found this membership check could be vacuous when conditionally guarded by the
projection list; the test now asserts the exact inclusion/exclusion before
checking the projection. Focused tests pass after that repair.

This improves reconstruction of existing source-indexed evidence only. It
introduces no production carrier or denotation, and does not close complete
Function-bound membership, callback adequacy, B-step-6 endpoint generation,
or principal common-allowance factorization. The boundary remains the actual
HIR's lack of application/callback invocation lowering.

## Independent complete-root membership audit

An architect audit of the smallest current Pure Function root, `id x = x`,
isolates the production bridge's missing semantic clause. Existing owners retain
the lambda occurrence, parameter ordinal, body/value/effect components, and
admission position (`LambdaRecipe`); `emit_lambda` records the identity-body
constraints; `admit_lambda_fact` emits the linked positive Function lower
contribution; generalization follows the actual definition-root row and
materializes the four Function ports; closed-use routing freshens and routes
decoded type predicates. The Function term retains its polarized children and
lineage. These facts establish source ownership and endpoint sharing, but not
the complete membership of the interpreted actual Function bound.

The smallest missing clause is **exhaustive root membership/admission**:
specify which finite typed observations belong to the actual bound at each
admitted challenge under fixed `nu,K,D`, and give every admitting alternative,
including any conservative endpoint extras, a finite scope-preserving decoder
to retained source/local-bound evidence. Source execution rules provide
witnesses for executions but do not exclude additional memberships; endpoint
ports and provenance likewise do not decide whether the bound is exactly
source-witnessed or admits other port-compatible behavior. Defining the actual
bound as the image of the source generator would assume the missing
production-conformance result, so it is not a derivation.

This audit finds neither a source counterexample nor evidence that the current
carrier is insufficient. It does not promote the exact-source-witness reference
interpretation to production semantics and does not select a new carrier. Once
the exhaustive membership/admission clause is independently settled, the next
proof obligation is to construct its decoder and show that closed-use
freshening preserves the same scopes, rigid quantifier positions, coupled
polarized effects, and `nu,K,D`. Review scope was this `id` root and its source,
constraint, Function-term, generalization, and closed-routing owners; no code,
tests, or measurements changed.
