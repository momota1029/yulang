# Omitted formal: retained Function field correspondence observation

Date: 2026-10-15
Status: provisional test-only observation; exact focused execution complete; one minor M1 reporting finding closed by primary repair
Branch: `research/simple-sub-intrusion`
Frozen HEAD: `402596bdbecdee9aee970e8cfdb05830960e7726`
Production baseline: `427d1ff5daab866fa7d89cb513a077063cc6454d`
Parent gates: H1/H2/U OPEN; H3/P disabled; profile-position matrix undecided

## Scope and authority

Authority: top-level inference principles §1.1 and annotation integration
§§1,3–5. This additive observation preserves the exact receiving-call fixture,
HIR/Apply/FormalConstruction authentication, all existing assertions and the
same-comparison condition `incidence.comparison == parent`.
It consumes the completed exact pair/source census and the reviewed bounded
Parent processing correspondence, without strengthening their conclusions.

Only `candidate_context_tests.rs` and this note are leased. No production
retention, semantic contract, expected output, profile position or theorem
status changes. The primary owns execution, independent review and integration.

## Bounded observation and owning seam

At an immediate Replay of a FunctionPort Argument comparison whose upper
Derived/Transport ancestry reaches the uniquely authenticated `cb x` source,
inspect every retained Extrusion TransportWitness on that ancestry. Decode
both Function terms in the witness's bound endpoints. Preserve all four actual
terms and the bound polarity. Argument and ArgumentEffect reverse that polarity;
ResultEffect and Result preserve it, as `candidate_extrusion::Work::Function`
constructs them. Decode raw LiveVariable/Component row identities directly;
`value_endpoint` and `effect_endpoint` canonicalize and are deliberately not
used for this comparison.

For each of the four source-associated Parent records, enumerate every field
whose raw original/output rows equal its parent/copy and whose field polarity
matches the saved Parent polarity. Print every match; a shared or repeated field
is never selected by iteration order. An empty match is not proof of selected-
bound descent. Work::Bound can copy selected descendants separately from the
direct child keys reconstructed by Work::Function.

An exact consumer-input flag additionally requires both the actual transported
RelationId to be the Replay upper input and the full witness.to BoundKey to
be that exact upper_input. Function endpoint matching alone cannot authenticate
the consumer. Existing Replay bound-pair assertions remain in place.

The static source frontier is the association between an individual Parent
Visit and Work::Function's child key/output, versus a Work::Bound selected
descendant. Work::Function keeps the child map locally and retains no per-field
certificate; candidate_effect::candidate_transfer_bound_origins retains whole
BoundKey from/to witnesses. This source inspection does not establish that this
is the first break on a particular consumer path.

In the exact run, the authenticated later `cb x` consumer ancestry was
`RelationId(66) --Transport(FreshUse)--> RelationId(13) --Derived--> RelationId(5)`.
There were zero qualifying Extrusion Function TransportWitnesses on that
ancestry. Consequently the run produced no per-copy field candidate sets and
evaluated no exact consumer-input flags. The four Parent records still share
the source relation, but this runtime result does not connect an individual
Parent to a Function field or identify the consumer-path break before that
point. No inverse relation or production retention field was added.

## Frozen inputs and checks

Dependency hashes were rechecked before writing and match the supplied census
and source-correspondence baselines:

```text
e6d9f5c983932e45616802810aa033d4d273baa44d04f512e5e97a4c9e3cbd77  candidate_context_tests.rs before edits
c4ffa98c7dacad210d1e0682ffec9628d2c914f78e6f4086d9062d0e912400aa  candidate_context_tests.rs after review repair
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  candidate_context.rs
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1  candidate_extrusion.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  candidate_effect.rs
77b145ed8a8bf2fae30a07ed74d11a29f38d18930f92e3c1c10456244fe9402e  candidate_intrusion.rs
e902da1c9a7f0fb4dcd806c87563d1ae46d35bbb999e69b7fee51c3c0f6e4bf5  lib.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd  candidate_scheme.rs
3a1ad7155d784c1ff0234dc7815f0d49618bff307a6564c0646cf8e510a248c4  candidate_source.rs
3db7eb04045391ceb939612226ea87e7bac6c035f3c2d4c210a8d3d4fd641831  shadow_apply.rs
```

Worker check: `git diff --check` passed. Worker used zero Cargo/build/test/probe
processes and zero measurement samples. Primary ran the required focused
command twice; both passed (`1 passed; 688 filtered out`) and reported the runtime
ancestry obstruction above. A fresh M1 compiler_referee review found one minor
reporting issue: the runtime obstruction and static source frontier shared one
label. The test diagnostic and this note now separate them. No semantic or
implementation finding remains. No delegates or Git mutations. M1; one bounded
static producer pass within the twenty-minute budget.

```sh
CARGO_BUILD_JOBS=2 timeout 300s cargo test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --lib candidate_context::tests::omitted_formal_receiving_call_records_authenticated_argument_dispatch -- --exact --nocapture --test-threads=1
```

Unverified: other fixtures/runs; all-path transport, source profiles,
protection, U, dynamic Receive/Observe, full Call, soundness, principality and
cutover. No parent gate closes.
Remaining decision: any production certificate requires a separately authorized
owner packet; no representation choice is made here. Shared task/theory/index
synchronization remains primary-owned and intentionally deferred.

Proposed checkpoint message: `research: observe omitted-formal raw Function fields`.
