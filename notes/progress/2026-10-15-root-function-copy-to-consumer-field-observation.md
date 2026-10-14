# Root Function output index and raw consumer field observation

Date: 2026-10-15
Status: provisional test-only observation; focused run passed and fresh M1 static review found no findings
Branch: `research/simple-sub-intrusion`
Assigned baseline: `3348b704ca23361414fdb118884a89daa202e8f7`
Expanded-lease baseline supplied by primary: `e61bd7389`
Production baseline: `427d1ff5daab866fa7d89cb513a077063cc6454d`
Parent gates: H1/H2/U OPEN; H3/P disabled; profile-position matrix undecided

## Authority and scope

Authority: [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§1.1 and [annotation integration](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1,3–5. Inputs are the exact receiving-call fixture, the
[pair/source census](2026-10-15-omitted-formal-copy-relation-uniqueness.md),
[Parent source correspondence](../theory/2026-10-15-extrusion-parent-source-correspondence.md),
[prior field observation](2026-10-15-omitted-formal-copy-field-correspondence.md),
and [root lineage audit](../theory/2026-10-15-root-function-extrusion-bound-lineage-audit.md).
The fixture, existing assertions and public compiler behavior are preserved.

The initial test/note lease could not read `candidate_intrusion::State`'s
private output index. The primary explicitly expanded the lease for exactly
one `#[cfg(test)]` read-only accessor in `candidate_intrusion.rs`. The accessor
looks up the exact `(TypedPairKey, ExtrusionEndpoint)` entry and copies every
indexed group's id, occurrence, start, end and activation flag. Runtime fields,
constructors, index behavior and production paths are unchanged.

## Bounded discriminator

At the existing authenticated source-to-consumer join, enumerate retained
FreshUse transports whose child is the actual Replay upper RelationId, whose
complete destination BoundKey is the exact Replay upper_input, and whose
antecedent has an explicit Derived edge to the authenticated source relation.
Require one such witness; report zero/multiple witnesses without selecting by
numeric identity or iteration order.

Query the existing output index using that source's exact RelationKey pair
and the actual witness.from endpoint. Print every matching group. Require one
group, and require its full span to equal the four exact census Parents;
check every Parent's occurrence, comparison pair and source set. A singleton
index entry alone supplies no source RelationId or activation history.

For a supported group, decode actual Function child terms at the source's
original upper demand, exact indexed root witness.from endpoint and exact
consumer witness.to endpoint. Enumerate Argument, ArgumentEffect,
ResultEffect and Result with actual composed polarity. Compare each raw Parent
parent/copy pair with original/root fields using direct LiveVariable/Component
identities, without row representative translation. Print all candidates;
stop at the first missing/shared candidate. For a unique field, decode and
report its same-position FreshUse consumer raw row, preserving shared consumer
fields as ambiguity. The actual upper RelationId and complete BoundKey are
printed alongside the field observation. Bound polarity must agree across
FreshUse. No identity equality between root and fresh consumer rows is assumed.

This is a bounded raw field observation, conditional on retained witnesses
and the existing source/construction bridge. Even a successful observation
cannot authenticate relation 13's rewrite-enqueue activation, prove all-path
transport, construct profiles or certify protection. The earlier Extrusion
witness observation continues with its historical runtime limitation; this
new discriminator examines FreshUse and the existing root-output index.

## Focused runtime result

The exact focused test passed once (`1 passed; 688 filtered out`). It found one
qualifying FreshUse edge: child `RelationId(66)`, antecedent `RelationId(13)`,
from `BoundKey(ValueRow(14), Negative, NegativeFunction(term 269))` to the exact
Replay upper input `BoundKey(ValueRow(24), Negative, NegativeFunction(term
335))`. The explicit ancestry also contains `Derived(13, 5)`.

For source `RelationId(5)` and its exact `(pair, term 269)` index key, the
lookup returned one group `(id 0, occurrence 0, span 0..4, activated false)`.
Its full span equals the four census Parents, each with the source pair and
source set. The raw fields matched uniquely in order:

| Field | Original term | Indexed root term | FreshUse consumer term | Parent raw rows | Consumer raw row |
| --- | --- | --- | --- | --- | --- |
| Argument | 258 | 265 | 331 | Value `16 -> 17`, positive | Value 28 |
| ArgumentEffect | 260 | 266 | 332 | Effect `9 -> 14`, positive | Effect 29 |
| ResultEffect | 261 | 267 | 333 | Effect `13 -> 15`, negative | Effect 28 |
| Result | 259 | 268 | 334 | Value `8 -> 18`, negative | Value 27 |

Every consumer row had one same-position field match. The recorded observation
is therefore `complete=true` for this one retained group and one exact consumer
BoundKey. This ties the four raw Parent pairs to the root Function output
indexed for source relation 5 and to the corresponding fields of the observed
FreshUse consumer. It still does not identify relation 13's unique enqueue
activation, establish all-path transport, or supply any protection/profile
semantics.

## Frozen inputs and artifact hashes

```text
c4ffa98c7dacad210d1e0682ffec9628d2c914f78e6f4086d9062d0e912400aa  candidate_context_tests.rs input
d022b69f8e9d3427ba69a08d81a8d51bc773dc50beb8ed3c62ea8cdd62bf008d  candidate_context_tests.rs artifact
77b145ed8a8bf2fae30a07ed74d11a29f38d18930f92e3c1c10456244fe9402e  candidate_intrusion.rs input
4a2b87ebf6e5e219c06763bc4e589517fd48c575c89038f2a11fc1e6494fe90e  candidate_intrusion.rs artifact
ed3e213e943a553943784e409194723f64acb810a0bcf06607ee95b0eb4e4ed1  candidate_extrusion.rs
c8ef7cc472f0dcb60d793c6f9b4f6ba1aefb76f919ff2a3ce9310f85eb647dcd  candidate_scheme.rs
6301ca80eec137df3f2c2c44e2edaa7dbdf1ed7a78c69617228888e63654e461  candidate_context.rs
f414efa7efdb17644f4dfa6b0bba621c1bb7cccd0f83735c33a0acb875da6b91  candidate_effect.rs
2845b4272783373fe339840d6f3bc570d6d4547ad6d6231419f24806c1b5e2aa  root lineage audit
efa7900907acd9a6c1da70fa841918e6aba3ed7977a1cece1c624259e49be8a3  Parent source correspondence
6d932619565db4f3556c7fa29a90a3f2c8a8828d42d8758cdcca55879e884cdb  pair/source census
```

## Checks and handoff

Worker checks: bounded `rg`/`sed`/`cat` source and authority reads; exact
`sha256sum` of the named inputs/artifacts; static lease/syntax inspection.
The primary ran the exact focused test command below once; one fresh
`compiler_referee` found no findings in the accessor and observation logic.
No probe or performance measurement ran. M1, one bounded static/edit pass
within the twenty-minute allocation; ten primary Cargo processes have been
used cumulatively, with zero measurement samples. The reviewer used one
read-only `git diff e61bd7389 -- …` contrary to its no-Git packet; no state
changed, and it disclosed this in its report.

Primary-owned focused command:

```sh
CARGO_BUILD_JOBS=2 timeout 300s cargo test -q -p yu-solver --features shadow-f5,shadow-apply-candidate --lib candidate_context::tests::omitted_formal_receiving_call_records_authenticated_argument_dispatch -- --exact --nocapture --test-threads=1
```

Unverified: other states or fixtures, selected-descendant correspondence,
rewrite activation, all-path transport, profiles/protection/U, full Call,
soundness, principality and F5 cutover. No parent gate closes.
No certificate design, production retention or profile decision is made.

Exact changed paths: `crates/yu-solver/src/candidate_intrusion.rs`,
`crates/yu-solver/src/candidate_context_tests.rs`, and this note.
Shared task/theory/index synchronization remains primary-owned and deferred.
Proposed checkpoint: `research: observe root output index and raw consumer fields`.
