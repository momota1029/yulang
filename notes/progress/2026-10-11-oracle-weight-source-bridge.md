# Exact nested source: directed-weight incidence before publication

Date: 2026-10-11
Status: frozen, unreviewed research source correspondence; original H remains OPEN
Claim class: bounded constructor derivation and first missing producer, not a universal theorem or source-qualified counterexample
Yulang3 HEAD at start: `0971cf7a921cd1aef92b8e7bcdf3800654dc63c4`
Assigned solver baseline: `35e88c8113c9c6516e260170503bea753e4ede6`
Oracle revision supplied by primary: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Inspected Oracle source root: `/tmp/yulang2-oracle-read`
Exclusive lease: this file only; leaf, no delegation or Git mutations

## Objective and fixed scope

Determine whether the exact source A already supplies the same authentic ID on
both a latent PUSH and an omitted right component of an included positive lower
reaching `compact_lower_bounds_from`, followed by an actual instantiated
call/output. This is the missing source incidence in
[generalized observation proof](../theory/2026-10-11-oracle-generalized-observation-proof.md)
§4, under original H in
[global effect hygiene](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§1. No hypothetical weighted Function is a source witness.

Authority remains [annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5, [concrete implementation gate](../design/2026-10-10-concrete-effect-annotation-implementation.md)
including its annotation checking/publication, conflict/replay and practical
formation sections, and [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 and Authority and integration. Contravariant concrete rows permit scoped
subtraction; covariant rows permit concrete members; composed polarity and
symbolic connections retain the selected meaning. No withdrawn callback result,
new meaning, source restriction or implementation permission is used.

Exact source, already accepted by the primary's three-run characterization:

```yulang
pub act tick:
    pub ping: () -> ()
my f(cb:(() -> (() -> [tick] ()))) = (cb ()) ()
```

Coverage is this source alone. No provider body, invocation of `tick.ping`,
reference to `f` after its definition, symbolic source tail, independent sibling
contribution or recursive source cycle is present. No source variant or fourth
Oracle invocation was authorized or run. The earlier A dump is accepted input
evidence, not an independently reproduced run here.

## Hypotheses and identity ledger

The derivation assumes the inspected source bytes, the already-qualified
annotation tree, valid arena coordinates, normal completion of the named
constructors and fresh allocation without exhaustion. It does not assume all
bound replay, projectability, extrusion correctness, preserved schemes, or H.

Use construction names rather than rendered `#0` as identity evidence:

| Name | Actual owner in A |
| --- | --- |
| a | The inner result-effect annotation `[tick]` within cb's formal annotation |
| i | Fresh `SubtractId` returned by a's `effect_row_stack` call |
| q | a's `function_boundary_effect_stack_inner` coordinate; a has no named tail |
| x | cb's actual lambda-parameter Value coordinate |
| P0 / N0 | Positive/negative outer Function companions attached to x |
| P1 / N1 | Positive/negative inner Function companions, returned by P0 / N0 |
| k1, v1, e1 | First application `cb ()`, its result Value and application Effect |
| k2, v2, e2 | Second application `(cb ()) ()`, its result Value and application Effect |
| c1 / c2 | Actual call-effect coordinates allocated by k1 / k2 |

These are one constructor derivation. No provider is substituted independently.
The provider inside this source is the formal's annotation-supplied positive
companion; no implementation of cb is supplied. q is an inferred coordinate,
not evidence of a connected symbolic source tail. The published `'b` and `#0`
names do not independently identify q or i.

## Constructor derivation and the first blocked incidence

Oracle paths below are relative to the inspected source root.

1. `annotation/constraints.rs::connect_parameter_computation_detailed`
   (251–282) activates parameter-boundary lowering. `connect_value_detailed`
   (124–137) emits P0 <: x and x <: N0 using ordinary unweighted subtype calls.
   `lower_value_bounds` (363–389) builds the four ports of both Function
   companions. For a, `lower_ret_effect_bounds` (424–470) obtains q, freshly
   allocates i, registers its declared fact, and builds PUSH_i(q) as P1's
   result Effect. Its negative companion is FILTER_tick(q).

2. The same inner constructor puts POP_i with the tick filter on **P1's Unit
   result Value**, via `wrap_non_subtracts` (848–851) and `predicate_weights`
   (921–925). The outer Function's immediate result Effect is omitted:
   `pure_effect_bounds` (492–499) supplies an empty subtraction list. Therefore
   P0's result Value is P1 without an i-POP wrapper, and P0's returned
   `output_subtracts` is empty. The Function constructor returns its immediate
   `ret_eff.subtracts`; it does not accumulate `ret.output_subtracts`.

3. cb is a `Def::Arg` with `scheme: None`, created in
   `lowering/pattern.rs` (242–281). Its name use reaches
   `lowering/name_ref.rs::lower_local_name` (145–175), but
   `tail.rs::instantiate_local_value` (855–859) returns that same x before any
   instantiator call. This syntactic lookup is not a generalized fresh use.
   `lambda.rs::connect_lambda_pattern_annotation` (1267–1341) marks the
   annotated parameter's `call_return_effect` as Annotated. Thus k1's
   `tail.rs::unannotated_local_callee_return_effect` (740–763) also returns bare
   c1; its later fresh unannotated marker allocation is unreachable on this
   parameter. No alternate marker is identified with i.

4. k1's four-port demand is emitted by
   `tail.rs::make_app_with_origins` (535–627) at the actual callee x. Its direct
   comparison with P0 starts with (empty, empty). At
   `constraints/machine/propagate.rs` (210–269), argument reversal preserves
   that empty pair and both return ports retain it. In particular, the source
   route from P0 to k1's returned Function P1 supplies **no right i-POP**.
   This is a local derivation of emitted comparisons; it does not certify every
   replayed bound or claim that a particular stored bound passed projection.

5. k2's callee is k1's `Expr::App`. The actual lookup
   `tail.rs::local_callee_def` (844–849) accepts only `Expr::Var`, so k2
   acquires no cb call predicate. Independently, cb's call predicate is empty:
   `lambda_annotation_predicate_constraints` (1581–1594) receives the empty
   outer `connection.subtracts`; `mark_lambda_param_call_predicate` (919–935)
   returns immediately for the empty predicate. The direct P1/k2 comparison
   again starts with the empty pair. Return-Effect decomposition then exposes
   PUSH_i(q) to c2; Stack normalization (propagate.rs:11–24) prefixes the PUSH
   to the **left** weight. Return-Value decomposition exposes Unit's
   NonSubtract wrapper to v2; normalization (26–37) prefixes POP_i to the
   **left** weight. Neither operation produces a right POP on the comparison
   of P1 with the call demand. k2 transports c2 and k1's evaluation Effect to
   e2 through the actual forwarding constraints (tail.rs:615–627).

The first proposed same-ID producer fails at step 2: the inner POP is on Unit,
not on the Function returned by k1. The actual constructor's immediate-effect
subtraction list prevents the attempted ancestor hoist. Step 5 then prevents
recovering that POP by looking up cb through the second application's callee.
Function reversal does generate right POPs **when its incoming left weight
already has POPs**, but that premise is absent on these direct P0/P1 call
comparisons. Its general transition rule is not evidence of the missing source
edge.

This rules out the named direct constructor route to the §4 discriminator. It
does **not** prove that no weighted same-i bound can arise under all Oracle
source histories, nor provide a theorem about all lower-bound tables for A.
An additional replay/extrusion derivation could only be evidence if it names
its actual producer and preserves this ledger. Merely finding bound storage
with two endpoint shapes would not establish that incidence.

## Export and delayed-use boundary

`compact/collect/mod.rs::compact_scheme_lower_bounds` (848–877) reads only
lowers returned by `scheme_projectable_lowers_in_scope`.
`constraints/structural_kernel/access.rs` (862–892) skips Excluded records and
passes Included or Unclaimed records. For a supplied lower,
`compact_lower_bounds_from` (898–920) really reads only its left weight.
Positive Function compaction (`collect/type_nodes.rs:17–23`) passes that weight
to results and resets arguments. These are confirmed source operations; they
do not manufacture a lower with the missing same-i right component, or prove
its inclusion in this exact source's scheme projection.

The earlier A dump retains `'b#0[tick]` on f's result Effect. That is a bounded
exported observation, consistent with the direct k2 Effect route above. It is
not the surviving joint replacement for an omitted right component: no authentic
such B has been established here. No inference from the retained PUSH to check
discharge or failure is made.

The actual selected-stack fresh-use operation in
`instantiate.rs::instantiate_scheme_parts` (620–647) clones recursive bounds
and the predicate with one shared fresh-ID map, then
`wrap_predicate_with_stack_pops` (770–787) inserts root POP_i'^MAX. This confirms
the owner of a possible later discriminator, conditional on an actual scheme
use selecting i. **A supplies no later use of published f.** Its k2 occurs in
f's body before publication and is not such an instantiation. There is therefore
no actual later instantiated call/output in this exact source to which the
omitted-right claim can be attached. The root operation cannot be retrospectively
inserted into A's prepublication cb comparisons.

Yulang3 does not supply that missing bridge either. Solver bytes are unchanged
between the assigned source baseline and inspected HEAD (the targeted Git diff
was empty). `candidate_effect.rs::candidate_formal_annotation` starts at
Negative polarity (1073–1091); `candidate_formal_pair` preserves that polarity
through results (1034–1052). The nested concrete row reaches a Negative
position and its initial guard rejects it (1035). These owners do not construct
Oracle's authentic i at this source boundary. This is a current source owner
gap, not an approved source restriction or permission to enable it.

## Result, independence, limits and resources

Result: a source-derived bounded obstruction to the attempted direct same-i
incidence, plus a syntactically absent postpublication f use. No authentic
included B with the requested right component was established, no exported
joint replacement was reconstructed, and H remains OPEN. This is not a yes/no
resolution over H's original source domain.

The inspected Oracle implementation is independent of a worker-authored toy
transition checker, but it is the implementation whose correspondence is being
examined; its own source and dump cannot certify universal hygiene. The local
derivation and the prior characterization share the primary-supplied source
revision and annotation qualification. Executable/source build correspondence
was not independently reconstructed here. No new reference interpreter,
mutation, seed, range or enumeration was used.

Static commands: bounded `sed`/`rg` owner reads, `cat` of assigned authority and
rules, `sha256sum` dependency snapshots/recheck, read-only branch/HEAD/status,
and `git diff 35e88c8113c9c6516e260170503bea753e4ede6
0971cf7a921cd1aef92b8e7bcdf3800654dc63c4 -- crates/yu-solver` (empty).
The nonexistent guessed Oracle `src/session` search target was reported by rg
and not used as evidence. Some combined initial captures were truncated;
the exact owners used above were reread in narrow complete sections. Searches
are incomplete outside the named constructor/use/projection cone.

Budget: static source inspection only, serial lightweight shell processes;
zero Oracle invocations, builds, tests, Cargo processes, instrumentation,
parallel heavyweight processes or measurement samples. CPU time, peak RSS and
total reasoning wall time were not measured. No timeout or resource failure
was observed. The write set is the sole leased Markdown note. Writes stop at
submission; independent review is pending.

Unverified scope: complete source/replay/extrusion closure and projection
inclusion for A; generalizer/pruner/finalizer joint replacement; a future
same-use provider and delayed generalized consumer; independent same-family
retention; symbolic source tails; rejection/safe nonpublication; H, complete
Call, soundness, principality and production/cutover.

Recommended next action: the primary should assign the owning source-generation
lane to supply a single authentic **postpublication scheme use** and its exact
same-ID argument-reversal producer before more compaction algebra. That requires
a separately scoped source variant or instrumentation lease; this note supplies
neither. Keep H OPEN with that missing source/use owner.

## Frozen dependencies

SHA-256 values pin inspected bytes. No dependency was edited by this leaf.
Oracle revision identity is inherited from the primary, not independently
revalidated by Git here. The generalized observation proof was already modified
when this job began; its precise read snapshot is listed rather than silently
claiming committed baseline equality.

| Dependency | SHA-256 |
| --- | --- |
| Global H note | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| Generalized observation proof | `56ea872aa52e8f139a9be8aaeedfa6f47c1002720ef35948b3145c197c02e37b` |
| Three-run A/B/C attack note | `faba92bc95ca1a46f0b45c4278a5a21a5836f3fbc62045b05227e6d3481176e9` |
| Top-level principles | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Annotation policy | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| Concrete implementation gate | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| Oracle annotation/constraints.rs | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| Oracle lowering/expr/tail.rs | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| Oracle lowering/expr/lambda.rs | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| Oracle lowering/name_ref.rs | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| Oracle lowering/pattern.rs | `b56344fca6fd964d1429084adaaf3a11d8603f7fb71d48d71d60d30ec4156126` |
| Oracle constraints/machine/propagate.rs | `8695fa5d7dfac805cd7d66e9e0760c8c298002b952b0cd8a43dcd1f8eb6f7086` |
| Oracle constraints/structural_kernel/access.rs | `ad90bc1444be22df6080c7131ef49fedace884178c375af84ecb09416b38740f` |
| Oracle compact/collect/mod.rs | `828fa02521e2426297a9369df2fd9ef1560b7403a668ddfe881063ef16bdfd40` |
| Oracle compact/collect/type_nodes.rs | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| Oracle instantiate.rs | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |
| Oracle constraints/mod.rs | `ad3cf5fd60462cb1a08ef1a5d6fc57c4fd640148597bc3b331d09729616d8392` |
| Y3 candidate_effect.rs | `ae98dd92e2c8eb7e538c4450f250826bf83872f3bb62f1de1b014406313634df` |

## Commit packet

- Exact leased/change path: `notes/progress/2026-10-11-oracle-weight-source-bridge.md`; frozen, writes stopped at submission.
- Baseline SHA: `0971cf7a921cd1aef92b8e7bcdf3800654dc63c4`; solver baseline `35e88c8113c9c6516e260170503bea753e4ede6`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1` supplied by primary.
- Changed dependency hashes: none authored; exact snapshot above, preexisting generalized-proof modification acknowledged; dependency equality must be rechecked by the primary before integration.
- Review status: unreviewed bounded research correspondence; no independent review, H closure, source-qualified counterexample or production conformance claimed.
- Checks already run: narrow source/authority reads, read-only source-baseline diff (empty), dependency hashes/recheck, leased-note whitespace/link/fence inspection; no Oracle, builds or tests.
- Proposed one-line research checkpoint: `research: trace nested Oracle weight incidence to missing fresh-use producer`.
- Shared-record deltas intentionally left for primary/curator: record immediate-effect subtraction ownership and App lookup barrier; record absence of postpublication f use in A; preserve included same-ID B and actual fresh-use consumer as OPEN source premises, alongside Y3 negative-formal owner gap. No shared records, authority, manifests, lockfiles or question-board bundles changed.
