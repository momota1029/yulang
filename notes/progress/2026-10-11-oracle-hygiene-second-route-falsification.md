# Oracle hygiene: tuple predicate aggregation as a second source route

Date: 2026-10-11
Status: frozen, unreviewed bounded source derivation; original H remains OPEN
Claim class: candidate source plus conditional constructor-path exclusion, not executed source qualification or a hygiene counterexample
Yulang3 baseline: `39968b554f3d4a71cece82e61188235a8559d706`
Oracle revision supplied by primary: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle inspected source: `/tmp/yulang2-oracle-read`
Exclusive write lease: this note only; leaf, no delegation or Git mutation

## Objective, authority and previous exclusions

Seek a second source-owned nonterminal residual carrier after exact A's inner
Unit-return route failed to supply the requested same-ID incidence. Retain H
exactly as frozen in [global effect hygiene](../theory/2026-10-11-oracle-global-effect-hygiene-proof.md)
§1: every successfully lowered source, composed-negative occurrence, original
scope/binders, actual instance, provider and call/output route; subtraction is
instance-local, independent same-family contributions survive, symbolic tails
remain connected, actual future lowers encounter retained checks, and correlated
lineage survives copying and publication. Incorrect lowers require authentic
checking and safe nonpublication. No original quantifier is narrowed here.

Authority is [annotation effect hygiene](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–5, [concrete annotation implementation](../design/2026-10-10-concrete-effect-annotation-implementation.md),
and [top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md)
§§1–5 and Authority and integration. Composed polarity, local subtraction,
resolved family identity and symbolic flow retain the selected meaning. The
withdrawn callback scheme supplies no expected output.

Excluded repeated methods: exact A and its Unit POP/
[App-lookup barrier](2026-10-11-oracle-weight-source-bridge.md), the recorded
direct/through/route probes, and the direct callback's
[projection-record audit](2026-10-11-oracle-direct-projection-owner-audit.md).
No new output-only probe, numerical stack-ID inference or transition-assuming
checker is used. This pass instead inspects **Tuple's aggregate predicate
constructor**, which the bare Function route does not use.

## Candidate source and fixed identities

This compact candidate uses one extra Unit component so the carrier is a Tuple
rather than a parenthesized Function:

```yulang
pub act tick:
    pub ping: () -> ()
my boxed(pair: ((() -> [tick] ()), ())) = pair
my provider() = tick::ping()
my consume (cb, ()) = cb ()
my observed() = consume (boxed (provider, ()))
```

This is not an executed or accepted minimal program. It is structurally reduced
for the new mechanism: a one-child parenthesized type is unwrapped, so removing
the second component returns to the already-recorded bare Function case.
The actual spelling is supported by the existing type parser's parenthesized
TypeExpr list and comma separators (`parser/src/typ/parse.rs:36–43,409–429`)
and `AnnTypeBuilder::build_type_paren_group` (annotation/builder.rs:262–280).
Successful parsing, name resolution, completed lowering and accepted publication
of these complete bytes were not independently evaluated. Constructor claims
below are conditional on that explicit AST qualification.

Fix a to boxed's first tuple component's `[tick]`, sigma to boxed's body,
pair to its formal Value x, i to a's primary paired-constructor fresh ID, and q
to that constructor's effect coordinate. Let F_i be the primary positive
callback companion, T_i = Tuple(F_i, Unit) its positive annotation Tuple, b the
actual boxed use in observed, p the provider supplied in b's first tuple item,
c the callback component extracted by consume's pattern, and k the actual
`cb ()` call in consume. All names describe one candidate source lineage.
Neither p, c nor k is independently selected. There is no symbolic source tail
or separately emitted same-family sibling in this candidate; later provider
independence is a required unproved part of its proposed discriminator.

## New constructor path: a POP on a nonterminal Tuple

Oracle paths in this section start at `crates/infer/src/`.

1. `annotation/constraints.rs::lower_value_bounds` (335–350) constructs the
   Tuple companions and **extends output_subtracts from each component**.
   Lowering F_i (363–389,424–470) supplies PUSH_i(Set(tick)) on its latent
   result Effect and POP_i with the tick filter on its Unit result Value.
   F_i also returns that POP_i in `output_subtracts`. The Unit component adds
   no predicate. Thus this Tuple's connection returns exactly that primary
   POP_i predicate, rather than the empty outer immediate-effect list in A.

2. `lambda.rs::lambda_annotation_predicate_constraints` (1581–1594) returns
   the connection's subtraction list for this non-Effectful Tuple.
   `lambda_parameter_output_predicate_constraints` (1571–1579) clears the list
   only for an `AnnType::Function`; a Tuple falls through and retains it.
   `connect_lambda_pattern_annotation` (1282–1283) stores the two lists
   separately. This is an output predicate supplied by annotation construction,
   not a cb call-induced latent predicate.

3. boxed's body is the actual pair reference. Its formal is monomorphic:
   `pattern.rs:242–281` initializes `Def::Arg` with no scheme, and
   `tail.rs::instantiate_local_value` (855–859) returns x directly.
   `wrap_lambda_param` (946–974), called by the defined-body wrapper
   (`lambda.rs:852–866`), combines the annotation output predicate with its
   actual frame (`tail.rs:1058–1077`). `lambda_output_predicate_vars`
   (1092–1112) wraps both body Value and Effect in that POP_i.
   The wrapper owner, `expr/constraints.rs:137–145`, uses `Pos::NonSubtract`.
   Therefore the returned Value route genuinely emits
   `NonSubtract(Var(x), POP_i with tick filter)` from these constructors.
   x already receives T_i from the primary annotation connection
   (annotation/constraints.rs:124–137).

4. Defined skeleton predicate wiring is consistent with that construction:
   `lambda.rs:1187–1237` obtains the same annotation predicate, wraps both
   current output coordinates and constrains them to the layer output. It
   does not require a call to pair or its callback component.

The nonterminal carrier is therefore a **source-emitted POP on the returned
Tuple coordinate**, conditional on the explicit candidate AST and normally
completed constructors. Unlike A's terminal Unit route or direct's cleared
bare-Function output predicate, it can reach structural Tuple/Function
decomposition. Public/erased callable-upper construction traverses Tuples too
(annotation/constraints.rs:155–211; lambda.rs:1284–1307,1458–1501) and can
allocate auxiliary IDs. Those IDs are not i and no numeric uniqueness is
assumed.

## Conditional exclusion at the direct positive compact path

The candidate initially aimed to retain i in the exported returned callback and
observe its fresh-use root POP at k. The actual positive collector defeats this
particular retained-PUSH route before such a conclusion can be drawn.

For a compact visit carrying exactly boxed's output POP_i to its original T_i
lower, `compact/collect/type_nodes.rs:84–91` passes the carried weight into
each Tuple component. Positive Function collection (:17–23) resets argument
weights and sends that POP to F_i's result Effect. Its Stack constructor
(:97–105) prefixes its own PUSH_i before the carried weight:

```text
tuple output weight:             POP_i
callback result Effect weight:  PUSH_i(Set(tick)) compose POP_i
active i stack after compose:   empty
```

This is the real order: `stack_weight.union(&weight)`, where
`poly/src/types.rs:402–410` defines union as compose. `append` (:485–495)
then `push_pops` (:540–557) removes the one matching active stack entry.
The tick filter persists; it is not a same-family contribution deletion.
Positive NonSubtract compaction (:92–96) adds F_i's Unit-return POP separately,
which does not recreate an active PUSH at q.

**Conditional local conclusion:** on this direct T_i compact path, the intended
original active i-PUSH at the returned callback's latent q is canceled by the
aggregate output predicate. That occurrence cannot itself supply the live
covariant-PUSH selection premise. `generalize/core/stack_ids.rs:76–88,176–180`
requires a nonempty entry.stack at a selected covariant coordinate. This is a
constructor-path exclusion, not an assertion that i is absent from every actual
installed scheme: other included records, recursive/role paths, cleanup and the
encountered-All selector (`generalize/mod.rs:867–888`) need their actual inputs.
No global no-i theorem or post-use cancellation witness follows.

## First missing premise and stop

The earliest unestablished operational premise is which returned-Value lower
records the actual scheme query projects for this candidate and what weights
those records carry. `compact_lower_bounds_from` (collect/mod.rs:898–920) sees
only the retained left component. Before that,
`compact_scheme_lower_bounds` (:848–877) reads actual projection decisions.
The production evaluator (`constraints/proof/mod.rs:9995–10038`) returns
Unclaimed for absent support/formula, rejects mismatched ledgers, and evaluates
the qualified case when both are present. Syntax, a NonSubtract wrapper and
bound storage do not determine those ledgers.

The lower owner (`machine/bounds.rs:630–731`) extrudes and checks filters,
may subsume a lower, admits its projection index, and registers derivations.
`register_lower_projection_delta` (:2476–2529) depends on actual claim parents
and whether the support ledger already exists. This pass has not evaluated
those records or the full replay closure. The general permission to evaluate
deterministic code does not justify assuming its concrete record/formula state.
The stop condition is met here.

The downstream source **does designate** a real later supplied provider and
consumer: expression tuples form actual tuple Value coordinates
(`expr/block_local.rs:9–65`), consume's tuple pattern emits matching positive
and negative tuple constraints (`pattern.rs:921–954`), and the ordinary app
constructor emits demands and joins actual call/evaluation Effects
(`tail.rs:535–627`). Top-level scheme instantiation uses the installed scheme
(`analysis/session/instantiate.rs:449–520`); selected IDs are consistently
freshened and root POP(MAX) inserted (`instantiate.rs:620–647,770–787`).
These owners identify what would consume the output. They do not establish a
selected original i, the actual use map, provider support on q, independent
attachment, or the final output row for these unexecuted bytes.

## Result, coverage and next action

Bounded result: Tuple aggregation creates an output predicate on a nonterminal
carrier without local callback activation. Its direct positive compact path
cancels the same constructor's active latent PUSH. Thus this new route is not
an established fresh-i/root-POP hygiene falsifier. It is not excluded by Unit
terminal shape; its missing evidence is actual scheme-projection/selection and
provider/output correspondence. No complete published scheme, actual failure,
independent contribution loss or H counterexample is claimed. H and all broader
Call/soundness/principality/production gates remain OPEN.

The method is static owner inspection and one explicit constructor-path
calculation. There is no independent executable oracle, supplied-transition
checker, seed, numerical range, mutation run or enumeration. Oracle source is
the implementation under examination; selected authority independently fixes
the required policy, but source inspection cannot certify its global behavior.
Prior dump observations are used only to avoid duplicate attacks. They supply
no acceptance or raw ID for this candidate.

Commands used bounded `rg`, `sed`, `cat`, SHA-256 snapshots/rechecks and
read-only HEAD/status. Initial oversized captures were truncated; the decisive
Tuple, predicate, wrapper, collector, composition and projection sections were
reread narrowly. Guessed nonexistent parser/test/proof paths were corrected
without relying on their output. Coverage is incomplete outside this owner cone.
No Oracle invocation, test, build, instrumentation, compiler edit, Git mutation,
delegation, heavy process or performance sample occurred. Shell reads were
serial lightweight processes. CPU/RSS and total reasoning wall time are unknown.
Only this leased note was written; writes stop at submission. Independent
review has not occurred.

Recommended next action: return this aggregate-constructor distinction to the
constructive owner and have it derive the candidate's **actual projection
record/formula slice** before another source variant. The direct-path calculation
is already discriminating; another surface probe would leave the same operational
premise untouched. Any owner instrumentation requires a separate explicit lease.

## Frozen dependency snapshot

SHA-256; Oracle paths are relative to `/tmp/yulang2-oracle-read/crates/`.
No dependency was changed by this leaf. Source revision identity is supplied by
the primary. The snapshot pins decisive inspected bytes, not all transitive
dependencies or proof of complete source/binary correspondence.

| Dependency | SHA-256 |
| --- | --- |
| Y3 notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| Y3 notes/progress/2026-10-11-oracle-weight-source-bridge.md | `009cf138309389c445e2ffb8f2acb2bc143b38798e032641388d21a600342bb0` |
| Y3 notes/progress/2026-10-11-oracle-direct-projection-owner-audit.md | `4ffba49b46626787f0c5cde12e72d94996f7bf68cf18c0dbcb7cadc923f75c59` |
| Y3 notes/design/2026-10-10-annotation-effect-hygiene-integration.md | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| Y3 notes/design/2026-10-10-concrete-effect-annotation-implementation.md | `3a3186723cd93edd2f767a7e4a481cb6dbed701fc749502e640071f65a4d89ae` |
| Y3 notes/design/2026-10-11-yulang-inference-top-level-principles.md | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |
| Oracle infer/src/annotation/constraints.rs | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| Oracle infer/src/annotation/builder.rs | `baad6a964909eaee3e7822aa5445dca8cd2f70185bd5a1f2157e878a512ddf7b` |
| Oracle parser/src/typ/parse.rs | `70a9b0e084ac8b84095d5d9ee450cd6020891c5583f294a83fc5134ec75bdd88` |
| Oracle infer/src/lowering/expr/lambda.rs | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| Oracle infer/src/lowering/expr/tail.rs | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| Oracle infer/src/lowering/expr/constraints.rs | `2800250aa516c519d91aa11b0d46455f0a86f14a009be3588c7e039d2c5cbe20` |
| Oracle infer/src/lowering/expr/block_local.rs | `661386fe559d8e207a9597962cfee3c11f05f21aa2888e22b2c0143825051898` |
| Oracle infer/src/lowering/pattern.rs | `b56344fca6fd964d1429084adaaf3a11d8603f7fb71d48d71d60d30ec4156126` |
| Oracle infer/src/compact/collect/type_nodes.rs | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| Oracle infer/src/compact/collect/mod.rs | `828fa02521e2426297a9369df2fd9ef1560b7403a668ddfe881063ef16bdfd40` |
| Oracle poly/src/types.rs | `9211e62291b82e71e1b78763b83fe9f1d81e0fe4396d9e12d42e9a4a9b13b47c` |
| Oracle infer/src/constraints/machine/bounds.rs | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| Oracle infer/src/constraints/proof/mod.rs | `bc0f3fbcf8f5ed01245e74283d3fd9cb13aa1713aff252a1847fde76b11b8e03` |
| Oracle infer/src/generalize/core/stack_ids.rs | `adb9cd35d483af62ea0c3ebc572b9a0535761f3bfb99aedad49b371833b95f8f` |
| Oracle infer/src/generalize/mod.rs | `03bfda4e4997347b59483de96eca652b67477639fc363e0890d546d2cf36fcef` |
| Oracle infer/src/analysis/session/instantiate.rs | `bf21175f47df78f35f2070fea51b3483d59a91ac4a606bace9e24f32878c2d19` |
| Oracle infer/src/instantiate.rs | `876ede0627a1ac64b155d3d7896a386ac1fa81d8814c40c77a0f3893128a9b2c` |

## Commit packet

- Exact leased/change path: `notes/progress/2026-10-11-oracle-hygiene-second-route-falsification.md`; frozen, writes stopped at submission.
- Baseline SHA: Y3 `39968b554f3d4a71cece82e61188235a8559d706`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1` supplied by primary.
- Changed dependency hashes: none authored; decisive snapshot above, unchanged at final recheck. No production dependency was edited.
- Review status: unreviewed candidate-source/conditional-path research checkpoint; no accepted source, independent review, H closure, counterexample or implementation authority claimed.
- Checks already run: narrow static source reads, dependency snapshot/recheck, leased-note links/fences/whitespace; zero Oracle executions, tests or builds.
- Proposed one-line checkpoint: `research: derive tuple predicate carrier and direct compact cancellation`.
- Shared-record deltas left for primary/curator: Tuple aggregation preserves the annotation output predicate that bare Function clears; its direct compact path cancels active i; actual projection/formula state, installed selection and same-lineage provider/output remain OPEN. Do not promote this candidate to an accepted source or H counterexample. No shared task/index/theory/authority/question record changed.
