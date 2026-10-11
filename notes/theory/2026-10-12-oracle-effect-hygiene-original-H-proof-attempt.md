# Original Oracle effect-hygiene H: direct proof attempt and projection obstruction

Date: 2026-10-12
Status: frozen and independently reviewed; original H remains OPEN
Claim class: source-to-consumer obstruction, not an established theorem, conditional closure, or counterexample
Yulang3 baseline: `37a107cfbf642da80ebb4950fad17dc8f6c788e9`
Oracle baseline: `a58eefc31e22141574b6f20c6a5748151c6d79f1`
Oracle locator: `/home/momota1029/rust/yulang2-oracle-capture`
Exclusive output lease: this file only; leaf, no delegation

## 1. Objective, authority, and frozen statement

Attempt the original universal H by induction over the actual paired annotation,
Function, application, handler, residual, generalization, and instantiation
constructors. Do not replace it with the direct-formal singleton or with a
theorem whose hypotheses assume attachment-to-Call correspondence.

The frozen statement is the H in
[Oracle global hygiene](2026-10-11-oracle-global-effect-hygiene-proof.md) §1:

> For every Oracle source program P in the original successfully lowered source
> domain, every successfully lowered composed-negative concrete annotation
> occurrence a, its original lexical scope sigma and binders, every actual
> copy/instantiation u of that occurrence, and every actual function call/output
> route k involving that occurrence, subtraction authorized by a removes only
> the contribution attached to that exact instance on that route. An independent
> contribution at the same resolved family survives that subtraction. Symbolic
> annotation tails remain connected; every current and future concrete lower
> reaching the relevant receiver encounters the actual retained check. The
> occurrence, attachment, scope, provider/call binder and correlated residual
> lineage remain appropriately identified through actual copying and
> generalization, up to the actual consistent renaming of a fresh use.

The quantifiers, successful-lowering domain, original scope/binders, actual
provider and complete output routes are unchanged. Nested Function arguments
reverse polarity and results preserve it. Concrete identity includes resolved
family operands. Ignoring annotation variables when collecting concrete atoms
does not disconnect or empty their tails. An invalid later lower requires an
authentic check/error and safe nonpublication, rather than an accepted typing.
Normal completed operations and fresh allocation without ID exhaustion are
shared operational assumptions, not attachment, replay, or generalization
correctness hypotheses. Arena-local numeric equality is not cross-arena identity.

Governing sources are
[annotation policy](../design/2026-10-10-annotation-effect-hygiene-integration.md)
§§1–4,
[attachment/admission](../design/2026-10-10-contextual-attachment-admission-design.md)
§§3–6,
[selected residual lineage](../design/2026-10-10-contextual-residual-lineage-selection.md),
[complete Call](../design/2026-10-07-complete-call-contribution-definition.md)
§§2–5, and
[top-level principles](../design/2026-10-11-yulang-inference-top-level-principles.md).
In particular, an actual Call includes callee computation, the whole argument,
dispatch to the actual returned provider and entry, and the original return and
future interface. An arbitrary four-port comparison is not a substitute for
that operation. Separate residual constructor lineages remain required for the
successor; Oracle key reuse is reference evidence, not authority to merge them.
The withdrawn callback output is not used. No new admission rule, source
restriction, rollback goal, or representation decision is adopted.

The existing local retained-check activation and per-use renaming lemmas in
the input note §§3–4 are reused with their exact limits. Re-reading those owners
does not constitute new proof progress. This packet neither proves complete
Call, global soundness, nor required principality separately.

## 2. Frozen source and proof method

Oracle HEAD matches the assigned revision, but the capture worktree has seven
tracked modifications, including `compact/collect/{mod,type_nodes}.rs` and
`lowering/expr/tail.rs`. Every Oracle source excerpt used below was obtained
with `git show a58eefc31e...:<path>`, not from those live files. Neither capture
hook nor other uncommitted instrumentation supplies a premise. The six governing
Y3 documents in §8 were byte-equal to the primary baseline when checked.

The induction attempts to carry the actual annotation occurrence and arena ID,
the paired four-port graph, the actual lexical binding/call, and each actual
residual derivation together. It follows emitted constraints into their owning
consumers; it does not attach a separately selected output witness afterward.
The steps below establish source wiring or identify an unproved preservation
step. They are not an assertion that each step already preserves H.

Oracle paths and line numbers below refer to the frozen revision.

## 3. Annotation, Function, and actual application steps

`crates/infer/src/annotation/constraints.rs:299–389::lower_value_bounds`
recurses on the actual annotation. For a Function, it constructs:

```text
positive: Fun(param.neg, arg_eff.neg, ret_eff.pos, NonSubtract(ret.pos, own predicates))
negative: Fun(param.pos, arg_eff.pos, ret_eff.neg, ret.neg)
returned output_subtracts: this Function's ret_eff.subtracts
```

Tuple construction accumulates its children's returned predicates. Function
construction retains nested graphs but does not accumulate all descendant
predicates into the enclosing Function's returned list. Thus the naive induction
invariant "the enclosing binder predicate contains every negative descendant"
fails at the actual Function constructor. The appropriate syntactic object to
follow is the complete paired graph plus its immediate returned predicate.
This correction does not supply a semantic attachment-to-call lemma.

`lower_ret_effect_bounds` at 424–470 installs the boundary graph, actual stack
facts, positive wrapper, negative filter, and returned predicate. Its symbolic
tail-only and wildcard branches are distinct. `lower_arg_effect_bounds` at
393–422 connects ordinary concrete argument-effect lowers instead of promising
the same stack constructor in every negative position. The previous source
inventory's signature-lowering cases remain part of the universal domain; this
packet does not replace them with the paired-parameter path.

`lowering/expr/lambda.rs:1244–1341::connect_lambda_pattern_annotation` consumes
the actual connection and retains the call/output predicates, public/erased
upper views, and local effect view. At 1190–1237 the defined skeleton wraps
both the actual current result Effect and Value with the frame's output
predicate. No predicate is applied to a separately chosen result coordinate.

`lowering/expr/tail.rs:535–624::make_app_with_origins` forms a demand at the
actual callee value, with this argument's Value/Effect and this application's
return Value/Effect. It forwards callee evaluation Effect and invocation return
Effect to this application's Effect. `local_callee_call_projection` at
691–707 and `local_callee_def` at 844–850 recover the lexical predicate only
for the actual resolved `Expr::Var`. A returned application callee receives
no guessed lexical predicate. Its nested latent Function ports must therefore
be justified by their actual graph propagation. The graph alone has not yet
established the complete original provider/Call meaning required by H.

`constraints/machine/propagate.rs:210–263` emits all four Function comparisons:
Argument Value and ordinary Argument Effect use `swapped`; both results retain
the incoming context. The pure-argument Effect branch uses `both_from_right`
with the actual return-effect target. `ConstraintWeights` at
`constraints/mod.rs:3566–3607` implements these distinct operations and ordered
replay composition. The established ID-local algebra permits no inference that
equal-family source contributions have the same attachment. It also does not
justify independently selecting witnesses for the duplicated `both` flow.

## 4. Handler formation and residual installation

The actual handler owner is `lowering/control.rs:922–1021`, not an assumed
handler relation. `lower_catch_with_scrutinee` forms its row from the actual
handled arms and the actual scrutinee. Handler arm bodies flow separately to
the handler result. A complete handled set uses the handler result Effect as
the row tail; an incomplete set retains a separate rest coordinate and forwards
the scrutinee Effect. `subtype_scrutinee_effect_to_row` uses the actual
`LocalEffect::Stack` view, constrains the public slot, and sends the stack's
inner variable and weight to the same row. This is genuine source wiring;
it is not a proof that every operational contribution has its intended view.

`constraints/row_effect.rs:87–230::add_effect_row_upper_bound` has weighted and
unweighted branches. In the weighted branch it checks the incoming filter,
retains concrete heads, and creates or reuses gamma keyed by source coordinate,
retained resolved families, and residual weight. It records the actual row
derivation, then sends both equations to `enqueue_row_derived_subtype`:

```text
source <: Row(retained heads, gamma)                 [empty context]
gamma  <: this exact tail                          [residual context + right context]
```

This retains reverse feedback and each actual projection at installation.
`subtract_row_items_from_left_stack_weight` at 1190–1216 transforms each
existing ID entry; it does not allocate a new attachment merely because a
family matches. Nevertheless gamma reuse is not a proof of joint exact-image
congruence of the original derivations. The retained derivations cannot be
collapsed into one independently chosen marginal residual.

The equation installation is not complete replay by itself. Its actual entry
owner is `constraints/machine/entry.rs:1617` onward. Canonical duplicate
admission retains a row derivation but does not requeue an already known
constraint. `canonical_subtype_constraint` at 1092–1118 drops identical Var
endpoints before examining the contextual weight. Those omission paths need
their own H preservation argument; neither stored derivations nor the local
registered-filter lemma supplies it. No omitted self edge is declared harmless
here merely because it is an ordinary scalar tautology.

## 5. Generalization reaches an exact earlier consumer than ID pruning

The live-to-scheme route is an actual source consumer.
`lowering/expr/tail.rs:944–1019::generalize_local_binding` drains pending
selection and subtype work, computes non-generic variables and the selected
boundary, constructs a generalized compact root, captures witnesses, finalizes
the scheme, and installs it on this local binding. It keeps a live slot instead
of a scheme while the indicated method selection remains pending. This is not
permission to assume that the completed scheme preserves H.

For module roots, `analysis/session/generalize.rs:580–602` calls
`compact_type_var_recording_merge_constraints_for_scheme`; the prepass at
17–69 actually consumes that compact result. The final cleanup/generalization
owners are reached at 476–549. The projection is therefore not test-only or
an unused audit surface.

The first unclosed source/consumer bridge identified on this generalized-output
route is **source contribution independence to projection claim accounting**:

1. `constraints/machine/bounds.rs:630–730::add_lower_bound` installs the actual
   extruded lower and calls `register_lower_projection_derivation` when its
   provenance changes. The reused retained-filter activation lemma covers
   registered checks, not the later projection decision.
2. `register_lower_projection_derivation` at 2332–2370 links actual qualified
   parent claims and calls `register_lower_projection_delta`. The latter at
   2476–2568 bootstraps/classifies carrier supports and installs their clauses.
3. `projection_carrier_is_independent` at 2689–2717 classifies a constraint
   origin by absence of a matching claim producer, and a structural/replay/row
   carrier by absence from the qualified-parent index. Other listed carriers
   are accepted as independent. **This is a concrete operational classifier;
   semantic independence from the annotation instance and its actual Call is
   not a displayed premise of that classifier.**
4. The live coverage states have actual constructors:
   `row_effect.rs:490–540::register_unweighted_row_reduction` registers a claim
   for the original producer and reduced upper, inserts its live coverage
   state, and records the reduction. `enqueue_initial_unmatched_reduction_subtype`
   at 551–570 attaches that claim to the actual row-derived constraint.
   `unweighted_row_reduction_routes_for_new_lower` at 362 onward handles
   subsequently admitted source lowers. This establishes construction and
   activation of the claim mechanism, not its semantic adequacy for H.
5. `constraints/proof/mod.rs:9975–10129::project_lower` validates the ledger and
   evaluates its actual formula graph. `CpkProjectionEvaluator` at
   11632–11765 interprets standalone, unary, and replay-conjunction clauses.
   At 11879–11918 it excludes a claimed root whenever its live coverage set
   is nonempty and includes an Independent support. A cycle encountered by
   `enter` at 11920 onward returns Excluded for that recursive visit.
6. `constraints/structural_kernel/access.rs:862–899` skips every Excluded
   lower. `compact/collect/mod.rs:848–884::compact_scheme_lower_bounds` then
   extracts only `entry.bound.clone()` from the included entries. The actual
   compact consumer does not carry their projection evidence onward with
   each bound. No omitted concrete lower reaches `compact_pos_row_item`
   merely because that latter constructor preserves any concrete lower it
   does receive.

The exact missing premise is this: for every original source P, occurrence a,
scope/binders, actual use u, actual complete Call/output route k, and independent
same-family contribution, the actual carrier and qualified-parent constructors
must leave that contribution represented in the exported coupled observation
when a projection claim excludes a lower. Any replacement representation must
retain the same whole-operation evidence, provider and shared residual
dependencies before observations or future uses are chosen. A nonempty live
row-reduction coverage set must justify discharging the covered route's entire
relevant obligation, including future lowers and latent outputs, rather than
merely justifying its internal ancestry classification.

This is an obligation, not an added assumption of H. No source-to-bound,
attachment-to-claim, or source-to-residual premise is imported to make it true.
In particular, `SchemeProjectionProofSupport::Independent` is not defined to
mean H-independent by fiat. The missing implication is at the actual bound
carrier/claim constructors and their exclusion consumer. Checking their internal
formula consistency is insufficient to establish it.

The original input note already left the global projection/generalization
premise open. The narrower owners above localize where to investigate that
same premise; they do not discharge it or establish that it is false. Earlier
live replay omission and gamma-congruence seams in §4 are also unclosed. Thus
"first" here identifies the first missing source-to-classifier bridge on the
generalized-output route, not a claim that all preceding semantic cases passed.

## 6. Why freshening cannot finish this induction

The downstream transformations make it impossible to finish with the existing
copying lemma alone:

- `generalize/core/stack_ids.rs:23–49,76–179` selects stack IDs from covariant
  live PUSH occurrences at quantified coordinates, with Function polarity.
- `generalize/mod.rs:177–238` removes IDs outside that selected set; 867–888
  separately extends declared-All quantifiers. `generalize/core/prune.rs:504–557`
  recursively removes those entries from the compact graph.
- `compact/collect/type_nodes.rs:13–22,117–135` distributes carried context
  differently across positive and negative Function ports.
- `compact/finalize.rs:586–603,837–839` resets principal weights' filters to All.
- `instantiate.rs:770–787` adds quantified root POPs with count `u32::MAX`.

The established single per-use map proves consistent renaming of the scheme
graph supplied to it. It cannot restore a lower that scheme projection
excluded, prove a pruned ID dead, prove an erased filter equivalent to the
exported structure, or show that the new root POPs preserve the source's joint
observations. Parameterized families and nested latent ports remain in H;
their binder/ID census closure is not inferred from ordinary-child traversal.

The two attempted routes therefore stop for precise reasons. Predicate-only
source induction fails at the nested Function return described in §3. Following
the complete graph avoids that syntactic mistake but reaches the actual
projection classifier/exclusion and later cleanup with no source-qualified
discharge argument. Advancing from there by the renaming lemma would silently
assume the very bridge under investigation.

No source-qualified counterexample is produced. An Excluded record, discarded
ID, erased filter, or shared gamma can be valid if an independently established
discharge/equivalence argument applies. Conversely neither a stored claim nor
a successful clone proves such an argument. H is neither proved nor refuted.

## 7. Economy audit and one next action

The prior local/conditional attempts and this construction-directed attempt
leave the same original semantic premise open. Apply
`rules/compiler-engineering.md`'s economy audit before another equivalent proof:
attached-only subtraction and independent survival are A; intended ordinary
generalization/instantiation is A/B. They cannot be relabeled C to close H.
Recovering original annotation/call incidence from the projection classifier's
ancestry IDs would be D if formation already knew and discarded it. The actual
annotation, lexical call, handler, and row derivation constructors know their
operands; the needed semantic action of source contribution ownership on claim
coverage has not been established here. A proposed retained certificate would
need proof at those owners and primary approval if it changes architecture;
this note selects no new certificate or reconstruction layer.

One next action: assign a source-qualified proof or falsifier for the exact
conversion from `register_lower_projection_derivation` / row-reduction claim
registration to `CpkProjectionEvaluator::eval_root_coverage` exclusion, retaining
the original annotation instance, actual complete Call/output route, one
independent same-family contribution, and both current/future source lowers.
Use an actual lowered source derivation or actual constructor induction, not
another supplied-transition checker. Keep H and its implementation/cutover
gates OPEN.

## 9. Independent review and exact status

An independent `compiler_referee` review found no blocking, major or minor
findings in the frozen packet. It checked the original H statement against the
pinned source note, the source wiring and consumers in §§3–5, the distinction
between operational claim classification and semantic independence, and the
limits stated in §§6–7. The review found no proof, source-qualified
counterexample, or hidden added premise. H remains OPEN.

The review also verified all 16 recorded Y3/Oracle dependency hashes against
the specified immutable objects. It did not certify the whole compiler,
execute the source fixture, or establish source-to-projection preservation.
The next owner remains the actual constructor-to-coverage implication at
`register_lower_projection_derivation` and row-reduction claim registration,
through `CpkProjectionEvaluator::eval_root_coverage` and scheme observation,
for one authentic independent same-family contribution and current/future
Call output routes.

## 8. Checks, dependency snapshot, resources, and runtime

Only the exact leased note was written. Static `cat`, `sed`, `rg`, frozen
`git show`/`git grep`, read-only Git orientation/status, and Python SHA-256
comparison were used. A mistaken search for an `expr/catch.rs` file was corrected
to the actual `lowering/control.rs` owner. Initial batched policy captures were
truncated; decisive sections were read again narrowly. No Oracle execution,
build, test, probe, network request, model escalation, delegation, or Git
mutation occurred. The final note received whitespace/local-link checks.

Resource budget: one 45-minute static leaf; no CPU-intensive process, no heavy
verification, zero measurement samples. Lightweight read batches used at most
three shell processes concurrently; later frozen reads and hashing were
sequential. Aggregate CPU/RSS and whole-packet wall time were not instrumented.
Primary retains the single verification owner and all independent review.

Requested runtime: `gpt-6.1-sol` / `high`, normal prover leaf. Project config
registers the unpinned prover with normal Sol/high defaults; callable schema
contains prover. Observed effective model/effort: unknown; no runtime metadata
was supplied to this leaf. No claim of override success, reload, or Astra use.

SHA-256 of governing Y3 bytes, all equal to the pinned baseline at comparison:

| Path | SHA-256 |
| --- | --- |
| `notes/theory/2026-10-11-oracle-global-effect-hygiene-proof.md` | `6ac3f9665f89633adb4a7feacaee79abfddab693eed2c5078241e51df9545df1` |
| `notes/design/2026-10-10-annotation-effect-hygiene-integration.md` | `503b1aab4205d063d1ab9f97358e8b128f82ee2ff818ad7150d9c7dac284254a` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |
| `notes/design/2026-10-10-contextual-residual-lineage-selection.md` | `d5c46b74d678028046bdfa0f7fd2b71bb2abfb112987000fe43e0fa5875d5d98` |
| `notes/design/2026-10-07-complete-call-contribution-definition.md` | `4c83a095dce3636ada842bfc32c18cf0ef598db0e361861fb8e659745b74411e` |
| `notes/design/2026-10-11-yulang-inference-top-level-principles.md` | `edb03dfc387ec98b941dc28fd137bd5ca5cbcbc9311f6377ab954f23cb59c389` |

Decisive Oracle bytes, read from the frozen revision rather than worktree edits:

| Oracle path | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/control.rs` | `4253ea5e94b671271fe64b5d1956bb961215e2e5c1278c56d88f0c67caaa7963` |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/constraints/row_effect.rs` | `080472bb5dcb3f724e808ff745c6fba304cc7ea2574b8f8eb3e3466964e937c2` |
| `crates/infer/src/constraints/machine/bounds.rs` | `c300c8c0c495da46822e1e1df38b833a6bffe5f3707642ae2cd26910b0608df7` |
| `crates/infer/src/constraints/machine/entry.rs` | `00c70ca0938b24d4d2dd38de6598fe54217aebd28150ac279b52839046b340b8` |
| `crates/infer/src/constraints/proof/mod.rs` | `bc0f3fbcf8f5ed01245e74283d3fd9cb13aa1713aff252a1847fde76b11b8e03` |
| `crates/infer/src/constraints/structural_kernel/access.rs` | `ad90bc1444be22df6080c7131ef49fedace884178c375af84ecb09416b38740f` |
| `crates/infer/src/compact/collect/mod.rs` | `828fa02521e2426297a9369df2fd9ef1560b7403a668ddfe881063ef16bdfd40` |
| `crates/infer/src/compact/collect/type_nodes.rs` | `96dc38a9a05c447f019bb0421e0b37057d283026ba87bce121bb33959b0d8ab2` |
| `crates/infer/src/analysis/session/generalize.rs` | `ed946b9ffb15f40c1fd721d8b2cb0907a6540c21d0bf690f784577307660e64a` |

All other Oracle locators are pinned by the same commit. Source inventory is
static and bounded: all inference forms, imported/free-ID behavior, extrusion
correctness, complete replay omissions, higher-order dispatch, complete Call,
all generalized observations, soundness, and principality are not certified.
No accepted theorem status or production authority is created by this note.

Commit packet:

- Exact leased/changed path: `notes/theory/2026-10-12-oracle-effect-hygiene-original-H-proof-attempt.md`; writes stop at handoff.
- Baselines: Y3 `37a107cfbf642da80ebb4950fad17dc8f6c788e9`; Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none among the pinned governing inputs; Oracle reads use immutable Git objects despite live capture edits. No dependency was edited by this leaf.
- Honest review status: independently reviewed source obstruction; no universal H closure, conditional closure, or source counterexample.
- Checks already run: static owner reads/searches, governing-baseline byte comparisons, SHA-256 snapshot, note whitespace/local-link checks; no builds/tests/execution.
- Proposed checkpoint message: `research: localize original Oracle H projection obstruction`.
- Shared-record deltas left for primary/curator: retain original H OPEN; link the exact bound-carrier/row-coverage classification and scheme exclusion seam in §5 without promoting a theorem or restarting established check/renaming lemmas. Keep complete Call, generalized observation, replay omission, residual correlation, soundness/principality, and production/F5 gates distinct and OPEN. No shared record was edited.
