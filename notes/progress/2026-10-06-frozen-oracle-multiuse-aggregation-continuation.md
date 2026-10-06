# Frozen Oracle multi-use frame and endpoint continuation

Date: 2026-10-06
Status: research-only historical characterization; independent review pending
Yulang3 baseline: `a5e19baaa248e31f7c3efbcca1fe01f9aa71d71b`
Frozen Oracle: `a58eefc31e22141574b6f20c6a5748151c6d79f1`, `/tmp/yulang2-oracle-rebuild`
Exclusive lease: this note only
Semantic and implementation authority: none

## Objective and method

Trace the two seams left by the reviewed
[multi-use archaeology](2026-10-06-frozen-oracle-multiuse-aggregation-archaeology.md):
`unannotated_call_frame_index`, and the producers/consumers selecting endpoints
from `call_uppers`, `call_public_upper`, and `call_erased_upper`. The reviewed
[main source-generation crosswalk](2026-10-06-main-source-generation-oracle-crosswalk.md)
is a locator and historical context, not authority. The method is six-file
static source inspection, frozen-blob comparisons, and conditional control-flow
derivation. No source program, Oracle executable, test, or solver was run.

Current authority remains call-view `q1/a2`,
`notes/design/2026-10-05-inferred-function-call-views.md` §§1–5 including §1.1,
and nested-block `q1/a1`,
`notes/design/2026-10-06-nested-block-function-source-realization-addendum.md`
§§1–3. The selected shared relation, internal protected seed and ordinary-value
refinement, annotation-scoped permission, and exact captured-step interpretation
are preserved. No historical branch supplies their missing current rules.

## Result and claim class

The previously located call-upper vector has a concrete source-lowering
producer and consumer: parameter annotation → local metadata → guarded
application recording → defined-lambda wrapper's argument endpoint. It is
more than an unused branch-local accumulator. Its ordinary recorder is
**annotation-dependent**: the inspected no-annotation construction supplies
neither public nor erased upper and thus does not enable that recorder.
Unannotated calls retain the distinct live-variable/frame-subtraction route.

The frame selector is now explicit. It chooses the introduction frame when
crossing an active inner defined skeleton, otherwise the current defined frame;
with a non-defined top frame it selects the introduction frame only in a
nonempty sub-syntax scope. A common formal `DefId` alone does not determine a
common frame across every call context.

Claim class: bounded historical control/dataflow characterization, with
conditional derivations over supplied lowerer states. Blob equality and the
cited local assignments are established provenance/representation facts.
There is no source-semantics theorem, independently reviewed result for this
note, old-to-current semantic equivalence, or production permission.

Hypotheses: H1 all six read source files match the frozen blobs (verified);
H2 ordinary defined-parameter, annotation, name/application, and wrapper
lowering reach the cited routines and complete successfully; H3 supplied
frame/skeleton and annotation-connection state satisfy the stated guards.
Construction of every H2/H3 state from an accepted surface program remains
unverified. These premises are not inferred from printed schemes.

## Frame production, selection, and use

All source paths below are relative to the frozen Oracle tree.

`crates/infer/src/lowering/expr/lambda.rs:644–742` installs each defined
parameter, pushes a `FunctionPredicateFrame::new(Defined)`, and calls
`mark_defined_unannotated_arg_call_frame` with that new frame index. The marker
writes the index only to locals classified `Unannotated`
(`tail.rs:832–841`). Parameter uppers supplied separately can change that
classification to `Annotated` (`lambda.rs:690–696`); source annotation absence
is therefore not the only input to this historical metadata.

An active defined skeleton is pushed when `self_value` is present, recording
`before_frames` and cloned parameter metadata (`lambda.rs:745–772`). The
selector uses that exact range (`tail.rs:801–830`):

| Lowerer state | Selected frame |
| --- | --- |
| No `local.unannotated_call_frame` | None |
| Top frame is Defined, and some active skeleton has `introduced < before_frames <= current < before_frames + params.len()` | Introduction frame |
| Top frame is Defined, without that crossing | Last Defined frame, found by reverse position |
| Top frame is not Defined and `sub_syntax_scopes` is nonempty | Introduction frame |
| Top frame is not Defined and no sub-syntax scope exists | None |

The caller `unannotated_local_callee_return_effect` additionally requires a
direct local callee whose definition is `Def::Arg`, `Unannotated` metadata,
and a selected existing Defined frame (`tail.rs:740–767`). Direct callee
resolution requires `Expr::Var` and follows its resolved reference target
(`:844–848`). The earlier note documents the resulting selected-frame map
lookup and subtraction reuse at `:769–798`.

Smallest discriminating state witness: introduction index 0, current Defined
index 1, and one active skeleton with `before_frames=1`, `params.len()=1`.
The selector's crossing condition is true and returns 0. Removing that active
skeleton, while keeping both frame indices and the same formal, makes it
return 1. This is a direct evaluation of the inspected boolean/branch logic,
not an executed compiler experiment or a claim that both states are accepted
source programs. It demonstrates precisely why frame sharing required a
separate premise in the prior two-call derivation.

## Annotation to call-upper inventory

`connect_lambda_pattern_annotation` in `lambda.rs:1244–1341` is the producer:

- No source annotation returns an empty call predicate,
  `call_public_upper=None`, `call_erased_upper=None`, and projection disabled
  (`:1252–1264`).
- For an annotation, it builds `AnnType`, connects parameter computation,
  and derives a call predicate (`:1266–1283`). With a nonempty predicate and
  a closed effect head, it obtains the public upper through
  `lower_public_callable_upper_with_evidence` (`:1284–1293`).
- With a nonempty predicate and an effect head, it erases selected annotation
  effect heads and obtains the erased upper through `lower_value_upper`
  (`:1294–1304`). Projection is disabled when the callable annotation has an
  effect wildcard (`:1339`).

The guards' meaning is traceable locally: a closed head has a nonempty row,
no tail, and no wildcard (`:1479–1507`); the effect-head predicate also visits
specified nested shapes (`:1458–1476`). Erasure preserves Function parameter
and argument-effect annotations, applies head erasure to return-effect rows,
and recurses through the result (`:1530–1554`). A wildcard row is retained;
otherwise its item list is emptied while its tail is retained (`:1557–1568`).
These are historical `AnnType` transformations, not current removal permissions.

`crates/infer/src/annotation/constraints.rs:207–212` shows that the
`with_evidence` method delegates directly to `lower_public_callable_upper`.
Its Function branch constructs a four-port negative Function using lowered
parameter/argument-effect bounds, a public return-effect endpoint, and a
recursively lowered result (`:190–203`). `lower_value_upper` delegates to
`lower_value_bounds` and selects its negative endpoint (`:151–153`). Complete
internals of `lower_value_bounds`, effect lowering, and every annotation shape
were not reconstructed here; names alone establish no receipt construction.

New pattern locals start with no public/erased upper, an empty call-upper
vector, no recorded use, and no frame metadata
(`crates/infer/src/lowering/pattern.rs:263–279`). Defined parameter lowering
calls `mark_lambda_param_call_predicate` (`lambda.rs:724–736`), which returns
early for an empty predicate and otherwise installs predicate weights and
public/erased/projection fields on the newly introduced locals (`:919–935`).
It records a predicate frame only when weights are nonempty (`:938–943`).

At an ordinary call, the application obtains the local's erased upper and
emits its occurrence-specific Function upper (`tail.rs:543–563,690–705`).
Only `Some(erased_upper)` enables the ordinary call-upper recorder and extra
erased-upper constraint (`:603–614`). The recorder retains distinct upper IDs,
marks erased use, and marks nesting when the current call frame differs from
the predicate frame (`:707–717`).

Conditional exclusion derivation: a fresh no-annotation local has erased upper
None; its empty predicate makes the marker return before changing that field;
the ordinary-call `Some(erased_upper)` guard therefore fails. In this inspected
construction chain, repeated calls to that local do not populate `call_uppers`.
The shared variable's ordinary Function constraints and eligible unannotated
frame mechanism still apply. This is a local chain result, not a global claim
that no other producer anywhere can change those fields. Exact-symbol searches
were confined to the six listed files.

## Inventory to wrapper argument endpoint

After lowering a defined body, the routine pops parameter frames in reverse
order and wraps the parameters while their locals still exist; local truncation
follows wrapping (`lambda.rs:852–865`). It supplies `body_type_expr.is_some()`
as the wrapper's projection flag (`:862`). `wrap_lambda_param` obtains its
argument endpoint from `lambda_param_public_arg`, creates the output predicate,
and constrains a fresh value with a positive Function containing that argument
(`:946–975`). Thus there is a concrete consumer in produced Function structure.
This is the wrapper's argument endpoint, not proof of a final exported scheme.

The selection order at `lambda.rs:978–1039` is exact:

1. Recognize a Var/As parameter and its local with `call_erased_used=true`.
2. If public upper exists, return its observed-wildcard adaptation immediately.
3. Otherwise, if the caller projection flag, local projection permission,
   nesting flag, and nonempty inventory all hold, allocate `projected`, submit
   `Pos::Var(projected) <: Ui[ret_eff := body.effect]` for each recorded upper,
   and return `Neg::Var(projected)`.
4. Otherwise, if erased upper exists, return its observed-wildcard adaptation.
5. Fall back to `Neg::Var(param.value)`.

The replacement in step 3 retains each Function's argument, argument-effect,
and return-value endpoints and replaces only its return-effect endpoint
(`:1111–1124`). A public upper takes precedence even when step 3's other guards
hold. This precedence is a historical implementation choice, not a current
profile/admission rule.

`callable_upper_with_observed_wildcards` (`:1041–1109`) passes a non-Function
upper through unchanged. For a Function with `Pos::Bot` argument, it allocates
one observed argument variable and submits every recorded Function argument
as a lower constraint into it (`:1058–1071`). For a `Neg::Top` result, it
allocates one observed result variable, constrains it below every recorded
Function result, and adds the reverse variable constraint when that result
is a plain `Neg::Var` (`:1074–1100`). It returns a new Function while retaining
the selected upper's argument-effect and return-effect endpoints (`:1103–1108`).
These loops concretely use multiple retained calls. They do not prove a
complete joint source relation or correlation after solving and generalizing.

## Remaining boundary and independence

The two formerly untraced implementation seams are now characterized at the
producer/selector/wrapper level. Remaining historical omissions are the actual
route and guards for a newly accepted multi-use source program, complete
annotation lowering, solver propagation and errors, final generalized/exported
scheme behavior, arbitrary aliases/imports/method dispatch, and broader
recursive/capture cases. Anonymous-lambda construction also installs annotation
metadata (`lambda.rs:285–304`) but uses its own direct Function construction
after truncating locals (`:347–364`); this note does not generalize the defined
wrapper consumer to that path.

No Handler/non-Handler classification corresponding to the approved current
ordinary-value inference was derived. Generic historical metadata and endpoint
names supply no current `beta/Slots(beta)`, profile, typed receipt, Omega,
receiver, or comparison-independent joint `(nu,K,D)` producer. Soundness,
principality, source adequacy, production membership and conformance remain
separate open gates.

Oracle source is the historical object, not an independent semantics oracle.
Its producer and consumer share one implementation's assumptions. Blob checks
prove provenance only; the conditional branch derivations prove only the
cited code consequences under H2/H3. No self-assuming checker, mutation suite,
independent semantic reference, or output-based inference was used.

Failure conditions include changed blobs, different lowering/parameter paths,
changed supplied annotation/skeleton state, failed lowering before wrapping,
or additional out-of-scope writes to the metadata. No repository-wide absence
claim is made. Source lookup stopped at the assigned six-file bound.

Recommended next action: use the current approved atomic source-evidence
obligation to derive the unannotated formal/use relation; the annotated Oracle
inventory route cannot supply that missing rule. Further old-side probing is
justified only by a new, specific correspondence question.

## Verification, resources, and hashes

Budget/coverage: at most six frozen files; six inspected, three revisited from
the earlier eight-file pass and three newly added (`lambda.rs`,
`annotation/constraints.rs`, `pattern.rs`). Four sequential lightweight
read-command captures, using Python and read-only Git archives; no parallel
compute, candidate execution, build/test, CLI, formatting, Git mutation, seed,
random range, or mutation. One intermediate capture was truncated; decisive
frame, endpoint, and initialization clauses were recovered in narrow later
captures. Omitted output is not claimed as inspected. Read captures reported
about 0.1 seconds each; total wall time, CPU and peak RSS were not measured.

Three source archive comparisons (four-file, two-file, and final six-file)
passed byte equality assertions. One archive comparison checked eight current
dependencies against the pinned Yulang3 baseline; all matched. No dependency
hash changed relative to this continuation's baseline. The prior note's hash
differs from its original worker submission because the integrated review-status
record is now part of the assigned baseline; this note does not edit it.

| Frozen source | SHA-256 |
| --- | --- |
| `crates/infer/src/lowering/expr/tail.rs` | `ac406b309fbb0ba558a18e37aba63a8e7ffeabbc377a111566b1f97d786f93b8` |
| `crates/infer/src/lowering/expr/lambda.rs` | `2e0206bdcfdfbe98d13c12eec7ba8f7964383bc08c92947352ad370754024db9` |
| `crates/infer/src/lowering/local.rs` | `300bc2b12d8f13aed0ae5f65cdec93683e7de2719be38bb33724f51730e52f81` |
| `crates/infer/src/lowering/name_ref.rs` | `699c7dc84a2b4889355ffe9cd23b3e871c295957dbcb3fbad96ee9ee36470ede` |
| `crates/infer/src/annotation/constraints.rs` | `3c0482d4549a2bfc7e651a6b2cc15fa4e70488fe8f68fcbfca34c1bfb72920db` |
| `crates/infer/src/lowering/pattern.rs` | `b56344fca6fd964d1429084adaaf3a11d8603f7fb71d48d71d60d30ec4156126` |

| Current dependency | SHA-256 |
| --- | --- |
| `notes/design/2026-10-05-inferred-function-call-views.md` | `4b3363b79901e84b87cc8e02b59b023ff82c33e76d0be6d255e2b7bbab1a65c1` |
| `notes/design/2026-10-06-nested-block-function-source-realization-addendum.md` | `750449c19d9bdb23278894373a61c6408985ae5703a0f00a8a9f919d045e7ed0` |
| `questions/2026-10-05-function-call-view-formation/approved-answer.md` | `1071cf1c2d9abce2ffbc829cec7757d2b2f52849174c04751bd63aeefa520536` |
| `questions/2026-10-05-nested-block-function-source-realization/approved-answer.md` | `04ee0dc089dc6ad19a184d31775a146c08b07f2f287099d2e5b54d7d1d5a643e` |
| `questions/2026-10-05-function-call-view-formation/receipt.md` | `6dcf408143c7eb48260d8c4df9ef73834da8d28a7f4ec9744ab381e67414cee0` |
| `questions/2026-10-05-nested-block-function-source-realization/receipt.md` | `e5e59e176eb865a588b2843b18137571fe9c5b6f43bf1ca349bc60c9ad90f0ec` |
| `notes/progress/2026-10-06-frozen-oracle-multiuse-aggregation-archaeology.md` | `6b2667fd95be910f25cd8da67177ea1d192e8600028cce32c14e67344defb7ee` |
| `notes/progress/2026-10-06-main-source-generation-oracle-crosswalk.md` | `d192164e3b07328620fd58c75f4f359b277333885747c815d073520b9bb67784` |

## Commit packet

- Exact leased path: `notes/progress/2026-10-06-frozen-oracle-multiuse-aggregation-continuation.md`.
- Baseline SHA: Yulang3 `a5e19baaa248e31f7c3efbcca1fe01f9aa71d71b`;
  frozen Oracle `a58eefc31e22141574b6f20c6a5748151c6d79f1`.
- Changed dependency hashes: none relative to the assigned baseline; eight
  current dependencies and six frozen source files matched their blobs.
- Review status: research-only historical characterization; independent review
  pending. Producer writes stop before submission for frozen review.
- Checks already run: four bounded read captures, three source archive equality
  comparisons, one current-dependency archive comparison, SHA-256 recording.
  No tests, builds, Oracle execution, or Git mutation. Primary owns final
  artifact diff/scope inspection and integration.
- Proposed one-line research-checkpoint commit message:
  `research: trace Oracle call-frame and public endpoint selection`.
- Shared-record deltas left for primary/curator: replace the two historical
  selector/consumer gaps with this bounded trace; identify `call_uppers` as an
  annotation-dependent producer/consumer route, preserve the distinct
  unannotated live-variable/frame route, and retain every current source-atomic
  relation/profile/receipt and proof gate. No shared records were changed.
