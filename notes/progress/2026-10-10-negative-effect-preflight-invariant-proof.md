# Negative effect-row preflight: current rejection-safety derivation

Date: 2026-10-10
Status: independently reviewed bounded source derivation; no proof-gate closure
Baseline: `26b89d7b4d587ad8fac09c72c35c6343f2326554`
Branch at inspection: `research/simple-sub-intrusion`
Producer: prover-equivalent generic leaf `/root/negative_effect_preflight_proof_fallback`
Requested runtime: GPT-6.1 Sol/high; observed model/effort: unknown
Authority boundary: contextual attachment/admission design §§3–7; concrete-formal acceptance remains disabled

## Frozen claim and scope

This derives the current candidate's rejection-safety invariant. It does not
prove the desired annotation hygiene semantics or source-owned subtraction.
The distinction matters: the Authoritative contextual attachment/admission
design selects an internal carrier and two cycle accelerations while explicitly
leaving arbitrary concrete-formal admission behind a later gate (§§5–7).
Rejecting an unsupported row today is not evidence that its intended local
subtraction behavior has been implemented.

Let `T` range over finite `SourceAnnotationType` trees in the frozen source.
Each node consists of an optional `SourceEffectRow` and a value constructor
`Unit`, `Int`, `Variable(name)`, or `Function(argument, result)`.
The definitions are owned by `yu-hir/src/module/source_annotation.rs:67–93`.
Concrete atoms mean entries of that row's `concrete: Vec<SourceEffectId>`;
they do not mean the nominal family implicitly added for an operation result.

For any root sign `v ∈ {Positive, Negative}`, define `sign(v, p)` on occurrence
paths `p ∈ {A, R}*` that exist in `T`: the empty path has sign `v`, descent
through a Function's argument (`A`) flips sign, and descent through its result
(`R`) preserves sign. The effect row attached to the reached type node has
that same sign. Equivalently, sign flips once per argument descent, including
argument descents inside previously negative positions. This definition uses
tree occurrences, not names, node IDs, or a separately chosen sign for each
marginal witness.

Write `NoNegativeConcrete(T, v)` for:

```text
∀ valid p in T,
  sign(v, p) = Negative ∧ T[p].effects = Some(row)
    ⇒ row.concrete = [] .
```

Write `Pann(T, v)` for the return value of `preflight_annotation(T, v)` and
`Pformal(T, v)` for `preflight_formal(T, v)`, translating Positive to `true`
and Negative to `false`. The precise statements are:

1. For all finite `T` and both `v`, `Pann(T, v) = true` implies
   `NoNegativeConcrete(T, v)`.
2. For all finite `T` and both `v`, `Pformal(T, v) = true` implies
   `NoNegativeConcrete(T, v)`. At every explicit negative row it additionally
   implies exactly one symbolic effect variable. At every explicit row, both
   preflights imply at most one symbolic effect variable.
3. For a retained `LocalSource` successfully preflighted by
   `CandidateInference::solve`, every annotation or used operation signature
   selected for a source-plan annotation/operation action satisfies (1) at
   Positive, or, for a formal annotation, (2) at Negative with its root effect
   row absent. The constructor descent agrees with that composed variance:
   Argument Value/Effect flip, Result Value/Effect preserve.
4. Independently of source preflight, every call to
   `candidate_signature_effect(context, Some(row), family, polarity,
   Negative, ...)` with `row.concrete ≠ []` returns an error before allocating
   this row's tail, creating/reusing its nominal view, inserting its port bound,
   or returning a live row term. This holds for both endpoint `polarity` values.

The quantification in (3) covers the successor entrypoint's source annotation
actions, not every declaration stored anywhere in an accepted HIR module.
In particular, an unused operation declaration is not preflighted merely by
the initial loop that collects its placeholder errors.

Hypotheses are finite, safely formed HIR annotation trees, successful return
from the named preflight, and unchanged immutable HIR/action annotations between
that check and construction. For the operational call-order consequence, use
the frozen Rust control flow and normal propagation of `?`/early `return`;
there is no hypothesis that arbitrary source reaches preflight successfully.
No assumption about effect-solver success, semantic cancellation, shared
attachment identity, or complete Call denotation is used.

## Structural induction on both preflights

Prove the two statements separately, each universally quantified over `v`.
This stronger induction hypothesis is required because an argument child gets
the opposite sign.

At a node admitted by `Pann`, its row is absent, or its variable count is at
most one and a negative sign implies `row.concrete.is_empty()`;
`candidate_source.rs:98–100` rejects every other explicit row. Thus the empty
path satisfies the claimed property. `Unit`, `Int`, and `Variable` have no
children, completing their cases without resolving or interpreting the name.

For a Function admitted by `Pann`, its final conjunction
(`candidate_source.rs:102–105`) is true only if `Pann(argument, flip(v))` and
`Pann(result, v)` are both true. The induction hypothesis proves the property
for every argument path under `flip(v)` and every result path under `v`.
Prefixing those paths by `A` or `R` agrees exactly with `sign`. Together with
the root-row case this covers all valid occurrence paths. Short circuiting
cannot hide a failed sibling in a successful conjunction.

For `Pformal`, the initial row predicate (`candidate_source.rs:92–94`) is
true for an absent row. At Positive it requires at most one variable; at
Negative it requires no concrete entries and exactly one variable. Hence
the empty-path property and the stronger symbolic-count claim hold. Its
Function conjunction recursively uses `!positive` for the argument and
`positive` for the result. The same all-signs induction proves both subtrees.
The non-Function cases again have no descendants.

Whole, local, and expression annotations therefore instantiate (1) with
Positive. Formal annotations instantiate (2) with Negative; the source
preflight independently requires their root row to be absent. Negative
positions inside a whole annotation allow explicit empty rows, while the
formal preflight requires one variable at explicit negative positions.
The theorem retains that difference rather than weakening either predicate.

## Actual source entrypoint, plan, and consumers

The source correspondence is a static audit of the following frozen owners.
There is no supplied executable model standing in for these constructors.

| Source input | Check before collection | Plan action and consumer | Root variance |
| --- | --- | --- | --- |
| Definition's whole annotation | `candidate_source::preflight`, line 58 | `emit_candidate_source`, lines 455–466: `Annotation`; `route_candidate_source`, line 573 → `candidate_annotation` → `candidate_annotation_pair` | Positive for both value terms |
| Local binding annotation | `preflight`, lines 61–64 → `preflight_local_annotation` | `emit_candidate_source`, lines 290–299: `LocalAnnotation`; route line 569 → `candidate_local_annotation` | Positive for both value terms |
| Expression ascription | `preflight`, lines 67–70 → `preflight_local_annotation` | `emit_candidate_source`, lines 388–409: `Ascription`; route line 552 → `candidate_expression_ascription` → `candidate_annotation_pair` | Positive for both value terms |
| Annotated Lambda parameter, including a binding parameter represented by a Lambda | `preflight`, lines 72–75: absent root row and `preflight_formal(..., false)` | `emit_candidate_source`, lines 245–257: `FormalAnnotation`; route line 553 → `candidate_formal_annotation` → `candidate_formal_pair` | Negative |
| Resolved operation reference's signature | `preflight`, lines 77–82: Function root, absent root row, and `preflight_annotation(..., true)` | `emit_candidate_source`, lines 326–338: `Operation`; route line 572 → `candidate_operation` | Positive |

`LocalSource` owns the whole annotation, binding list, and expression list;
the relevant forms are declared in `yu-hir/src/module/local_source.rs:13–147`.
`preflight` scans those same lists, including all expression annotations;
planning selects from those lists and clones the selected annotations into
actions. There is no new annotation tree synthesized by the listed actions.
Binding parameter metadata is not an additional formal constructor input:
the `FormalAnnotation` action is emitted from the Lambda expression's
parameter, which the expression loop already checked.

`CandidateInference::solve` (`shadow_apply.rs:79–116`) checks each binding's
retained `LocalSource` at line 92, propagates preflight failure immediately,
checks permissible HIR errors, and only then calls
`collect_candidate_mode(hir, true, true)` at line 110. Collection
(`lib.rs:1123–1135`) obtains those retained local sources for the same binding
roots and invokes `emit_candidate_source`. Non-local-source fallback inputs
use `preflight_expression`; they are not a second annotation-action producer.
Thus no retained-source annotation action in this entrypoint escapes the
listed polarity preflight. Referenced operation declarations are checked
through each `Operation` expression, including declarations reached through
resolution rather than the local declaration list.

The private `collect_candidate_mode` does not itself call source preflight.
Unit-test helpers directly call it with `true, true` and some tests directly
call annotation consumers. Those are real bypasses of the source-entrypoint
check, outside statement (3); this note does not promote collection to a
self-validating admission API. The audited non-test graph-effects collection
entry is `CandidateInference::solve`. `ConstraintBatch::collect` and the
value-only `CandidateValueObservation` use the `candidate_graph_effects = false`
route and are excluded from this successor annotation-action claim.

## Constructor correspondence and independent refusal

Endpoint term polarity and composed annotation variance are separate arguments.
`candidate_annotation_pair` constructs its upper term at endpoint Negative and
its exposed term at endpoint Positive, with variance Positive for both
(`candidate_effect.rs:1098–1118`). `candidate_local_annotation` does the same
(`1006–1015`) after repeating `preflight_local_annotation` at line 987.
`candidate_operation` starts its signature at endpoint Positive and variance
Positive (`664`). `candidate_formal_annotation` rejects an explicit root row
and starts its paired constructor at variance Negative (`942, 955`).

For `candidate_signature_value`'s Function case (`1257–1299`), `opposite`
flips endpoint polarity and `reversed` flips variance. The argument Value
call gets both flips; the result Value call preserves both. Argument Effect
receives `opposite, reversed`; Result Effect receives `polarity, variance`.
Hence both component kinds follow the same occurrence-sign recurrence used
by the proof. Paired construction does not turn a negative-variance source
row into a positive-variance source row merely by constructing its positive
endpoint term.

For formal annotations, `candidate_formal_pair` first rechecks each node's row
predicate (`899–900`), then gives the reversed variance to argument Value and
Effect and the current variance to result Value and Effect (`909–913`).
`candidate_formal_effect_port` allows an absent row, an empty-concrete
singleton symbolic row, or the explicit covariant branch. Only the latter
calls `candidate_signature_effect` for both endpoint polarities, retaining
Positive variance (`919–935`). Thus a negative concrete formal row also
fails independently at the paired constructor; its effect port cannot select
the positive-view branch.

For any explicit row, `candidate_signature_effect`'s guard
(`candidate_effect.rs:1364–1366`) precedes its variable-count check, scoped tail
lookup/allocation, view-cache lookup, view creation, fresh port, bound insertion,
and final `live_effect_term` call. If variance is Negative and concrete entries
exist, it immediately returns `Err(exhausted())`. This proves statement (4)
for arbitrary calls, including calls that bypass preflight. The assertion is
local to this row: an earlier sibling or parent call may already have allocated
other state. Atomic rollback of such earlier state is not proved here.

At Negative with an admitted explicit row, the remaining branch returns the
symbolic tail's live term or the endpoint-appropriate bottom/empty leaf
(`1384–1395`); it does not construct a nominal concrete view. At Positive, the
view branch preserves the nominal `SourceEffectId` entries by extending its
`allowed` vector with `row.concrete` (and the operation family when supplied),
retains the symbolic tail and annotation source coordinates, calls
`candidate_signature_view`, and inserts a fresh port bound to `Support(view)`
for endpoint Positive or `Allowance(view)` for endpoint Negative
(`1396–1433`). A cached view preserves the already retained view; this note
does not prove cache-key uniqueness or freshening semantics.

`candidate_signature_view` (`597–650`) retains `allowed` and `tail` in the
stored `View` and may retain contextual source weights. That storage is enough
for the construction claim; it is not evidence of subsequent subtraction or
filter discharge. For a whole annotation's explicit root row,
`candidate_annotation_computation_effect` uses endpoint Negative with variance
Positive (`1172–1209`), or directly uses a singleton symbolic tail. This is
consistent with root polarity and does not bypass a composed-negative check.

The omitted-row branch can synthesize an operation family's `Support` view
before the explicit-row guard. It receives `family = Some(...)` only at the
outermost operation signature's result port (`1282–1285`); that signature
starts at variance Positive and result descent preserves it. This synthetic
family is not a negative concrete source annotation row, and cannot be used
to generalize statement (4) to all possible omitted-row invocations.

## Falsifier audit, checks, and exclusions

The named falsifiers are (a) an annotation action admitted through the covered
entrypoint without its corresponding root-sign preflight, or (b) an explicit
negative concrete annotation row reaching its live row/view constructor before
rejection. The call-site and guard-order audit found neither in the frozen
sources. Direct test/internal collection bypasses were retained as exclusions,
not hidden by claiming that all possible callers pass through source preflight.

Checks performed were read-only `rg` call-site searches, bounded `sed`/`cat`
source inspection, branch/baseline inspection, and SHA-256 equality of the
seven direct dependencies against `git show <baseline>:<path>`. The latter
confirmed that the inspected files equal the pinned revision. No compiler,
unit test, finite-model checker, semantic execution, timing experiment, or
benchmark was run. No test evidence is claimed. Measurement samples: zero;
heavyweight build/test processes: zero. Lightweight inspection commands used
no retained scratch outputs; no child was launched by this leaf.

Unproved scopes include syntax/lowering completeness, arbitrary source
admission, concrete-negative subtraction, same-family unrelated-contribution
hygiene, attachment grouping/fresh-use identity, source-to-context transport,
mixed-component termination, certificate recognition/invalidation, rollback,
actual solver discharge, complete Call/Catch behavior, inference soundness,
principality, production/default cutover, and runtime/backend execution.
Absence of concrete entries does not imply absence of future effects through a
symbolic tail. Successful preflight does not imply successful inference or
publication. Rejection-safety is a current implementation property and does not
authorize keeping this rejection after the later enabling gate is satisfied.

## Frozen direct dependencies and next gate

The following SHA-256 values bind the derivation's inspected source/authority
snapshot. Rules/configuration were read for workflow; their text is not an
extra semantic premise of the induction. All seven direct dependencies matched
the baseline when checked before writing this note.

| Path | SHA-256 |
| --- | --- |
| `crates/yu-solver/src/candidate_source.rs` | `8adc289142dd78a625184dd661fb162e49f24532a19c7c4f9e114e604c0966a0` |
| `crates/yu-solver/src/candidate_effect.rs` | `2599ad4412c7fc51841a4fcc4139f3b4d117ad6fa40a78a41a709ebe5ad1600e` |
| `crates/yu-solver/src/shadow_apply.rs` | `6bea8808153b8b71a57e4a8583284e49284ec9aa35118a61f44a3a387a8a32f6` |
| `crates/yu-solver/src/lib.rs` | `9c16200d5982efb6c20e19b969a289368954579113d2b166041abc7741ab0fa1` |
| `crates/yu-hir/src/module/source_annotation.rs` | `a348a47530e57c2b3475a4c0d9f020e24ba04ea58a06292847892640567e61cb` |
| `crates/yu-hir/src/module/local_source.rs` | `906864b15edd43c33cd675ebff86e2652655d6fd1000ed47fe197a4cfd7ed7ed` |
| `notes/design/2026-10-10-contextual-attachment-admission-design.md` | `717f734c42ced6aec52ea5c4280c75955950a793cdb9b020aedde208f02680dc` |

Next proof gate: obtain independent review of this frozen rejection invariant,
then keep the enabling source-to-consumer obligation separate: prove that an
admitted negative concrete occurrence creates attachment-local authority and
that the actual subtraction/check/replay consumers preserve it through the
selected lifecycle, with exact mixed-component admission where required.
The present theorem supplies no premise that closes that later gate.

## Independent review and primary baseline audit

An independent compiler-referee review found no BLOCKING, major, or minor
finding. It accepted the all-signs induction, source-entrypoint coverage and
the local guard ordering, while preserving the distinction between current
rejection-safety and desired hygiene/admission. The reviewer did not use Git.
The primary independently hashed all seven listed dependencies against the
pinned baseline commit; every current file matched its baseline blob exactly.
No executable source, build, test, or semantic execution was added by review.

Commit packet: sole leased output is this note; baseline as above; direct
dependency changes: none at inspection. Proposed checkpoint message:
`research: derive current negative effect-row preflight safety`.
Review status: producer derivation only, independent review pending. Shared
record delta for the primary: record this bounded current-rejection result
without closing effect hygiene or concrete-formal admission; leave
`tasks/current.md` and shared theory/design status updates to their owners.
