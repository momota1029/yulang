# Ground head readback for total materialization

Status: Lean construction complete, astra2-centered-26, 2026-11-15.
`GeneralNominalCenteredHeadMatHeadReadback.ground_head_readback roles` proves the
unchanged `GeneralNominalCenteredHeadMatSemanticAncestry.GroundHeadReadback roles`.
It has no residual hypothesis. The same module supplies unconditional
`ground_depth_bound`, `ground_cover`, and `progress`, and `ground_accessible`
for the unrestricted successor Step under the original checked WF ground-source
assumptions. No Step, guard, source contract, boundary, or earlier definition
is changed. No termination counterexample or owner question arose.

## Exact result and source authority

The closed global statements are:

```lean
GeneralNominalCenteredHeadMatHeadReadback.ground_head_readback roles :
  GeneralNominalCenteredHeadMatSemanticAncestry.GroundHeadReadback roles

GeneralNominalCenteredHeadMatHeadReadback.ground_depth_bound roles :
  GeneralNominalCenteredHeadMatGroundCover.GroundDepthBound roles

GeneralNominalCenteredHeadMatHeadReadback.ground_cover roles :
  GeneralNominalCenteredHeadMatStepFiniteProgress.GroundCover roles

GeneralNominalCenteredHeadMatHeadReadback.progress roles :
  GeneralNominalCenteredHeadMatStepExecutor.Progress roles
```

`ground_accessible` states:

```lean
(checked : Checked registry)
(source : InitialSource registry context root)
(point : ∀ index, (root.demand.arguments index).1 =
  (root.demand.arguments index).2)
(ground : GroundRoots context root rootLabels)
(coverage : Coverage registry context.interpretation) :
Acc (fun next current => Step registry root current next)
  (initial context root)
```

These are the actual total-materialization, justified-cache relation and the
existing source contract. Accessibility is not restricted to a compatible
subrelation or to one executor. The earlier retrospective ancestry theorem
gives the installed-depth bound `mass rootLabels`.

Section 6.3 requires normalized size: hidden same-name record fields are removed,
same-tag variants are merged, and capture-dependent destructive merging is
excluded by declaration checking. It also says 「名前なしの引数だけで数え、この出力専用の変数は数えない」.
The proof uses the existing `countsCovered`, normalized `inputNames`, and
`SharedCaptures.Needed`; it adds no measure for associated outputs. Each name
needed in a normalized unnamed child has a finite readback. The existing
`needed_excludes_output` theorem excludes output-only names from this set.

The current checked language requires normalized heads and unnamed children
of a declaration with children to be count-covered. Residual joins are outside
that existing certificate. The proof handles variant payloads after the
specified normalization, including repeated payloads that merge away, and
arbitrary record tails. It does not claim inversion for unrestricted residual
multi-tag joins in `Meaning`; the target uses `CountedMeaning`. Multi-tag
associated outputs and defaults remain legal materialized equations and are
not included in the input-depth measure.

## Arbitrary labels, not just emitted labels

The frozen `EnabledHeadReadback` quantifier ranges over every semantic input
label list. Such a label is closed, count-covered after normalization, and
equivalent to a center's value. It need not itself have a WF or successful
translation certificate. The proof preserves that quantifier.

`GeneralNominalCenteredHeadMatRecordReadback` separates a finite record spine
from its remaining tail. Every closed count-covered nonrecord tail has either
no field observations or all trivial field observations. The latter case
includes the algebra's fallback-to-bottom interpretation of unsupported
applications. If the whole value is equivalent to a finite record signature,
a fresh label outside both finite field lists rules out that latter case.
This does not identify the tail with the empty record; exact tails and
nonrecord tails retain their ordinary meanings.

`GeneralNominalCenteredHeadMatRecordProjection.record_parts` recovers the
finite payload patterns in the cached signature's order. Duplicate freedom
comes from the existing normal form. Field sorting preserves the sum of their
sizes, and the finite record spine costs its number of fields plus one.
`fold_payload` uses the parent comparison at observation depth `depth + 1`
to recover the payload comparison at `depth`, for every rank and environment.

`GeneralNominalCenteredHeadMatHeadShape` uses role observations to distinguish
constructor heads. Bottom cannot satisfy a head test, and a record with a
present field cannot be exact-empty. Scalar, pair, variant, invariant nominal,
empty-record and exact-empty meanings are kept distinct. Nominal alias keys
need no inverse catalogue: semantic identity and argument count determine the
test, while counting ignores the numeric key.

`GeneralNominalCenteredHeadMatHeadParts.inversion` combines those results.
For any closed count-covered normalized label and a canonical test satisfied
by its meaning, it returns finite projection patterns whose total cost plus
the head cost is at most the input label's size. Arbitrary record tails and
malformed/fallback applications are covered by the argument, not excluded by
an additional premise. Nested variable captures can retain their complete
finite labels even when their values have no inspection-tree representation.

## From the real frame to finite captures

`GeneralNominalCenteredHeadMatSchemaMass.schema_mass` interprets actual-mode
schema uses. A variable use identifies the observed value with the plan's
actual binder. A constructor use invokes semantic inversion and the existing
unique finite-projection readback, then sums the child bounds. Its intermediate
capture-weight premise is discharged in the final producer.

`GeneralNominalCenteredHeadMatWeightedHead.head_weight` reads the actual
head-only `Frame.prepared` certificate. Finished inspection proves every
query complete; normalized declaration checking supplies canonical finite
query templates. The corrected packet's `headSchema` supplies their actual
center tests and variable equalities. The semantic input labels are used
directly; no conversion to the old `ClosedTerm` relation is attempted.
The theorem bounds the full substituted head weight for every substitution
whose capture weights are bounded by their finite semantic representations.

`GeneralNominalCenteredHeadMatHeadReadback.finite_capture` derives capture
existence from this universal weight theorem. If a needed head variable had
no finite representation, assigning that variable weight larger than the
whole parent label mass and every other variable weight one would contradict
the head inequality. This uses the actual normalized head occurrence of that
name, not an output equation or a guessed substitution.

`minimum_capture` chooses a least-size finite representation separately in
each model. `readback` applies those choices to all needed names, uses a
one-node variable label for each unused name, and proves both the exact
`Captures` predicate and the instantiated-head mass comparison. These are
proof witnesses for a model; execution does not choose concrete argument types.

The local theorem is stronger than the requested reachable-state producer:
it needs the actual head-only frame, a nonempty requirement list, corrected
packet `Holds`, and semantic centered inputs in the same model. It does not
need a separate chosen-effect, cache, or journal inhabitance assumption.
Those guards remain unchanged in `Installable`; they restrict when the local
theorem is used. `ground_head_readback` obtains the frame from the real enabled
installation and aligns registry/interpretation using configuration preservation
along the actual trace. It then satisfies the frozen producer verbatim.

## Hypotheses and remaining work

There is no undischarged hypothesis in `ground_head_readback`,
`ground_depth_bound`, `ground_cover`, or `progress` beyond their `roles` parameter.
Their quantified source obligations remain exactly those in the frozen target.
`ground_accessible` retains the five original assumptions displayed above.
The local `readback` retains `Frame`, nonempty requirements, corrected packet
`Holds`, and semantic `Inputs`; the global theorem discharges their operational
origins. Intermediate inversion lemmas retain explicit closedness, normality,
canonical tests and carrier equivalence. No intermediate finite-capture or
weight premise remains in the global result.

`CanonicalExitLifting`, general `Extension`/`SelectedCompletion`,
`GeneratedSelectedChildren`, and exhaustive K2 projections are unchanged.
No claim about these separate obligations follows merely from accessibility.

The exact public theorem inventory is in
`lean/Audit/GeneralNominalCenteredHeadMatHeadReadback.lean`.

## Review and checks

No registered/callable `prover` role or configuration was available; no prover
agent ran. The primary constructed the derivation. Separate read-only source
audit and fresh independent review checked the arbitrary-label domain, record
projection depth, actual head preparation, capture-existence argument and exact
global target. The reviewer ran the seven new modules directly with Lean,
all with exit **0**, and found no added premise. A second source review
confirmed that no source/guard restriction was introduced.

The following final commands ran from `lean/`, all with exit **0**:

```text
lake build --wfail Yulang.GeneralNominalCenteredHeadMatRecordReadback Yulang.GeneralNominalCenteredHeadMatRecordProjection Yulang.GeneralNominalCenteredHeadMatHeadShape Yulang.GeneralNominalCenteredHeadMatHeadParts Yulang.GeneralNominalCenteredHeadMatSchemaMass Yulang.GeneralNominalCenteredHeadMatWeightedHead Yulang.GeneralNominalCenteredHeadMatHeadReadback
lake build --wfail Yulang
lake build --wfail
lake env lean Audit/GeneralNominalCenteredHeadMatHeadReadback.lean
```

The full builds completed 2,845 and 2,846 jobs, respectively. The new audit
covers all 45 public theorems; the only reported logical dependencies are
`propext`, `Classical.choice`, and `Quot.sound`. `git diff --check`, the
append-only/frozen-file/import/scope checks, and the dependency scan exited
**0**. Exploratory builds exited **1** while elaboration errors were being
resolved; all final checks above were rerun successfully. No git refs changed.
