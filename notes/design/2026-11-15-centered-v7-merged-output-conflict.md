# V7 merged-output rejection and selected-only evidence

Status: additive proof record, astra2-centered-31, 2026-11-15.

V7 implements the owner's merged-output rejection decision on the unchanged
Alloc Step. All twelve operational bridges, canonical exit lifting, exactness,
saturation and order laws are closed. The previous R merge fixture now rejects
its generated R class, never selecting it or reporting pending.

The requested universal completion route still has a closed counterexample:
the fixture's parent P remains head-selected with its children already recorded,
while the full journal is empty. This refutes V7 `HeadBaseline` and
`SelectedCompletion`; it does not refute generated-child coverage. Production
work stops at this requested counterexample boundary.

Following the supervisor's cycle-199 correction, the evidence interface is
**selected-only**, with no prior-shaped evidence assumption. Conditional V7
composition is proved from exactly this field and selected-child generation;
the twelve other fields are discharged. The cycle-199 terminal fixture satisfies
the new pointwise evidence obligation vacuously through rejection, despite
having an inhabited model. Global evidence remains dot's task.

## The conflict definition

The governing owner wording supplied in turn 31 is
「まとめた需要の出力の指定どうしが合わなければ、その需要の拒否として報告する」.
The existing §6.3 rule also requires 「二つの関連型の出力を等しいとし、需要を一つにまとめる」,
including 「impl を選ぶ前、保留のままでも行う」. Named requests are outputs;
matching and ambiguity continue to use only unnamed inputs. The new predicate
never tests a prospective implementation to filter the head-candidate set.
The supplied turn-31 decision is authoritative even though this checkout's
spec snapshot does not yet contain its new sub-bullet.

`GeneralNominalCenteredHeadAllocMergedConflict` defines:

- `MergedClass`: a recorded nonreflexive alias edge belongs to the focus class.
- `HistoryModels`: the original source and its root centers, every recorded
  total packet, and every recorded historical effect hold in one assignment.
- `ClassEquations`: all named requests in the entire alias class with the same
  name have equivalent values; every already-recorded implementation in that
  class satisfies its live effects on the current request union. This includes
  requests appearing only on the newly merged side.
- `ContextPresent`: a selected list of current ordinary atoms and a selected
  list of registered class demands.
- `ContextModels`: `HistoryModels`, those ordinary atoms, and those supporting
  classes' `ClassEquations` hold jointly.
- `MergedOutputConflict`: the class is merged, some such context is inhabited,
  and no model of that context also satisfies the focus `ClassEquations`.

This is a precise feasible-subjournal definition of a contradictory class
extension. Optional supporting atoms/classes matter: deleting all other merge
constraints could lose an interaction between classes, while requiring the
entire already-inconsistent journal would recreate the turn-30 failure.
The positive context witness prevents deriving this diagnostic merely from
an unrelated empty journal. `history_entails_clear` excludes it when the
historical journal already entails the focus equations. `conflict_same_class`
proves identical merged-conflict status for aliases.

The definition certifies incompatibility of currently recorded constraints;
it does not identify the first historical merge responsible for an error.
In particular, later equality feedback may contribute atoms to a context.
It also does not assert that `MergedOutputConflict` is equivalent to empty
current `Models`: pairwise raw merges through a member with no output requests
need not yet record every whole-class equality. `class_models_exclude_conflict`
therefore retains its explicit premises that the full model satisfies all
registered class equations and the focus equations. There is no hidden
historical-causality or whole-class-coverage assumption in the twelve-law proof.

## V7 priority and differences from V6

`B4TargetV7.SourceBoundary` adds only the key-independent
`MergedOutputConflict : Registry → State → Demand → Prop` field. Step, Initial,
models, evidence, registry checking and declaration matching are retained.
The new `RejectReason`, `Local`, and `Classify` use this exact priority:

1. If there is no merged-output conflict, apply V6 literally.
2. In a conflicted class, a known-root K2 reason retains rejection priority.
3. Otherwise, two distinct head survivors yield ambiguity.
4. Otherwise, the merged-output conflict yields rejection, even when input
   heads are unknown or an ordinary inspection would be pending.

Thus a merged conflict never becomes pending, and no unique implementation
must be chosen to diagnose contradictory requests. Under merged conflict,
two survivors yield ambiguity even if another ordinary inspection would have
been pending. This is the explicit new ambiguity exception; it is not claimed
to be V6's old safe-ambiguity rule. Existing post-choice `OutputConflict` keeps
its old unique-head rule whenever the merged conflict is absent.

`selected_iff` says precisely that V7 selection is V6 selection plus absence of
`MergedOutputConflict`. `conflict_not_pending` and `merged_unique_rejected`
certify the new priorities. `local_total` and `local_functional` are proved.
`Classify` recursively combines V7 local nodes with selected child dictionaries.
The five clauses of `Statement` retain their shape: only Exact,
DictionarySound and NoFalseRejection now refer to V7 Local/Classify/RejectReason;
SaturationTotal and OrderIndependent retain the underlying V6 types.
No V5 or V6 file was changed.

## Closed bridges and canonical executor

`GeneralNominalCenteredHeadAllocV7Composition.twelveLaws` proves all twelve
fields without a residual hypothesis:

| Fields | Proof connection |
| --- | --- |
| `progress`, `closure`, `stepModels`, `dictionaryRefl`, `initialReorders` | Same operational boundary; reuse the closed Alloc laws. |
| `execution`, `halted` | Reuse actual terminal execution and progress, with the new V7 final chooser. |
| `frontierLocal`, `localIdentity` | New frontier protocol from V7 totality and functionality. |
| `whereAccessible` | Every V7 selected-child edge is an old selected-child edge. |
| `treeExecution` | The new executor resolves the V7 frontier. |
| `canonicalLocalOrder` | New V7 observations over the existing two-way journal permutation simulation. |

The new `LiftedExit` and `finalState` in
`GeneralNominalCenteredHeadAllocV7KernelExecutor` constrain **V7** Local.
Reusing the old chooser would have retained only V6 observation agreement.
`conflict_related` transports the historical journal, selected ordinary atoms,
registered supporting classes, whole-class equations and recorded live effects.
`kernel_related` and `kernel_order` then transport the complete V7 classifier.
`GeneralNominalCenteredHeadAllocV7Canonical.canonical_exit_lifting` closes the
new lift, and `GeneralNominalCenteredHeadAllocV7Executor` exposes the Alloc
executor over the compiled registry. Its `canonicalLocalOrder`, `exact`,
`saturationTotal`, and `orderIndependent` are unconditional. Registry-order
quantifiers still cover all shared reachable states and all demands.

## Exact evidence field for dot

The obsolete prior-shaped field is not used. Dot's new target is exactly

```lean
B4SkeletonV7.EvidenceNode
  (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles)
```

It is also named `GeneralNominalCenteredHeadAllocV7Composition.EvidenceNode roles`.
For `b := GeneralNominalCenteredHeadAllocV7Boundary.boundary roles`, its fully
expanded obligation is:

```lean
∀ r, b.Checked r → ∀ s root, B4TargetV7.Reachable b r root s →
  ∀ model, b.Models s model → ∀ d key children dictionaries,
    (d = root ∨ b.Generated r s root d) →
    b.Stable r s d →
    (∀ child, child ∈ children → b.Stable r s child) →
    B4TargetV7.Local b r s d (.selected key children) →
    CommonRoleOutermostResolver.All₂
      (fun child dictionary => b.Evidence r s model child dictionary)
      children dictionaries →
    b.Evidence r s model d (.node key dictionaries)
```

The Local premise includes SafeKnown, unique head selection,
`¬ OutputConflict r s d key`, and `¬ MergedOutputConflict r s d`.
`B4SkeletonV7.EvidenceAt b r s root` names the suffix beginning at `∀ model`.
It is a pointwise obligation, not a proof of the global field.

The other remaining production field is exactly

```lean
B4SkeletonV7.GeneratedChildren
  (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles)
```

It quantifies over a reachable state, a root/generated stable demand, and an
actual V7 selected frontier, and requires every listed child to be generated.
There is no recursive classification or child-evidence premise in that field.

`B4SkeletonV7.dictionary_evidence` uses these selected-only obligations and
one reachable final snapshot's stability closure throughout its finite
structural dictionary proof. `B4SkeletonV7.b4_of_bridges` assembles the target.
For the concrete successor, the final exact conditional theorem is

```lean
GeneralNominalCenteredHeadAllocV7Composition.composition
  (node : GeneralNominalCenteredHeadAllocV7Composition.EvidenceNode roles)
  (generated : GeneralNominalCenteredHeadAllocV7Composition.GeneratedChildren roles) :
  B4TargetV7.Statement
    (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles)
    (GeneralNominalCenteredHeadAllocV7Executor.executor roles)
```

`dictionarySound` has the same two hypotheses and returns the corresponding
V7 DictionarySound clause. There are no additional canonical-order, progress,
choice, baseline, or packet-assembly hypotheses in this composition.
Neither global production field is asserted as proved.

## Both regressions and the remaining completion obstruction

`GeneralNominalCenteredHeadAllocV7MergeRegression.regression` reuses the actual
checked Initial → P installation → R merge → terminal continuation from turn
30. Initial and post-install models are inhabited. The final generated R class
now has `final_rejected`, `final_not_selected`, and `final_not_pending`.
This is the same actual terminal trace, not a claim that it equals the new
canonical executor's chosen result from the initial source.

The parent is different: its class has no merge, its head is still uniquely
applicable, and its two child edges and packet are already recorded.
`GeneralNominalCenteredHeadAllocV7ParentBaseline.stable_selected_counterexample`
proves the checked/WF initial source, actual reachability, stability, selected
parent P, rejected child R, recorded parent children, and empty full journal.
`not_headBaseline` and `not_selectedCompletion` are closed negative theorems
for the concrete fixture roles. No final-state invariant is assumed.
This is an **overstrong proof-interface obligation**, not a new semantic
question or a reason to reject the parent locally. Its tree can retain the
selected parent and rejected child. An installation/extension obligation should
be needed only when the selected children's production is not already recorded.
`PacketAssembly` and `ChoiceFromCommon` remain unproved and unrefuted; the
universal positive baseline cannot be their unconditional entry point.
The witness does not refute GeneratedChildren or Statement.

For cycle 199, commit `45f6868be` was read from the local origin repository
without fetching or changing refs. Its exact declaration/source identities
were ported to separate `GeneralNominalCenteredHeadAllocV7Cycle199*` modules;
the dot files and their prior-interface refutations were not edited.
The single implementation has head Int and associated body `nominal0[Int]`,
while the root requests Int. The registry encoding is the identity here.
`GeneralNominalCenteredHeadAllocV7Cycle199Regression.terminal_regression`
proves checked Initial, an inhabited journal, actual Step stability, V7
rejection, and `B4SkeletonV7.EvidenceAt` at that snapshot.
`evidenceAt` is vacuous specifically because every root/generated demand is
that rejected root (`no_selected`), not because models are absent. This proves
that the cycle-199 terminal fixture does not violate the new evidence field;
it does not prove the global field assigned to dot.

## Checks and review

All fifteen new modules are imported from `lean/Yulang.lean`. The new audit
`lean/Audit/GeneralNominalCenteredHeadAllocV7.lean` checks all 155 public
theorems, including the generic recursive evidence and composition proofs.
Only the two source-composition production hypotheses remain; internal family
lemmas' Good/Supported premises are supplied by the actual trace in the closed
negative results.

No configured or callable prover role was available. The primary constructed
the bounded derivations directly. Independent read-only reviews checked the
new conflict definition, priority, permutation/executor transfers, both
regressions, and the corrected selected-only evidence/composition interface.
They confirmed the distinction between present-subjournal incompatibility and
first historical error attribution, and between the false completion interface
and the unrefuted generated-child field.

Exact final command results are recorded below after verification.

| Exact command from the repository root | Exit |
| --- | --- |
| `cd lean && lake build --wfail Yulang.GeneralNominalCenteredHeadAllocV7ParentBaseline Yulang.GeneralNominalCenteredHeadAllocV7Cycle199Regression` | 0 |
| `cd lean && lake build --wfail Yulang` | 0 |
| `cd lean && lake build --wfail` | 0 |
| `cd lean && lake env lean Audit/GeneralNominalCenteredHeadAllocV7.lean` | 0 |
| `git diff --check` | 0 |

All 155 audited declarations use only `propext`, `Classical.choice`, and
`Quot.sound`. Independent audit review confirmed exact coverage with no missing
or duplicate theorem entries. Previous bytes of `lean/Yulang.lean` and
`notes/design/INDEX.md` are preserved; the remaining changes are fifteen new
modules, one new audit, and this note. The new modules passed the forbidden
construct scan. No git refs were changed; HEAD remains
`de0f1a3ad763414cb16f6e829a52f158b6c5fd34` on `astra2/centered`.
