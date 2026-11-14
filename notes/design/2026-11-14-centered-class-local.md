# Centered class-wide applicability and the unchanged installation guard

Status: Draft — G″ has twelve unconditional V5 fields; child production remains conditional.
Date: 2026-11-14.
Scope: astra2-centered-13; additive modules only, unchanged centered Step and Initial.

## Result

G″ classifies a candidate using the existing per-occurrence Survivor together
with `GeneralNominalJointCandidates.Joint`. Joint requires one raw journal model
for the candidate branch at the focus and every registered occurrence in its
alias class, retaining all named-output requests. Its existing compatibility
condition for historical packets is also retained. No pending, K2, rejection,
ambiguity, or priority rule changes. The earlier two-declaration fixture is
rejected by the existing zero-survivor rule at its plain R focus.

All twelve previously established fields transfer to G″. The new canonical
executor transports Joint through the complete permutation simulation and
proves canonicalLocalOrder for the changed Local, including arbitrary demands.
The composition still takes exactly EvidenceNode and GeneratedChildren.
EvidenceNode was not investigated in this turn.

There is a further implementation mismatch: the unchanged installation rule
still requires uniqueness in the old per-occurrence classifier. Filtering by
Joint can leave one class candidate where the old classifier is ambiguous.
A checked, ground-reachable, inhabited example now certifies that mismatch,
including an exact Frame, value support, and a common centered model. This is
an obstruction to the unconditional reachable selected-to-installable lemma;
it is **not** a negation of the stable GeneratedChildren field.

## Existing fixture: the remaining step

All names in this paragraph are in
`Yulang.GeneralNominalCenteredClassLocalAliasProgress` unless qualified.
`no_committed_frame` proves that no Frame for the old selected key 2 and its
nonempty emitted children is Committed. Only root-to-R edges exist at this
snapshot; there is no outgoing edge at the plain R focus.

`equate_at` and `equate_step` construct an actual administrative equality step
from the old `CompletionAliasTrace.finish`: the journal entails `output = 1`,
but its raw context does not. The separating raw assignment gives `output` the
value `list int` and keeps the source model elsewhere. Thus `not_stable` proves
that the snapshot is not Stable even at the plain focus.

`stable_extension` reuses the existing executor to prove exactly:

```lean
∃ final, B4Target.Steps (Step registry root) finish final ∧
  Stable registry final root ∧ Stable registry final focus
```

It does not assert the same classification, missing children, or a model at
that final state. Persistence of the old mismatch to a stable extension remains
open. Consequently neither `¬ UncoveredCompletion roles` nor the negation of
G′'s GeneratedChildren is claimed.

## Authority and representation

The repair implements the existing [§6.3 decision](../../spec/06-roles.md):
「すべての名前なしの引数が同じものを指す」 demands satisfy
「二つの関連型の出力を等しいとし、需要を一つにまとめる」 and
「impl を選ぶ前、保留のままでも行う」. An occurrence with no output request
cannot discard another occurrence's request within that one demand.

The [§6.5 center decision](../../spec/06-roles.md) says
「実際の引数の名前（中心）は明示して持つ」 and
「実装が共有の情報を失ったことを理由に需要を保留にする規則は足さない」.
Both fixtures use the identical center name 1 for the two R occurrences.
No provenance-based deferral is introduced.

Concretely, `GeneralNominalCenteredClassLocalBoundary.fields roles` changes only
this field of `GeneralNominalCenteredAdministrativeLocal.fields roles`:

```lean
Survivor := fun registry state focus key children =>
  GeneralNominalRecursiveCandidates.Survivor
    registry state.erased.current.context focus key children ∧
  GeneralNominalJointCandidates.Joint
    registry state.erased.current focus key
```

`boundary` uses the unchanged remaining fields and the unchanged Initial.
`reachable_iff` is definitional equality with G′ reachability. `local_total`
and `local_functional` retain the generic V3 classification rules. In
particular, `alias_fixture_rejected` derives rejection using those rules after
Joint excludes the only raw candidate; it does not add a new category rule.
Joint's witness is a **raw journal model**, not yet a common centered model.

## Twelve fields and exact transport

The namespaces below all begin `Yulang.GeneralNominalCentered`.

| V5 field | G″ theorem or transfer | Change needed |
| --- | --- | --- |
| progress | `AdministrativeComposition.progress` | Unchanged Step/Initial; reused directly |
| closure | `AdministrativeComposition.closure` | Unchanged Stable/Generated; reused directly |
| stepModels | `AdministrativeComposition.stepModels` | Unchanged Step/Models; reused directly |
| dictionaryRefl | `AdministrativeComposition.dictionaryRefl` | Reused directly |
| initialReorders | `AdministrativeComposition.initialReorders` | Reused directly |
| frontierLocal | `ClassLocalBoundary.frontierLocal` | Rebuilt from class-wide total/functional Local |
| localIdentity | `ClassLocalBoundary.localIdentity` | New frontier's defining equality |
| whereAccessible | `ClassLocalWhere.whereAccessible` | Same finite identity rank, using selected raw Survivor and registration |
| execution | `ClassLocalExecutor.execution` | New lifted-exit choice; same actual execution relation |
| halted | `ClassLocalExecutor.halted` | New lifted-exit choice; same actual halt condition |
| treeExecution | `ClassLocalExecutor.treeExecution` | New diagnostic resolves G″ Local |
| canonicalLocalOrder | `ClassLocalExecutor.canonicalLocalOrder` | New proof transporting Joint and choosing a common canonical observation |

`ClassLocalOrder.local_iff` proves registry reordering at a fixed state.
`paired_local_iff` transports the new Local under the existing ledger relation;
`observations` specializes it to the reachable permutation relation.
`ClassLocalExecutor.canonical_exit_lifting` uses the existing reversible Step
simulation and this stronger Local correspondence. It has no residual
hypothesis. `ClassLocalExecutor.bridges` and `composition` have the exact
remaining input:

```lean
structure Remaining (roles : Roles.RoleDecls) : Prop where
  evidenceNode : B4SkeletonV5.EvidenceNode (boundary roles)
  generatedChildren : B4SkeletonV5.GeneratedChildren (boundary roles)
```

No V5 definition or previous executor is modified. The accessibility argument
is reused; no new centered-transition termination proof is attempted.

## Exact production reduction

`ClassLocalBoundary.selected_joint` supplies Joint directly.
`ClassLocalProduction.selected_frame` constructs a current-context Frame from
reachability, generated-focus membership, and G″ selection.

Filtering does not imply uniqueness before filtering. The named condition is:

```lean
RawUnique registry state focus key :=
  ∀ other children,
    GeneralNominalRecursiveCandidates.Survivor
      registry state.erased.current.context focus other children → other = key
```

`ClassLocalBoundary.selected_old_iff`, under Checked and G″ selection, proves
that old G′ selection is equivalent to RawUnique. With the same Checked and
selected premises and an exact Frame, `ClassLocalProduction.frame_installable_iff`
proves:

```lean
GeneralNominalCenteredBoundary.Installable registry state plan ↔
  RawUnique registry state focus key ∧ Feasible registry state plan
```

Here `Feasible` is exactly existence of a raw value-support PacketGuard and a
single assignment satisfying both the current centered Models and plan.Holds.
There is no additional Joint premise.

The conditional theorem `ClassLocalProduction.generatedChildren` has exactly
one named residual, `UncoveredFeasibility roles`, whose full quantifiers are:

```lean
∀ registry, (boundary roles).Checked registry → ∀ state root focus key children,
  B4TargetV5.Reachable (boundary roles) registry root state →
  Generated state.erased.current root focus → Stable registry state focus →
  Local registry state focus (.selected key children) → children ≠ [] →
  (¬ ∃ plan, Frame registry state focus key children plan ∧
    GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet) →
  RawUnique registry state focus key ∧
    ∃ plan, Frame registry state focus key children plan ∧
      Feasible registry state plan
```

Under that residual the proof constructs Installable, uses stability to obtain
Committed, and takes the actual packet edges. General RawUnique under these
**stable/uncovered** premises, general raw value support, and general common
centered-model feasibility are all undischarged. The following example shows
why RawUnique cannot simply be omitted from the reachable-state reduction.

## Reachable selected candidate blocked by the frozen Step

The new `ClassLocalChoiceSource/Trace/Local/Obstruction/Feasibility` modules
extend the old checked fixture with a third declaration. This is schematic
Yulang; the surface text was not parser-checked:

```yulang
role Start 'a:
role R 'a:
    type out
role Z:

impl Start (list 'a):
    where 'a: R(out = int)
    where 'a: R

impl R int:                 // key 2
    where Z
    type out = list int

impl R int:                 // key 3
    where Z
    type out = int

// Root: (list int): Start
```

The declarations pass the actual checker. `ChoiceTrace.first_step` installs
Start; `second_step` merges the two R sites with the same explicit center.
`ground_reachable` proves the actual source-to-snapshot execution;
`finish_model` supplies a centered model. At the plain R focus:

- `ChoiceLocal.raw_ambiguous` proves the frozen per-occurrence classification
  sees keys 2 and 3.
- `ChoiceObstruction.no_bad_joint` excludes key 2, since the other R request
  requires the already recorded `output = int`.
- `good_joint` provides one explicit raw model for key 3 at both occurrences.
- `class_selected` proves G″ selects key 3 with a nonempty Z child list.
- `not_installable` excludes **every** centered plan focused at this occurrence:
  its frozen Feedback Installable guard would contradict raw ambiguity.
- `reachable_class_selection_blocked` packages Checked, actual ground
  reachability, a centered model, generated-focus membership, G″ selection,
  nonempty children, and the universal installation exclusion, with no premises.
- `ChoiceFeasibility.frame`, `raw_decision`, `equations`, and `feasible` supply
  an exact Frame, empty-support raw value guard, and a common centered model.
  `not_raw_unique` and `not_committed` certify the remaining obstruction and
  absent packet edges. `joint_and_feasible_but_blocked` packages Joint and
  Feasible alongside failure of Installable.

The exact stale guard is
`GeneralNominalFeedbackSteps.Installable`'s per-occurrence
`GeneralNominalFeedbackK2.Local ... (.selected ...)` conjunct; its nested
Cycle Installable also retains the earlier local selection guard. This is not
list-order dependence or a new language choice. If the supervisor permits a
new transition relation, both old selection checks would need to use the same
class-wide candidate set as G″, with the remaining installation guards retained.
This turn preserves Step as requested and does not implement that extension.

No Stable assertion is made for the new snapshot. Turning it into a literal
GeneratedChildren counterexample would require a stable extension preserving
plain-focus selection and proving its independently allocated Z child remains
ungenerated. That argument remains open; no target field is declared false.

## Checks, theorem inventory, and review

The new audit `lean/Audit/GeneralNominalCenteredClassLocal.lean` lists every
public theorem in the eleven new modules by fully qualified name. It is also
the exhaustive theorem inventory; the central names and every residual are
listed above. All eleven modules are imported from `lean/Yulang.lean`.

Final commands, from the repository root (logs in `/tmp/centered-13-*.log`):

| Command | Exit |
| --- | --- |
| `cd lean && lake build --wfail Yulang.GeneralNominalCenteredClassLocalAliasProgress Yulang.GeneralNominalCenteredClassLocalChoiceFeasibility` | 0 |
| `cd lean && lake build --wfail` | 0 |
| `cd lean && lake build Yulang` | 0 |
| `cd lean && lake env lean Audit/GeneralNominalCenteredClassLocal.lean` | 0 |
| `git diff --check` | 0 |

The audit checks 149 public theorems; the only dependencies reported are
`propext`, `Classical.choice`, and `Quot.sound`. A separate filesystem check
confirmed that both tracked-file changes are strict appends, no other tracked
files changed, and every new module has a root import. The prohibited-token
search found no matches in the new proof modules or this note (search exit 1).
Development builds with elaboration errors and one interrupted slow build are
not passing checks. Rust tests and surface parser checks were not run.

The configured/callable `prover` role was unavailable; no prover agent ran.
The primary constructed this bounded derivation. A separate read-only reviewer
checked the changed Local, exact field quantifiers, canonical transport,
source-generated counterexample, value/common-model witnesses, and the scope
of stable_extension. The reviewer independently ran Lean checks successfully
and confirmed that no stable-field negation has been established.
