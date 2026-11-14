# Centered completion: a reachable alias-class obstruction

Status: Draft — checked counterexample to reachable selection implying Joint;
not a counterexample to the stable V5 field.
Date: 2026-11-14.
Scope: unrestricted centered Step and administrative ground boundary G′.

## Result and stopping point

An actual ground InitialSource reaches, by one installation and one centered
merge, an inhabited state where G′ selects a generated demand with a nonempty
child list but Joint is false. Required raw and centered merges are already
closed at that demand. The centers are the identical source name `1`; no
provenance information is missing.

The main closed theorem is
`Yulang.GeneralNominalCenteredCompletionAliasObstruction.reachable_selected_without_joint`.
It proves checkedness, ground reachability, an explicit centered model,
generation of the selected demand, its G′ selection, nonempty children, and
the negation of Joint. It has no premises.

`reachable_frame_without_completion` additionally constructs an actual selected
Frame and proves it cannot be completed. `no_completion` proves this for every
Frame for the selected key and children; its explicit parameters are the
candidate plan and that Frame proof.

This meets the task's instruction to stop when a completion component fails at
a reachable state. **Stability is not proved.** The result refutes the proposed
invariant over all reachable selected states after merge closure. It does not
refute `UncoveredCompletion`, whose premises include stability, nor
`B4SkeletonV5.GeneratedChildren`. No termination result or evidence-node bridge
is changed or extended.

## Checked fixture and execution

The following is schematic Yulang for the checked declaration carrier; the
surface text has not been parser-checked. `Z` has zero ordinary arguments.

```yulang
role Start 'a:
role R 'a:
    type out
role Z:

impl Start (list 'a):
    where 'a: R(out = int)
    where 'a: R

impl R int:
    where Z
    type out = list int

// Root demand: (list int): Start
```

The roles are `Start = 0`, `R = 1`, `Z = 2`; declarations have keys `1` and `2`.
The root has identity `100`, point endpoints `(0,0)`, and the source model
assigns `list int` to source `0` and `int` to source `1`. Both declarations pass
all declaration checks, including capture-stable structural descent. The
nullary Z demand ensures that the selected R candidate has a
nonempty child list; it need not have a visible implementation.

1. `AliasTrace.first_step` installs the parent with empty support. Its two
   generated R demands have point endpoints `(1,1)` and the same explicit
   center `1`. The requested occurrence carries an allocated target `output`
   for `out`; the plain occurrence requests no associated output.
2. The installed parent packet's named materialization constrains `output` to
   `int`. `AliasTrace.output_int` extracts that fact from every raw journal
   model of the resulting merged state.
3. `AliasTrace.second_step` merges the two generated R occurrences, again with
   empty support. The merge produces the alias edge. Its output-atom list is
   empty because the plain occurrence has no requested outputs.
4. `AliasLocal.ready` proves registration and both required merge closures.
   `AliasLocal.child_selected` proves G′ selection of key `2` at the plain
   occurrence. Its private branch has no root output request, so it can use
   the current context model and emits the nullary Z demand.
5. Joint additionally requires a branch for the requested occurrence in the
   same journal model. Its materialization requires `output` to have nominal
   head `list`. `requested_branch_incompatible` combines that fact with
   `output_int` and scalar/nominal separation. `no_joint` follows.

Here `AliasSource`, `AliasTrace`, `AliasLocal`, and `AliasObstruction` abbreviate
the corresponding `GeneralNominalCenteredCompletionAlias…` namespaces. All four
modules are imported from `lean/Yulang.lean`.

The source is not merely satisfiable in a candidate-private model:
`AliasTrace.finish_model` constructs `CenteredSteps.Models finish exampleModel`.
Likewise, reachability is the actual two-step path from the source, not a
hypothesis about a hypothetical execution.

## Exact implementation mismatch

`GeneralNominalDemandMerging.outputAtoms` only equates targets for output names
requested on **both** sides. This correctly adds no equations when one side
has an empty request list, but the rest of the implementation must still
retain the other side's conditions when classifying the shared demand.

G′ adds registration and merge closure to the old per-occurrence Survivor.
The `GeneralNominalRecursiveCandidates.Consistent` conjunct of `Prepared` supplies a witness for
that occurrence's private context and materialization. It neither includes the
other occurrences in its alias class nor quantifies over the historical packet
ledger. `GeneralNominalJointCandidates.Joint` does both. Explicit center
identity establishes the merge; it cannot make contradictory named-output
conditions jointly satisfiable.

The relevant owner decisions are already recorded in [spec §6](../../spec/06-roles.md):

- §6.3: 「同じ入力の需要はまとめる」 and 「impl を選ぶ前、保留のままでも行う」.
  The example performs this merge before classifying the plain child.
- §6.3: 「等式そのものは捨てず、通常の制約・同じ入力の需要のまとめ・再帰型（K2）の判定には使う」.
  The parent's named equation remains in the journal; its output is not used
  to justify inspection. Both R inputs are already source-known `int`.
- §6.5: 「実際の引数の名前（中心）は明示して持つ」 and
  「実装が共有の情報を失ったことを理由に需要を保留にする規則は足さない」.
  The two occurrences carry exactly the same center, so a provenance-pending
  rule would not address this example.

No new language decision is needed to explain the failure of this invariant:
merge closure alone is weaker than applicability of the merged class. A
possible additive repair is a class-wide local applicability test retaining
all named requests and checking them against the current journal in one
assignment. In this example the merged R class should fail the incompatible
output requirement. This note proposes that implementation direction; it does
not change the boundary, Step, V5 statement, or rejection/pending rules.

## Remaining field and hypotheses

The target remains exactly:

```lean
B4SkeletonV5.GeneratedChildren
  (GeneralNominalCenteredAdministrativeLocal.boundary roles)
```

The established sufficient residual remains
`GeneralNominalCenteredSelectedCompletion.UncoveredCompletion roles`. It
quantifies over a checked registry, a ground-reachable state, a generated
focus, **Stable registry state focus**, G′ selection, nonempty children, and
absence of an already committed selected Frame, and concludes existence of a
Frame with Completion. General Joint, raw value support, and a common centered
model under those full premises are still unproved. No hypothesis was added
to the existing twelve-field composition.

For this fixture, stability and absence of a committed selected Frame are not
certified. No negation of `UncoveredCompletion` or of `GeneratedChildren` is
claimed. The global value-support and model-extension obligations are not
resolved by the counterexample. EvidenceNode remains with the other worker.

## Checks and review

Commands run from the repository root (output redirected to the corresponding
`/tmp/centered-12-*.log` files):

| Command | Exit |
| --- | --- |
| `cd lean && lake build --wfail Yulang.GeneralNominalCenteredCompletionAliasSource Yulang.GeneralNominalCenteredCompletionAliasTrace Yulang.GeneralNominalCenteredCompletionAliasLocal Yulang.GeneralNominalCenteredCompletionAliasObstruction` | 0 |
| `cd lean && lake build --wfail` | 0 |
| `cd lean && lake build Yulang` | 0 |
| `cd lean && lake env lean Audit/GeneralNominalCenteredCompletionAliasObstruction.lean` | 0 |

The new audit covers every public theorem in the four modules. Dependencies
are restricted to `propext`, `Classical.choice`, and `Quot.sound`.
Development builds that failed during construction are not counted as passing
checks. Rust and surface parser checks were not run.

The configured/callable `prover` role was unavailable; no prover agent ran.
The primary constructed this bounded derivation. A separate read-only reviewer
checked the concrete trace, model inhabitation, merge closure, and exact scope
of the counterexample. The review agrees that stability remains outside the
proved result. No existing definition, Git ref, or frozen document was changed.
