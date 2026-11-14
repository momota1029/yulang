# Centered completion components and registered terminal confluence

Status: Draft — checked additive results, not a completed B4 composition.
Date: 2026-11-14.
Scope: the unrestricted centered Step and the administrative centered ground
boundary G′. Existing definitions remain frozen.

## Result

G′ still has eleven unconditional V5 fields in this worktree. This change proves
initial-state Joint and empty value support, characterizes the remaining
completion components, and proves reachable registration equals generation.
It also constructs an actual **registered-root** terminal fork. Consequently,
literal terminal Local confluence is false even when restricted to generated
demands. No claim about the fixed executor's order field or two successful
dictionaries follows from that counterexample.

New modules:

- `GeneralNominalCenteredCompletionParts`: initial production components and
  exact current-frame support/model characterizations.
- `GeneralNominalCenteredRegisteredLocal`: registration/generation equivalence,
  unregistered classification, and the exact domain split for Local agreement.
- `GeneralNominalCenteredRegisteredFork`: one source, two actual two-step paths,
  two inhabited halted states, and different selected frontiers at their root.

## Authority and the distinction between models

The owner requires 「同じ入力の需要はまとめる」 and 「impl を選ぶ前、保留のままでも行う」
(spec/06-roles.md §6.3). G′'s administrative readiness already enforces the
required merging before selection. This is a statement about aliases, not a
proof that all branches of the merged class have a common assignment.

The center decision says 「実際の引数の名前（中心）は明示して持つ」 and
「実装が共有の情報を失ったことを理由に需要を保留にする規則は足さない」 (§6.5).
No new pending rule is introduced here. The unresolved bridge is an
implementation/proof obligation of the frozen guards.

The order decision is 「兄弟の順序によらず結果は同じになる」 (§6.3), including
「保留・選択・曖昧・拒否、辞書の中身」. The terminal fork below does not overturn
that decision. It identifies literal endpoint names in the current Lean Local
frontier as information that is not canonical even after halting.

For an exact selected `Frame`, `frame_branch` supplies

```lean
∃ model, plan.packet.Holds model
```

and `frame_context_model` supplies a model of the current nominal context.
Neither conclusion includes all historical packets, stored sites, or center
plans. The source of the witness is `RecursiveCandidates.Prepared.Consistent`,
which quantifies over the candidate's private state and materialization.
It does not quantify over `SaturationState.Models` or `CenteredSteps.Models`.
Thus the local Survivor witness cannot simply be reused as a journal witness.

## Completion: what is proved and what remains

For any exact current Frame and any support list, `frame_value_iff` proves:

```lean
ValueSupport.PacketGuard state.erased plan.packet support ↔
  ValueSupport.DecisionGuard registry state.erased focus support
```

The reverse implication uses the decision guard's all-candidate read condition
for this visible declaration. This removes no support or dependency condition:
the right side still includes raw admissibility and value grounding.

At `CenteredSteps.initial context root`, `initial_joint` derives Joint from the
Frame's branch witness. The initial journal is empty and its only stored site
is the root; all alias-branch obligations use that witness. No additional
Joint premise is assumed. `selected_initial_value` derives the value guard
with empty support: each head is a source head at this initial snapshot.

For a literal point root, `initial_completion_iff` consequently proves the
single residual statement:

```lean
Completion registry (initial context root) plan ↔
  ∃ model, plan.packet.Holds model ∧ plan.Equations model
```

This is an initial-state result, not an induction over arbitrary reachable
states. Even here the centered branch witness on the right remains explicit.
The registered Display fixture independently constructs that witness for its
concrete plans, universally over their source models.

For general reachable selected Frames, `completion_parts_iff` is exact:

```lean
Completion registry state plan ↔
  Joint registry state.erased.current focus key ∧
  (∃ support, ValueSupport.DecisionGuard registry state.erased focus support) ∧
  ∃ model, CenteredSteps.Models state model ∧ plan.Holds model
```

`common_model_iff` expands the final conjunct into one assignment satisfying
all of these conditions simultaneously:

1. the complete raw journal;
2. the new raw packet branch;
3. every recorded site's center interval;
4. every earlier centered plan's equations;
5. the new plan's equations.

The following general steps remain unproved, including at stable reachable
states:

- **Joint:** alias closure does not supply its recorded-key agreement and its
  single model for every alias-related branch. The existing
  `GeneralDictionaryJointMergeResidual.separate_joint_merge_iff` still needs
  `Shared` even when each old class independently has same-key Joint.
- **Value support:** centered head justification uses centered input, output,
  and merge facts. Forgetting centers maps these models to raw models, in the
  wrong direction for transferring universal head entailment to every raw
  support-slice model. A suitable extension of raw slice models, preserving
  observed values, and the raw admissibility/grounding conditions remain.
- **Common centered model:** the current candidate witness must be extended
  compatibly with the complete journal and all center equations above.

Accordingly `UncoveredCompletion` remains open on its original domain:
checked registry, reachable state, generated focus, stability, selected
nonempty children, and absence of any committed exact current Frame. This
change does not collapse its three general obligations into one proved lemma.
No source-reachable production counterexample is asserted.

## Registration and the unregistered case

`registered_iff_generated` proves, for every G′-reachable state,

```lean
Registered state demand ↔ Generated state.erased.current root demand
```

The proof tracks actual installation edges. Administrative enqueue cannot add
an arbitrary observer: its focus must already be generated and registered.
Every centered site has a raw partner with the same occurrence.

For an unregistered demand, centered root/candidate cycles are impossible
because their witnesses include a registered site. Administrative pending
blocks selection, ambiguity, and zero-candidate rejection, but retains the
existing rejection priority. Define

```lean
LegacyReject registry state demand :=
  FeedbackK2.RootK2 state.erased.current demand ∨
  FeedbackK2.CandidateK2 registry state.erased.current demand
```

The module proves exactly:

```lean
Local registry state demand .rejected ↔ LegacyReject registry state demand
Local registry state demand .pending  ↔ ¬ LegacyReject registry state demand
```

The legacy cycle predicates already imply that root heads are known. Thus no
extra known-head conjunct is needed in this formula. Unregistered does not
by itself imply pending.

`local_agreement_iff` reduces all-demand Local agreement between reachable
snapshots to agreement on demands generated at **either** endpoint, together
with `LegacyReject` equivalence for demands generated at neither endpoint.
Restricting only to the intersection would miss one-sided registration. The
outside rejection equivalence is explicitly required, not proved harmless.

## Actual registered terminal fork

Reuse the earlier source with three names: 0 denotes `list int`, and names 1
and 2 both denote `int`. Its cached list descriptor initially contains bounds
`(1,2)`. This time the actual source root is **Display name 0**, identity 100;
its root argument is the literal point `(0,0)`. The registry contains only
`Display (list a)` with child `Display a`.

Both paths start at this same `InitialSource`, with ground label
`[list int]`, and use the unchanged centered Step:

| Path | First action | Second action | Final root Local |
| --- | --- | --- | --- |
| false | certified descriptor revision to `(1,1)` | guarded root installation | selected key 1, child input `(1,1)` |
| true | certified descriptor revision to `(2,2)` | guarded root installation | selected key 1, child input `(2,2)` |

The revision changes neither semantic model set. The installability proofs
supply actual Joint, raw value support, centered decision/inspection guards,
and a common centered model. Each path records exactly its emitted child.
The root is generated, registered, and administratively ready at both ends.

`stable` checks every constructor of centered `At`. Installed root proposals
are already committed; the scalar child has no matching declaration. Cross
merges between `list int` and `int` are impossible. Current-context models
already satisfy the raw journal, so equality feedback adds nothing. Existing
descriptors are point-closed. Original names are known, and models assigning
unused reserved names different scalars rule out either refresh constructor.

The checked conclusions include:

```lean
∀ side next, ¬ Step registry observer (finish side) next
∀ model, Models (finish false) model ↔ Models (finish true) model
¬ TerminalLocalConfluence GeneralDeclarationExamples.roles
¬ TerminalGeneratedLocalConfluence GeneralDeclarationExamples.roles
```

The last law quantifies only over the union of generated demands; the witness
is the actual root, which lies in both sets. The two literal child lists differ,
while `child_semantics_agree` proves the same child invocation identity and
role, with equivalent input values in every common model. Both ends have a
concrete model, so this equivalence is not vacuous.

This refutes the proposed **literal** arbitrary-terminal Local route. It does
not refute the fixed choice executor's `CanonicalLocalOrder`; that theorem
compares particular chosen endpoints under reordered registries. The fixture
also does not exhibit two successful dictionaries or distinct final resolved
diagnostics: its scalar children have no matching declaration. Agreement
modulo canonical child identity and input equivalence remains a suitable
semantic objective, but transporting that objective to the current literal
Local field requires an additional canonicalization or comparison bridge.
No such general bridge is claimed here.

## Exact remaining fields and scope

The two requested fields remain:

```lean
B4SkeletonV5.GeneratedChildren
  (GeneralNominalCenteredAdministrativeLocal.boundary roles)
GeneralNominalCenteredAdministrativeComposition.CanonicalLocalOrder roles
```

The first still follows conditionally from `UncoveredCompletion`. For the
second, the exact fixed-executor residual `FinalLocalAgreement` remains open;
its stronger `TerminalLocalConfluence` sufficient hypothesis is now refuted,
even on generated roots. EvidenceNode remains the separate worker's task.
The P/W trigger execution is unchanged. No new owner decision is requested.

The `yulang-proofs` skill was applied. No configured or callable `prover` role
was available; no such agent ran. The primary constructed these bounded proofs,
with separate read-only reviews of component quantifiers, registration, the
actual terminal execution, and the final counterexample's scope.

## Validation

Final commands from `lean/`, all exit 0:

```text
lake build Yulang.GeneralNominalCenteredCompletionParts Yulang.GeneralNominalCenteredRegisteredLocal Yulang.GeneralNominalCenteredRegisteredFork
lake build Yulang
lake env lean Audit/CenteredCompletionRegistered.lean
```

The module build completed 892 jobs. All 50 public theorems have audit entries;
their dependency union is exactly `propext`, `Classical.choice`, `Quot.sound`.
Private helper proofs are covered transitively. Separate reviewers also ran
each module directly with `lake env lean`, all exit 0.

From the repository root, `python3 /tmp/yulang-centered-completion-scope.py`
exited 0. It checks frozen-file preservation, append-only changes, all three
imports, all public theorem audit entries, excluded proof constructs, trailing
whitespace, and the branch name. No Git references were changed.
