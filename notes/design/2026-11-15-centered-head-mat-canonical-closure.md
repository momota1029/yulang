# Canonical exits and live class retention for total materialization

Status: Draft proof record. Date: 2026-11-15. Scope: astra2-centered-27,
the existing total-materialization successor, its justified caches, and its V6
Local. No language definition, target, executor, Step, or Initial is changed.

## Closed result

`Yulang.GeneralNominalCenteredHeadMatCanonicalClosure.canonical_exit_lifting`
proves the frozen
`GeneralNominalCenteredHeadMatStepExecutor.CanonicalExitLifting roles`.
It has only the `roles` parameter. Its source assumptions remain those already
quantified by that obligation: a checked registry, a reachable state from the
existing ground-point WF Initial, and an empty packet list at the shared start.
No permutation, model, trusted-ledger, or progress producer is assumed.

The same namespace exports `halted`, `saturationTotal`, `canonicalLocalOrder`,
and `orderIndependent`. The latter two retain the existing executor and exact
frozen target propositions. In particular, canonical local order quantifies
over every demand and frontier at any state reachable under both reordered
registries. It is not limited to generated demands, initial starts, successful
results, or a quotient of child records.

`halted` and `saturationTotal` use the preceding unconditional progress theorem;
their proofs do not need exit lifting. Exit lifting closes the remaining
canonical-order premise. Existing execution, closure, stepModels,
frontierLocal, localIdentity, whereAccessible, treeExecution, dictionaryRefl,
initialReorders, and exactness continue to use the same boundary and executor.
Thus all twelve previously identified bridge laws are unconditional for this
successor with V6 Local. This is not the full B4 statement: child production
and dictionary evidence remain separate.

## Governing decisions

The frozen spec §6.3 states, 「兄弟の順序によらず結果は同じになる」 and
「連言の項を入れ替えても、結果（保留・選択・曖昧・拒否、辞書の中身）は変わらない」.
The registry relation retains declaration/clause identities and all source
content while permitting declaration and where-clause enumeration changes.
The fixed canonical-registry executor implements the requested declaration
order independence without requiring arbitrary terminal states to coincide.

The same section states, 「同じ入力の需要はまとめる」 and describes retaining
output equations. The later owner instructions in turns 15 and 22 require
head-only matching, all class output requests, and cached heads justified by
source constraints plus settled outputs. The proofs preserve those existing
successor definitions. They neither filter candidates by outputs nor add a
pending case. Ordinary constraints and K2 retain the full corrected journal;
cached observations retain their exact trusted-slice certificates.

## Concrete permutation correspondence

The new modules have prefix `GeneralNominalCenteredHeadMatPermutation`.

- `Plans.Pair` preserves the actual input center site, head preparation,
  historical packet readbacks, private context, total Inputs/Outputs,
  emitted schema, class effects and defaults. It is constructed by the
  existing registry/declaration rebase followed by replacement of allocation
  metadata with the counterpart's current enumeration.
- `Raw.Raw` relates current contexts up to metadata membership, pairs packet
  observations, and preserves raw-site membership, edges, and aliases.
  Raw-site lists need not be equal: this successor emits centered children
  in source where order. The source identities and canonical child edges are
  unchanged. Centered-site membership is likewise retained.
- `Raw.Snapshot` retains historical raw and centered sites and aliases.
  An effects-only equality of request lists would be insufficient:
  `Trusted.ClassReadback` also inspects the producing effect's historical
  centered sites. The snapshot relation preserves those data explicitly.
- `Ledger.Related` has a coherent relation on complete plans and paired
  effect journals. `models` relates every full corrected model using the
  same assignment. `trusted`, `facts_models`, `readback`, `class_readback`,
  `justifies`, and `cache` transport exact historical support slices.

Coherence is keyed by **plans**, including the input center site. Current
novelty is `¬ Committed state plan`; it does not imply that the raw packet
has never appeared. `Simulation.Recorded` states that every recorded plan
is committed and is preserved through every actual constructor. Installation
therefore gives a fresh plan on each side, sufficient to extend the coherent
relation even if a raw packet repeats with different centers. No raw-packet
novelty premise is substituted for the actual guard.

`Administrative.administrative` transports enqueue, justified refresh,
full-model equality feedback, and reobservation. Reobservation copies the
descriptor entries, relates the resulting snapshots, and transports both raw
restriction and exact trusted-cache soundness. `Administrative.merging`
retains the relation across the unchanged merge operation.

`Install.counterpart_enabled` constructs an actual counterpart Effect. It
transports head-only uniqueness, readiness including defaults, safe Local,
exact cache, total materialization, choice compatibility, actual-position
safety, alternatives, and the entire common installation model. That common
model includes every prior effect's live equations in the enlarged class.
`installed_related` extends both plan and effect journals.

`Simulation.at_forward`, `step_forward`, and `step_backward` cover every
unrestricted successor constructor. `observations` proves literal Local
equivalence at an arbitrary fixed target registry with the appropriate role
signature. `steps_backward` lifts actual finite traces, and `halt_reflects`
reflects termination of a corresponding terminal state.

## Canonical executor connection

`packet_free_ledgers` derives empty plans and effects from an actual successor
trace whose final packet list is empty. `packet_free_self` initializes the
relation from that fact. `packet_free_steps` replays the trace under any
registry: an installation is impossible in such a prefix, and every remaining
constructor is registry independent. This does not project the new refresh
certificate into an old Step.

For a checked reachable packet-free state, initial reordering and passive-prefix
replay make the identical start reachable under the canonical registry. The
preceding `HeadReadback.progress` supplies accessibility there. Its fixed
`terminalState` therefore has an actual canonical exit. Backward simulation
produces an exit under the original registry, reflects halting, and relates
all Local observations at the canonical target. This is exactly `LiftedExit`.
The frozen composition then supplies canonical local order and V6 order
independence by congruence of canonical registries.

## General completion progress

`GeneralNominalCenteredHeadMatCompletionRequests` proves a new reachable
source invariant. A generated child's output request identities depend only
on the retained source seed, parent invocation, declaration ID, clause ID,
and source output syntax. `outputTarget` chooses either the deterministic
purpose-2 output binder or the deterministic purpose-5 equation target;
neither depends on descriptor captures. This covers explicit output binders,
not only declarations without binders.

`same_outputs` uses source identity injectivity and checked declaration/clause
keys to prove that two formed occurrences with the same invocation identity
have exactly the same output list. `invariant` carries this property through
the existing `Built` history together with registration of every alias-edge
endpoint. The actual Step-to-Built theorem discharges its source origin.

`install_requests` proves membership equivalence between a registered root's
class requests before and after installing any current head Frame. If a newly
emitted site is already aliased to that root, the old alias path has a
registered representative of the new site's identity; `same_outputs` gives
the already-retained requests. Reflexive aliasing uses registration of the
root itself. Installation adds no alias edges. Duplicate or revised child
records therefore introduce no new request into an existing class.

`GeneralNominalCenteredHeadMatCompletionLive.effect_present` establishes
registration of every historical effect's root. `class_effects_install`
then transports its complete class equations. Consequently, on the actual
checked reachable boundary, for an effect whose registry and snapshot match:

```lean
InstallationModels state effect model ↔
  Models state model ∧
  GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan model ∧
  effect.Holds model
```

This is `installation_models_iff`. All post-install Live obligations, for
both the new effect and every historical effect, are discharged without an
extra preservation assumption. `common_successor_model` constructs the
successor journal model from those three common-model components.
`extension_iff` and `selected_installable_iff` expose precisely the remaining
choice and common-branch obligations.

## Exact remaining hypotheses

Canonical exit lifting, canonical local order, halting, saturation totality,
and order independence have no new hypotheses. Their original checkedness,
reachability and source restrictions are unchanged.

General SelectedCompletion is still conditional. The new namespace
`GeneralNominalCenteredHeadMatCompletionAssembly` names three sufficient
global obligations. They are not proved necessary, nor an exact decomposition
of possible failure. In particular, `PacketAssembly` quantifies over every
matching current effect with feasible chosen effects, not only selected or
stable foci:

1. `HeadBaseline roles`: every checked reachable selected node has a current
   journal model satisfying its positive `ChosenHead` predicate.
2. `PacketAssembly roles`: for a matching current effect, an inhabited current
   journal plus chosen effects extends to one model of that journal, the
   corrected packet Inputs/Outputs, and the chosen effects. It may change the
   assignment; it must preserve all three predicates. No future Live premise
   remains. Required construction includes ordinary capture constraints,
   actual projection readbacks, coherent emitted equations, child centers,
   and preservation of historical packet models.
3. `ChoiceFromCommon roles`: at a selected current effect with such a common
   branch model, recorded choices in its alias class have the chosen head key.

`selectedCompletion` proves the frozen `SelectedCompletion roles` from exactly
these three named premises; `generatedSelectedChildren` proves the existing
stable/reachable/generated child-production obligation from the same premises.
Neither theorem is an unconditional proof of GeneratedChildren.

No well-formed reachable stable counterexample was established. A considered
merge-created empty journal is not sufficient: equality feedback remains
enabled, so that snapshot cannot simply be reported as a stable witness.
No language decision is requested. Exhaustive K2 projections for multi-tag
rows and open tails remain unchanged; the permutation proof preserves the
existing cycle predicate and does not prove its projection completeness.
Dictionary evidence remains outside this worker's scope.

## Validation and review

The `yulang-proofs` skill was used. No registered/callable `prover` role or
configuration is available in this checkout; no prover agent ran. The primary
constructed the bounded derivation. Separate read-only source audit and fresh
independent proof review checked the actual source paths and exact canonical
quantifiers. The independent review also checked output-only binders, repeated
invocation identities, registered alias endpoints, and all historical live
effects. No proof defect was found.

All commands below ran from `lean/`; each exited **0**:

```sh
lake build --wfail Yulang.GeneralNominalCenteredHeadMatPermutationPlans Yulang.GeneralNominalCenteredHeadMatPermutationRaw Yulang.GeneralNominalCenteredHeadMatPermutationLedger Yulang.GeneralNominalCenteredHeadMatPermutationLocal Yulang.GeneralNominalCenteredHeadMatPermutationAdministrative Yulang.GeneralNominalCenteredHeadMatPermutationInstall Yulang.GeneralNominalCenteredHeadMatPermutationSimulation Yulang.GeneralNominalCenteredHeadMatCanonicalClosure Yulang.GeneralNominalCenteredHeadMatCompletionRequests Yulang.GeneralNominalCenteredHeadMatCompletionLive Yulang.GeneralNominalCenteredHeadMatCompletionAssembly
lake build --wfail Yulang
lake build --wfail
lake env lean Audit/GeneralNominalCenteredHeadMatCanonicalClosure.lean
```

The [new audit](../../lean/Audit/GeneralNominalCenteredHeadMatCanonicalClosure.lean)
lists every public theorem in the eleven new modules: **120**, with no missing
or duplicate entries. Reported dependencies are limited to `propext`,
`Classical.choice`, and `Quot.sound`; two theorems have no dependencies.
The independent reviewer reran the audit successfully.

From the repository root, `git diff --check` exited **0**. A source-scope check
confirmed that the only changed tracked files are append-only import additions
in `lean/Yulang.lean` and an append-only entry in `notes/design/INDEX.md`.
Every new module has a root import; no disallowed proof construct occurs in
the new modules. The branch and integration head remain `astra2/centered`
and `385a2cdb63a09008a29fc350353bd46ecccab543`.
