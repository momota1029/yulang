# Centered total materialization: packet and journal integration

2026-11-14, astra2-centered-21. This is a partial integration result. The corrected packet meaning, journal updates, support slices, and metadata invariants are checked. A successor operational Step and boundary are **not** assembled. None of the twelve boundary-law transfers or general selected-to-installable availability is claimed for this journal.

The preceding compiler is [total materialization](2026-11-14-centered-head-total-materialization.md). All additions use the `GeneralNominalCenteredHeadMatStep` prefix. Existing definitions, including refresh and descriptor caching, are unchanged.

## Source authority and consumer inventory

The source obligations remain those in spec/06-roles.md. In §6.3, “同じ role の需要が二つあり、すべての名前なしの引数が同じものを指す … とき、二つの関連型の出力を等しいとし、需要を一つにまとめる” requires shared inputs and the whole class's output equations. In §6.5, “中心は `lower ≤ 中心 ≤ upper` を満たす未知の型の名前で、具体的な型を選ぶものではない” fixes what centers mean. “実装が共有の情報を失ったことを理由に需要を保留にする規則は足さない” rules out a provenance-loss deferral.

The §6.3 rule “片付いていない impl の出力を根拠にした展開は保留する” also matters during this migration. Source/head readback alone does not replace the existing provisional value-subterm dependency guard.

| Consumer | This turn | Remaining connection |
| --- | --- | --- |
| Full packet equations | `Packets.Holds`, exactly equivalent to `HeadMatPlans.Models` | Connect to final install guard |
| Input/output support split | `Packets.Inputs` / `Outputs`; cached context omitted from the input support slice | Provisional dependency ledger and finite support alternatives |
| Current journal models | `Journal.Models` reads the new packet and class-effect equations | Operational Step and model-extension producer |
| Installed raw sites | `installCore` appends `plan.emitted.map Site.observed` | Include this update in the final Step |
| Class effects/defaults | New compiled `ClassEffects`, snapshot and live ledgers | Common successor model for every selected frame |
| Settled support/readback | `Support.Trusted`, `Readback`, `ClassReadback` use corrected equations | Promotion availability and value-subterm support |
| K2 observation graph | No migrated graph is exported | Total-expression constructor edges, defaults, and journal-aware inspection checks |
| Refresh/caching | Literal update and existing certificate remain unchanged | `RefreshExactTransport` for corrected reachable journals |

`GeneralNominalCenteredSteps.State` is retained as a data container. Its legacy `Models`, packet interpretation, and fact interpretation are not conjoined with the corrected `Journal.Models`. Retaining both meanings would be wrong for the preceding turn's union example: the old capture-based schema forces distinct payload variables equal, while the total expression denotes their union.

## Packet and journal results

`GeneralNominalCenteredHeadMatStepPackets.models_iff` proves exact equivalence with the preceding total-plan model. `private_models`, `head_equations`, `emitted_holds`, `output_equation`, and `shared_center` expose its consumers.

`GeneralNominalCenteredHeadMatStepJournal.install_models` states, with `effect.snapshot = state.core`,

```lean
Models (install state effect) model ↔ InstallationModels state effect model
```

Here `InstallationModels` explicitly contains the old corrected journal, new packet, snapshot effects, new live effects, and all earlier effects' enlarged live obligations. It does not derive a common model. `installed_inhabited` requires that common model. `merge_models` similarly exposes added output atoms and all enlarged live obligations; merging is not asserted to preserve inhabitation automatically. `installed_child` proves edge recording for the update.

`GeneralNominalCenteredHeadMatStepPreservation.install_restrict`, `merge_restrict`, `merged_output_effect`, `merge_retains_effect`, and `install_retains_effect` prove backward model restriction and retention of the stored equations. These are ingredients for `stepModels`, not a proof of that boundary field without its Step.

The concrete old multi-tag row fixture now satisfies the complete corrected packet model. `GeneralNominalCenteredHeadMatStepRows.source_packet_extension` provides a corrected initial-journal model and corrected packet model while preserving the fixture’s original model on every source identity. `installed_journal_inhabited` additionally provides an inhabited result of the concrete journal installation, including snapshot and live class effects. This is **not** an enabled Step trace: the final operational guards have not been supplied.

## RequestsDeclared and center recording

`GeneralNominalCenteredHeadMatStepRoles.origin_role` proves that a canonical invocation identity determines the role under checked declaration/clause identifiers. Aliases retain a role color. Consequently `requests_declared` covers all requests in the alias class, including requests contributed by only one occurrence.

`GeneralNominalCenteredHeadMatStepCoverage.Recorded` links every raw occurrence to a centered occurrence, every recorded packet to a plan, and every effect to a recorded plan. Initial, installation, merge, and context-update lemmas preserve this invariant.

`GeneralNominalCenteredHeadMatStepHistory.Built` is an explicit **overapproximation of journal construction**, not Step. Its installation constructor requires the stored effect's frame and matching snapshot/registry; it does not impose generated focus, novelty, K2, or support guards. Its context constructor preserves seed and interpretation without requiring an operational refresh. It has no enqueue constructor.

Over these histories, `recorded`, `snapshots_recorded`, `roles_invariant`, and `interpretation` are proved. `requests_declared` needs only `Checked registry`, a `Built` history, and a `Frame`. `ready` additionally needs `registry.roles = roles` and source interpretation `Coverage`; it includes role defaults. `emitted_complete` propagates total-schema completeness through the history. Connecting actual successor reachability to `Built` remains open, including showing that an unrecorded generated focus cannot require enqueue.

`History.class_readback_covers_requests` uses the snapshot invariant to show that the support readback covers every raw class request. It still requires `Support.ClassReadback`; the theorem does not manufacture a trusted explanation.

## Allocation and model extension

An emitted variable request can be an identity equation. Repeated targets are also possible. Requiring all targets to be distinct and disjoint from every right-hand-side source is unnecessarily strong for this representation.

`GeneralNominalCenteredHeadMatStepAllocation` therefore proves:

- `coherent_target`: repeated targets are allowed when their assigned values agree.
- `schema_extension`: simultaneous assignment satisfies every equation under `Coherent` and `StableReferences`.
- `independent_stable`: the preceding strict independence criterion implies the new criterion.
- `variable_identity`: a variable identity equation preserves the assignment.
- `common_model_extension`: lifts the construction under an explicit journal-preservation premise.

The precise remaining premises are:

```lean
Coherent resolve before equations :=
  ∀ first ∈ equations, ∀ last ∈ equations, first.target = last.target →
    value (sources resolve before) first.mode first.expression =
      value (sources resolve before) last.mode last.expression

StableReferences resolve before equations :=
  ∀ equation ∈ equations, ∀ mode name, name ∈ names equation.expression →
    ∀ assigned ∈ equations, assigned.target = resolve mode name →
      value (sources resolve before) assigned.mode assigned.expression =
        (before (resolve mode name)).1
```

These are **literal value equalities**, stronger than carrier equivalence. General checked-source allocation coherence is not proved. `common_model_extension` also requires `journal before` and:

```lean
∀ after : Assignment,
  (∀ identity, identity ∉ schema.equations.map Equation.target →
    after identity = before identity) →
  journal before → journal after
```

This premise must still be established for the complete current journal. The source-only freshness theorem from the preceding turn cannot discharge preservation of previously installed plans and live effect ledgers.

## Refresh and unfinished operational guards

The frozen `GeneralNominalCenteredSteps.Refresh.exact` quantifies over the old centered `Models`. Its refinement component still proves `Preservation.refresh_restrict` for the corrected journal. The converse requires the exact named residual:

```lean
GeneralNominalCenteredHeadMatStepPreservation.RefreshExactTransport state context :=
  ∀ model, Journal.Models state model → GeneralNominalState.Models context.state model
```

`refresh_exact_iff` characterizes this as forward corrected-journal preservation. `source_refresh_exact` discharges it at an initial state. No general reachable discharge or reachable failure is claimed. The earlier clarification about retyping this certificate remains unanswered; this turn leaves the literal certificate untouched.

Two other guard obligations prevent assembly of the operational boundary:

1. Migrate the complete provisional value-subterm support ledger, dependency alternatives, and certified observation views. The settled `Trusted` slice alone is insufficient; substituting it for the old `GeneralNominalValueSupport.PacketGuard` would change which unresolved outputs may justify expansion.
2. Generate sound K2 edges from the total expression language and role defaults, and connect corrected journal equality to every required root/inspection check. Filtering the old `Plan.tests` is insufficient: old schemas omit the very multi-tag rows/defaults now materialized. No such filtered graph is retained in these additions.

These are implementation/proof obligations, not a proposed language decision. No new reachable counterexample was established this turn. There is no claimed counterexample-based stop or owner question.

The twelve old boundary laws remain proved for their frozen boundary. For the corrected journal, no assembled-boundary transfer is claimed: progress, closure, stepModels, execution, halted, frontierLocal, localIdentity, whereAccessible, treeExecution, dictionaryRefl, initialReorders, and canonicalLocalOrder all await the successor Step/Local/executor. Generic local totality and structural equality arguments should be reusable once those definitions exist; that expectation is not counted as a transfer. General `Extension` and `GeneratedChildren` remain open.

## Verification and proof inventory

All public theorem names introduced here are listed exactly in `lean/Audit/GeneralNominalCenteredHeadMatStep.lean`; it checks each theorem's logical dependencies. No prover launch surface was available; the primary constructed these bounded derivations and a separate reviewer checked them. The reviewer distinguished the construction-history invariant and model witnesses from operational reachability.

Intermediate module builds caught elaboration errors; those errors were fixed before the final checks. The final commands below all exited **0**. The audit covers **66 public theorems** and reports only `propext`, `Classical.choice`, and `Quot.sound`. The append-only check confirms that the only modified pre-existing files are `lean/Yulang.lean` and `notes/design/INDEX.md`, each with its original contents preserved as a prefix. No git references were changed.


```sh
# Working directory: lean; exit 0
lake build --wfail Yulang.GeneralNominalCenteredHeadMatStepAllocation Yulang.GeneralNominalCenteredHeadMatStepCoverage Yulang.GeneralNominalCenteredHeadMatStepHistory Yulang.GeneralNominalCenteredHeadMatStepJournal Yulang.GeneralNominalCenteredHeadMatStepPackets Yulang.GeneralNominalCenteredHeadMatStepPreservation Yulang.GeneralNominalCenteredHeadMatStepRoles Yulang.GeneralNominalCenteredHeadMatStepRows Yulang.GeneralNominalCenteredHeadMatStepSupport

# Working directory: lean; exit 0
lake build --wfail Yulang

# Working directory: lean; exit 0
lake env lean Audit/GeneralNominalCenteredHeadMatStep.lean > /tmp/centered21-audit.log 2>&1

# Working directory: repository root; exit 0
git diff --check
```
