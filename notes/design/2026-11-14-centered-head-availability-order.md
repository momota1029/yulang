# Centered V6 availability and canonical execution

Status: canonical execution and local order proved; general selected availability,
default integration, and retrospective merge-error reporting remain open.
Date: 2026-11-14. Scope: centered-17, baseline `08552eef0`, `astra2/centered`.
All additions are separate modules. No existing transition, target, refresh,
descriptor cache, or classifier definition is changed.

## Source contract

[§6.1](../../spec/06-roles.md) explicitly permits omitting an associated equation
when the role supplies a default: 「default があれば省略できる」.
[§6.3](../../spec/06-roles.md) separates unnamed inputs from named outputs,
retains all requests when merging, and specifies a type error when the chosen
associated equation conflicts: 「それまでに積まれた制約と合わなければ、その時点で型エラーになる」.
Candidate ambiguity still depends on heads, not those output requests.
[§6.5](../../spec/06-roles.md) gives actual arguments explicit center identities:
「実際の引数の名前（中心）は明示して持つ」. None of the new modules adds a
pending case, filters a head using outputs, or changes refresh.

## Availability: proved reduction and exact remaining work

In `GeneralNominalCenteredHeadStepAvailability`:

- `selected_guards`, `selected_safe`, and `selected_alternatives` derive settled
  decision availability and the actual-position inspection guards from V6 Local.
- `frame_value_iff` identifies raw packet value support with the raw decision
  certificate at the same Frame. `selected_initial_value` supplies empty raw
  support at an initial selection; this is not a general reachable-state theorem.
- `selected_has_effects` and `selected_frame` use the **positive chosen-head
  baseline** and selection's absence of conflict to obtain a current journal
  model satisfying all chosen class effects. No extra consistency assumption is
  added to this extraction.
- `selected_installable_iff` removes uniqueness, inspection safety, alternative
  safety and administrative closure from the remaining proof obligations.
  It assumes the specific current Frame and its existing `EffectsReady`.
- `enabled_or_committed` produces an actual successor Step when the packet is
  novel, and otherwise reports its semantic commitment. A completed selected
  node does not promise another enabled Step.

The exact residual `Extension registry state plan` is the conjunction of:

1. The full emitted schema's `unknown = false`.
2. `ChoiceCompatible state.core.erased.current plan.packet`.
3. A support list satisfying the **raw** value-support decision guard.
4. One assignment satisfying `InstallationModels state plan support`: current
   extended Models, the whole `plan.Holds`, current chosen output equations,
   successor chosen output equations, and every previous effect's successor
   live equations.

These are genuine remaining obligations. The current class-effect witness in
`selected_frame` does not already establish the emitted child equations or the
successor live ledger. Neither reachability nor stable-candidate closure is
proved to discharge this `Extension`. In particular the current centered
trusted ledger cannot automatically replace the raw value-support certificate.

## Defaults: certified gap and scope-correct schema interface

The frozen `HeadOutputs.EffectsReady` demands an **explicit** equation for every
retained request. `DeclarationChecked.signature` permits a role default instead.
This cannot be repaired by a theorem saying that default lookup supplies an
explicit list member.

`GeneralNominalCenteredHeadStepDefaults` constructs a checked singleton registry
and an inhabited ground-point InitialSource representing a unary role `R` whose
`out` defaults to positional argument 0, the leaf implementation `R int` with no
explicit associated equations, and the request `R(int, out = int)`.
The concrete results are `checked`, `source`, `inhabited`, `ground`,
`initial_source`, `reachable`, `fallback`, `no_ready`, `no_chosen_head`,
`no_positive_baseline`, `no_output_conflict`, and `no_install`.

The example establishes an actual source-formed defaults gap. It does **not**
prove its Local is selected or its state stable, and it does **not** refute an
availability implication that assumes the frozen positive baseline: that
baseline is itself absent. `recorded_default_blocks_live_ready` separately proves
that any recorded effect exposed to a request without an explicit equation
cannot satisfy the frozen live-readiness predicate. No reachable delayed-merge
witness for this latter implication is claimed.

`GeneralNominalCenteredHeadDefaultSchemas` supplies an additive interpretation
interface. Explicit equations retain declaration binders. A default term uses
the positional **whole input center**, as proved by `positional_parameter` and
`positional_default`; it never treats role parameter 0 as impl binder 0.
`ready_of_coverage` handles default lookup using checked signature coverage,
requiring `RequestsDeclared` for the merged class and materialization coverage
for its explicit bodies. `default_scoped` retains the role's scope certificate.
`equations_default`, `restrict`, and `ready_restrict` give the corresponding
equation and request-retention laws. `Example.ready`, `Example.equations`, and
`Example.inhabited_effects` interpret the concrete positional-default example
successfully while `Example.old_ready_fails` certifies the old guard's failure.

The general `ConstructorMeaning` parameter is an **unimplemented source bridge**,
not an assumption of the canonical theorem. `Roles.Term` defaults have no
general-carrier constructor-resolution contract. `Pattern.encode` uses tagged
constructor numbers for counting and is not an authorized default decoder.
The existing Metadata contract checks only present primitive entries; it does
not guarantee coverage of every constructor in an emitted schema or default.
Source elaboration must supply the correct constructor meaning, its semantic
compatibility, and the required coverage. The positional example is independent
of that parameter because its body contains no constructor application.

This schema API is not wired into the frozen Effect, Models, OutputConflict or
Installable. Completing defaults requires additive successors of those consumers
and their producer proofs. In particular this turn does not discharge existing
`LiveEffectsReady` universally. No language decision or new deferral is proposed.

## Canonical route: no residual simulation premise

The route consists of these modules and principal theorems:

| Module suffix after `GeneralNominalCenteredHeadStep` | Proved connection |
| --- | --- |
| `Order` | `prepared`, `survivor`, `unique`, `chosen_head`, `chosen_effects`, `conflict`, `local_iff`: fixed-state registry invariance |
| `EffectPermutation` | `plan_pair`, `EffectPair.holds/live/ready`, `Related.models/live_ready`: complete historical/live ledger transport |
| `ObservationPermutation` | `frame_counterpart`, `chosen_head`, `chosen_effects`, `conflict`, `local_iff`: fixed-registry observations across paired snapshots |
| `TableExtension` | `installed_related`, `installed_corresponds`: coherent packet-table extension using only head Frames |
| `InstallationPermutation` | `counterpart_enabled`: new Installable, novelty, and installed correspondence, including successor live equations |
| `Simulation` | `at_forward`, `step_forward`, `step_backward`, `observations`, `steps_backward`, `halt_reflects` |
| `Registry` | `distinct_shared_packet_free`, `packet_free_steps`, `packet_free_reachable`, `packet_free_self` |
| `CanonicalExecutor` | `canonical_exit_lifting`, `execution`, `halted`, `treeExecution`, `canonicalLocalOrder`, `exact`, `saturationTotal`, `orderIndependent` |

The installation proof preserves the same common assignment through packet
rebasing, current and successor class requests, and every historical live effect.
It never manufactures old output-filtered applicability or Joint. Raw support
alternatives use their existing permutation theorem. Recorded commitment and
novelty exclude collisions when the finite packet pairing table grows.
Administrative, refresh and merge steps retain the same effect records and
reuse their original core certificates. No stronger refresh premise is added.

For a shared reachable input, distinct registry tags imply the packet list is
empty. The trace then contains no installations, its effect ledger is empty,
and its passive prefix transports literally. The canonical execution is lifted
back to an actual execution under the original registry. The executor's returned
states may differ, but their V6 Local observations agree literally.

`CanonicalExecutor.CanonicalLocalOrder roles` retains the complete field shape:

```text
∀ r r', Checked r → Checked r' → Reorders r r' →
∀ s root, Reachable r root s → Reachable r' root s →
∀ d f, Local r (executor.run r s root).1 d f ↔
       Local r' (executor.run r' s root).1 d f
```

`canonicalLocalOrder` has no additional hypothesis. Likewise `exact`,
`saturationTotal`, and `orderIndependent` prove the actual V6 target properties
for this executor and the existing declared ground-point boundary. The
executor-dependent execution, halting, tree execution, and frontier laws are
re-proved; the existing progress, closure, stepModels, whereAccessible,
dictionary reflexivity and initial reordering laws remain applicable. This is
not a proof of the complete V6 Statement, dictionary evidence, or child production.

## Merge-created inconsistency

`GeneralNominalCenteredHeadStepEmptyModels.empty_no_conflict` certifies that
prospective OutputConflict is false when the current extended Models are empty.
`empty_no_install` then excludes every installation.
`empty_safe_unique_selected` proves the conditional diagnostic mismatch if
safe-known head uniqueness remains true. `merge_empty_iff` gives the exact
unsatisfiable conjunction: old extended Models, raw equal-output atoms, and the
complete successor live ledger.

No reachable merge creating this situation is constructed here, and no new
error rule is installed. Reporting that error requires retaining an inhabited
pre-merge witness or an explicit conflict event; the current prospective predicate
cannot recover it from an already empty model set.

## Validation and review

All public theorem names are listed explicitly in
[the new audit](../../lean/Audit/GeneralNominalCenteredHeadAvailabilityOrder.lean).
The work uses the `yulang-proofs` skill. The configured prover role is unavailable;
the primary constructed the proofs and a separate reviewer checked their exact
statements and dependencies. No prover agent ran. Independent isolated source
compilation and exported-statement checks passed; the review confirmed the full
canonical quantifiers and the explicit defaults/availability limitations.

Final checks, with working directory `lean/`:

```text
lake build --wfail Yulang.GeneralNominalCenteredHeadStepAvailability Yulang.GeneralNominalCenteredHeadStepDefaults Yulang.GeneralNominalCenteredHeadDefaultSchemas Yulang.GeneralNominalCenteredHeadStepCanonicalExecutor Yulang.GeneralNominalCenteredHeadStepEmptyModels
exit 0
lake build --wfail
exit 0
lake build Yulang
exit 0
lake env lean Audit/GeneralNominalCenteredHeadAvailabilityOrder.lean
exit 0
```

The new audit checks 149 public theorems; its only logical dependencies are
`propext`, `Classical.choice`, and `Quot.sound`. `git diff --check` and the
baseline-prefix/import/prohibited-term check exit 0. Existing tracked changes
are exactly appended imports in `lean/Yulang.lean` and an appended INDEX entry;
HEAD remains `08552eef0` on `astra2/centered`. No refs were changed.

During construction, intermediate single-file checks returned exit 1 for proof
elaboration/name errors, subsequently corrected. One build invocation from the
repository root returned exit 1 because that directory has no Lake configuration;
the reported final build commands use `lean/`. An intermediate edit helper also
returned a missing-path error before the corrected path was used. These are not
unresolved validation failures. No general selected-to-installable theorem,
default-aware operational successor, reachable merge-error trace, or complete
V6 Statement is certified by the successful checks above.
