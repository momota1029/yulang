# Centered head-only installation and class effects

Status: Draft — successor relation and local/model/progress laws proved;
source-complete resolution and V6 composition remain open.
Date: 2026-11-14.
Baseline: `5d03ce5bd`, `astra2/centered`.
Scope: centered-16; additive modules prefixed `GeneralNominalCenteredHeadStep`.

## Contract and operational change

This implements the owner clarification recorded in the
[V6 head/output note](2026-11-14-centered-head-output-v6.md): unnamed arguments
are inputs, named arguments are outputs, all class requests are retained, and
outputs cannot filter candidates or resolve ambiguity. A unique implementation's
inconsistent associated equations are a post-choice type error. The relevant
[§6.3](../../spec/06-roles.md) says 「すべての名前なしの引数が同じものを指す」
for merging and 「それまでに積まれた制約と合わなければ、その時点で型エラーになる」
for an associated equation added after choice.

The new [state and effects](../../lean/Yulang/GeneralNominalCenteredHeadStepEffects.lean)
wrap the existing centered state in `State.core` and add a list of `Effect`
records. An effect stores the registry, pre-installation core snapshot, actual
plan, head-only Frame/Unique certificates, and explicit-schema coverage. Its
`Holds` predicate contains the captured head equations and **all** class output
equations at that snapshot. Its `Live` predicate interprets the same chosen
plan against the output requests of its **current** alias class. Thus a later
merge need not replay an already committed raw packet just to retain requests.

The new [kernel](../../lean/Yulang/GeneralNominalCenteredHeadStepKernel.lean)
uses the same raw packet and child emitter. The installation guard contains:

- the new head-only Frame and Unique, and V6's existing safe-known observations;
- explicit output coverage and the existing emission schema's completeness flag;
- the existing recorded-choice compatibility, value-support and actual-position
  safety conditions; alternatives use head-only preparation;
- one common model satisfying the current extended journal, the concrete plan,
  all chosen class output equations, and the live ledger after child emission.

Neither the old output-filtered `Prepared`, old Local selection nor `Joint`
appears in this guard. `plan.Holds` remains the concrete packet/center equation
semantics checked **after** head uniqueness. Materialization and model checks
cannot remove a head from the candidate set or select between two heads.
Raw semantic commitment still prevents repeated installation.

An enabled install adds the same raw packet, raw children and centered sites
as before, and records the class effect. It cannot install a prospective V6
output conflict. No error packet or new pending case is added.

Administrative, refresh and merge constructors have exactly their old core
premises and core results. In particular both the direct centered refresh
certificate and administrative refresh certificate are unchanged. The direct
certificate still quantifies over `CenteredSteps.Models state.core`, not the
stronger new Models. Descriptor caching and interpretation are untouched.
The effect ledger is preserved by these constructors; its live interpretation
changes when the underlying alias class grows.

## Model laws and merging

The extended model predicate is:

```text
Models state m =
  CenteredSteps.Models state.core m ∧
  ∀ effect ∈ state.effects, effect.Holds m ∧ effect.Live state.core m
```

`Kernel.install_models` proves an iff with `InstallationModels`: old extended
Models, the concrete plan's Holds, the captured class output equations, the new
effect's live output equations after emission, and all prior effects' live
equations after emission. These last clauses account for any enlarged live
class; they are not silently inferred from a per-occurrence packet.
`Kernel.installed_inhabited` derives a successor model from the guard's common
witness. This does not assert that every reachable state is inhabited.

`Kernel.refresh_models` proves exact preservation of extended Models using the
unchanged core certificate. Alias equivalence is transported explicitly because
it is indexed by the whole raw state even when the alias list is unchanged.
`Kernel.stepModels` and `steps_models` prove model restriction for every actual
successor step/trace, with no checkedness or reachability premise.

`Coverage.merge_models` proves exactly:

```text
Models (merge state first last support) m ↔
  Models state m ∧ old outputAtoms first last hold in m ∧
  every recorded effect's Live equations hold for the enlarged class in m
```

The operational merge guard is unchanged. The last conjunct is the additional
semantic content of the new class ledger, not a model-preservation claim for
merging. The request-union monotonicity proof handles registered occurrences
and alias growth; it does not intersect named-request lists. It also gives
`merged_one_sided_request` when one merged occurrence has no output request.

Two coverage statements are deliberately distinguished:

1. `Coverage.OutputEffectCoverage registry before after root key` quantifies
   over **extended** Models of `after` and concludes the previous turn's
   `HeadOutputs.ChosenClassEffects registry before.core root key`. This is the
   natural lifted statement because the successor's state/model types changed.
   `installed_coverage`, `coverage_steps`, and `coverage_merge` prove it at
   installation and preserve it for the fixed historical snapshot.
2. `installed_live_after_steps` proves that the actual recorded plan's
   `OutputEquations after.core` holds for the enlarged current class after any
   further successor trace. `live_merged_class` specializes the live equations
   to merges; `live_merged_equal_outputs` gives equality of all same-name targets.
   `effects_step`/`effects_steps` prove actual ledger persistence.

These are universal model implications. A merge can make extended Models
empty, so none of the merge laws asserts a compatible successor model.

## V6 boundary and local agreement

[HeadStepBoundary.boundary](../../lean/Yulang/GeneralNominalCenteredHeadStepBoundary.lean)
instantiates the unchanged V6 target with the successor Step and extended
Models. Initial states are the same checked ground-point source states lifted
with an empty effect ledger. Pending, head survivors, K2 and administrative
readiness retain the preceding head boundary's core observations.
OutputConflict uses the **extended** model predicate, with the same feasible
chosen-head baseline and absence of a common model of chosen effects.

`installable_selected` proves the operational-to-local direction for the actual
key and emitted children. `ambiguous_no_install` and `conflict_no_install`
exclude installation respectively for distinct head survivors and a prospective
output conflict. `output_conflict_rejected` gives the genuine V6 rejected
classification when its higher-priority safe-known conditions hold.
`local_total` and `local_functional` continue to hold.

The reverse availability claim is **not** proved: Local selection alone does
not construct Frame/schema/value-support/compatible-emission witnesses. This
is separate from uniqueness and from the successful-installation model law.

## Progress and requested bridge results

The generic finite missing-fact engine is reused directly. There is no
simulation premise to the old Step and no restriction to compatible steps.

1. `HeadStepProduction.plan_matching` and `production` restate the existing
   center-readback producer with head-only preparation and explicit emission
   completeness. They use the actual successful plan's equations, without
   `Joint` or an old installation judgment.
2. `HeadStepAncestry.sites_bounded` restricts a retrospective extended model
   backwards through the new Step and proves
   `depth + mass(site labels) ≤ mass(root labels)`. The chosen center readbacks
   supply finite labels and checked normalized Paterson descent bounds children.
   A prospective installation's common model supplies the witness used by
   `installed_depth_bound`; no global state-inhabitation premise is needed.
3. `HeadStepEnumeration` reuses the finite invocation, allocation, occurrence
   and report bases. Refresh support and differing-site merges retain the same
   finite raw source bound. Raw signatures suffice because every installation
   still requires raw packet novelty, while other constructors gain an existing
   known/equality/point/alias fact.
4. `HeadStepAccessibility.finiteCover` constructs every field of the new finite
   cover; `ground_cover` discharges the intermediate `GroundCover` hypothesis.
   `ground_point_root_accessible` and `progress` therefore cover the unrestricted
   successor Step from the stated ground-point Initial states.

The exact requested results are:

| Result | Theorem and premises |
| --- | --- |
| stepModels | `GeneralNominalCenteredHeadStepKernel.stepModels`: an actual Step and a successor model. Boundary-shaped version: `HeadStepBoundary.boundary_stepModels`. |
| closure | `GeneralNominalCenteredHeadStepKernel.closure`: halted implies stability of root and every generated demand. Boundary-shaped version: `HeadStepBoundary.boundary_closure`. |
| progress | `GeneralNominalCenteredHeadStepAccessibility.progress`: Checked and actual reachable-from-ground-point-Initial, with no remaining cover/production hypothesis. |
| actual terminal execution | `GeneralNominalCenteredHeadStepAccessibility.terminal`: same scope; finite trace, halt, stable closure and model restriction. |
| class effects at installation | `GeneralNominalCenteredHeadStepCoverage.installed_coverage`: the successful install guard. |
| preservation and enlarged classes | `coverage_steps`, `coverage_merge`, `installed_live_after_steps`, `live_merged_class`. |
| whereAccessible | `GeneralNominalCenteredHeadStepWhere.whereAccessible`: all registries, successor states and roots, with no reachability premise. |

The local child proof uses registered parent identities and the unchanged
allocation's strictly larger child identities. It does not assume operational
progress or that selected children have already been emitted.

## Remaining obligations and limits

- **Schema coverage.** This turn inherits the explicit associated-equation
  interface from centered-15. An installation's `EffectsReady` covers its
  snapshot; later merged requests can introduce defaults or unsupported
  translations. The named `HeadStepEffects.LiveEffectsReady state` obligation
  requires coverage for every live class, and is not proved for all reachable
  states. `OutputEquations` alone must not be described as complete interpretation
  of those uncovered source forms. No pending or candidate-filtering rule is
  introduced for this implementation gap.
- **Feedback from the new ledger.** Frozen core equality, support, same-input,
  refresh and K2 consumers do not read ledger-only equations. A future fact
  producer/consumption bridge is needed to make those equations available to
  ordinary propagation and settled output readback. The pending owner question
  about unsettled-output refresh is not answered by changing a certificate here.
- **Merge-created inconsistency.** Newly activated live equations can empty
  extended Models even when the core still has models. The prospective conflict
  predicate requires an inhabited pre-state and does not diagnose that already
  inconsistent snapshot. Complete error reporting for such merges remains open;
  coverage laws are not a substitute for this diagnostic obligation.
- **Availability and composition.** Unconditional selected-to-installable,
  source-complete effects/default evaluation, canonicalLocalOrder and
  GeneratedChildren are not proved. EvidenceNode remains outside this worker's
  scope. No V5/V6 target, old Step, or previous-cycle source is modified.

None of these remaining semantic/production obligations is an extra hypothesis
of the exported progress, closure, model-restriction or local-accessibility
theorems. The intermediate conditional theorem in `HeadStepProgress.progress`
is instantiated by `HeadStepAccessibility.ground_cover` in the final export.

The configured prover role is unavailable; the primary constructed the bounded
derivations. Independent review checked the guards, model laws, the full new-Step
ancestry/cover chain and quantifiers. It found no logical gap in the stated
theorems and identified the schema, feedback and merge-error limits above.

## Validation

All final commands below ran from the repository root and exited **0**:

```text
cd lean && lake build --wfail Yulang.GeneralNominalCenteredHeadStepAccessibility Yulang.GeneralNominalCenteredHeadStepCoverage Yulang.GeneralNominalCenteredHeadStepWhere
cd lean && lake build --wfail
cd lean && lake build Yulang
cd lean && lake env lean Audit/GeneralNominalCenteredHeadStep.lean
git diff --check
```

The [dedicated audit](../../lean/Audit/GeneralNominalCenteredHeadStep.lean)
lists all 72 public theorem checks, with dependencies confined to `propext`,
`Classical.choice`, and `Quot.sound`. Earlier intermediate builds exited 1 for
local elaboration issues (list append/flatten reduction, indexed Alias
induction, implicit state parameters and one missing import); the final checks
above supersede them. No proof escape remains in the new modules.

The scope check passed: all eleven new modules are imported, old-file changes
are only appended imports and the design-index entry, the branch remains
`astra2/centered`, and HEAD remains `5d03ce5bd`. No commit, push or ref mutation
was performed.
