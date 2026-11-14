# Successor finite cover from bounded installation ancestry

Status: checked conditional theorem, astra2-centered-24, 2026-11-15.
`GroundCover` and `Progress` are **not unconditional**. No Step, boundary,
Initial predicate, source contract, refresh certificate, or earlier module is
changed in this turn. There is no certified reachable counterexample and no
new owner question.

## Result and exact residual

The new namespace `GeneralNominalCenteredHeadMatGroundCover` provides:

```lean
cover
  (checked : Checked registry)
  (source : InitialSource registry context root)
  (bound : InstalledDepthBound registry context root limit) :
  FiniteCover registry root (initial context root)

accessible_of_depth_bound checked source bound :
  Acc (fun next current => Step registry root current next)
    (initial context root)

ground_cover (depth : GroundDepthBound roles) : GroundCover roles
progress (depth : GroundDepthBound roles) :
  GeneralNominalCenteredHeadMatStepExecutor.Progress roles
```

All the operational names in these statements denote the total-materialization,
trusted-cache successor. The exact remaining assumption is:

```lean
GroundDepthBound roles :=
  ∀ registry, Checked registry → ∀ context (root : Occurrence roles) labels,
    InitialSource registry context root →
    (∀ index, (root.demand.arguments index).1 =
      (root.demand.arguments index).2) →
    GroundRoots context root labels →
    Coverage registry context.interpretation →
    ∃ limit, InstalledDepthBound registry context root limit
```

`InstalledDepthBound` is defined in the new
`GeneralNominalCenteredHeadMatStepDepthSupport` namespace. It quantifies over
every actual successor trace from `initial context root`, every effect whose
focus is generated from the root, and every enabled, uncommitted installation.
It requires a depth at most `limit` and the existing `AtDepth registry seed
root.identity depth effect.plan.packet.site.occurrence.identity` ancestry.
It does not bound the executor alone or a restricted Step. No proof of this
remaining assumption is supplied.

The previous finite-cover assumption included three finite inventories and
semantic representation of every future installation. Those inventories and
the representation are now constructed from this one depth premise. The
construction does not assume a finite family of cached descriptors or histories.

## Construction

`GeneralNominalCenteredHeadMatPlanData.Same` records equal registry, declaration,
input centered site, seed, constructor catalogue, interpretation, and erased
inspection report. From these data, `delta` proves equivalence of the corrected
`Inputs ∧ Outputs`, and `children` proves equality of literal child lists.
`emitted_mem` preserves every emitted centered site. This deliberately does
not equate full packet `Holds`: the current raw context is not part of the code.
The existing finite-progress proof obtains that context separately from the
installation frame and the current state's Models.

`GeneralNominalCenteredHeadMatSemanticCodes` enumerates declaration/report/site
codes. `signature` chooses a realizing plan only to give the code a semantic
delta. `encode_represents` proves that any realizing plan gives the same delta
and children. `Config` supplies the seed, catalogue and interpretation omitted
from the code; `encode_mem` supplies the finite report-enumeration proof from
located arguments and bounded raw slot IDs. These results cover the corrected
total schemas, including actual child equations and non-actual endpoint equations.

`GeneralNominalCenteredHeadMatStepDepthSupport` proves configuration preservation
through every successor constructor, converts Installable into its current
head frame, and bounds parent invocations and reserved raw sources from the
depth premise. `GeneralNominalCenteredHeadMatStepEnumeration` then proves
`source_pool`, `slot_pool`, and `sites_enumerated` on actual traces. Both refresh
constructors use their support certificates. Reobservation preserves the raw
source pool. Equating sources uses only membership of its two IDs, so it does
not need the obsolete raw-model equality guard. Merging retains the support
of all named output targets. Enqueue is impossible on these traces because
generated demands are already registered.

Center names require a separate enumeration: they need not be raw source IDs.
`GeneralNominalCenteredHeadMatEmissionCodes.canonicalInput` replaces a plan's
input with a fixed site solely for enumeration; `canonical_emitted` is a
definitional equality. This artificial plan is not asserted to be installed,
installable, or model-valid. Emissions depend on packet data, so all child
center sites are drawn from finitely many representative emissions.
`centers_enumerated` proves that the actual centered-site journal is contained
in the initial root site plus that list. The final cover uses semantic codes
with these actual centered sites, not the artificial inputs.

Together these results discharge the cover's signature representation,
raw-source membership, raw-slot membership, and centered-occurrence membership
clauses. `accessible_of_depth_bound` then uses the previous missing-fact
accessibility theorem without changing its relation.

## Why the older child-label producer was not copied

The old `GroundAccessibility.ClosedTerm context pattern term` requires
`Inspection.translate ... (normalize pattern) = quote term`. The old record
query accepts a tail only when its translation is a record node. The total
compiler preserves arbitrary covered record tails.

`GeneralNominalCenteredHeadMatLabelDomain` checks a precise witness: the pattern
`record label (app scalarKey []) (app emptyKey [])`, when `emptyKey` is interpreted
as `exactEmpty`, passes the normalized `covered` test but has no old `ClosedTerm`
for that exact pattern. It still has a total translation under `PatternCovered`.
This is a representation statement. It does not construct a checked registry,
a reachable state, or a failing installation; it does not rule out some other
semantically equivalent label. It does not refute `GroundDepthBound`.

The old ancestry proof uses normalized substituted child patterns as its labels.
Using that producer unchanged therefore needs an additional argument that is
not present. A route to the remaining proof is a finite semantic label/readback
relation supporting total record tails, with normalization and Paterson mass
bounds, or an ancestry invariant specialized to the enabled installations.
No old-query restriction has been added to the source contract or Step.

This respects §6.3's structural-size decision and its rule that heads may be
cached only from source constraints and settled outputs. The actual successor's
refresh certificates are unchanged; no full-journal head fact is substituted
for a trusted-cache certificate.

## Other requested goals

No closure of goals 2–4 is claimed in this turn:

- `GeneralNominalCenteredHeadMatStepExecutor.CanonicalExitLifting roles` remains
  open. The new code equality is not a journal/trusted-ledger permutation
  simulation. Existing fixed-context packet rebasing remains insufficient for
  terminal lifting.
- `GeneralNominalCenteredHeadMatStepAvailability.Extension state effect`
  remains the conjunction of `ChoiceCompatible` and an inhabited
  `InstallationModels state effect`. Neither general choice compatibility nor
  common successor-model construction is discharged here.
- `GeneralNominalCenteredHeadMatStepCompletion.SelectedCompletion roles`
  remains open: each reachable selected local result must have a matching
  effect with registry, snapshot, focus, key and children equal and satisfying
  `Extension`. Consequently general `GeneratedSelectedChildren` remains
  conditional on that premise.
- Exhaustive K2 projections for multi-tag rows and open tails remain open.
  The existing pair/scalar regression and acyclicity facts are unchanged.

The new foundational comparison lemmas retain their explicit local inputs:
`Same`, or `Config` plus finite inventory membership, visibility, located
arguments and raw slot support. Their application to enabled reachable plans
is proved by the frame/configuration and enumeration lemmas. The operational
cover retains `Checked`, `InitialSource`, and `InstalledDepthBound`; its global
progress corollary retains precisely `GroundDepthBound`. The label-domain
witness separately retains its exact-empty interpretation and WF coverage
premises. There is no additional hidden producer, common-model, or scheduler
assumption in the cover.

## Review and checks

The registered `prover` role/configuration was unavailable; no prover agent
ran. The primary constructed the bounded derivations. A separate read-only
source audit and fresh independent review checked the representation issue
and all seven modules. The reviewer ran each module directly with Lean,
exit 0, and agreed that unconditional progress remains open.

Final commands, run from `lean/`:

```text
lake build --wfail Yulang.GeneralNominalCenteredHeadMatPlanData Yulang.GeneralNominalCenteredHeadMatSemanticCodes Yulang.GeneralNominalCenteredHeadMatStepDepthSupport Yulang.GeneralNominalCenteredHeadMatStepEnumeration Yulang.GeneralNominalCenteredHeadMatEmissionCodes Yulang.GeneralNominalCenteredHeadMatGroundCover Yulang.GeneralNominalCenteredHeadMatLabelDomain
lake build --wfail Yulang
lake build --wfail
lake env lean Audit/GeneralNominalCenteredHeadMatGroundCover.lean
```

All four final commands exited **0**. The full Yulang build completed 2,831 jobs;
the default build completed 2,832 jobs. `git diff --check` and the final
append-only/import/dependency scan also exited **0**. Exploratory proof builds
had exit 1 while resolving elaboration errors; an early `lake build` from the
repository root also exited 1 (wrong working directory). The final checks above
were rerun from `lean/` after those issues were fixed.

The audit lists all 43 new public theorems and the `cover` construction; every
reported dependency is in `propext`, `Classical.choice`, `Quot.sound`.

## Exact theorem names
- `Yulang.GeneralNominalCenteredHeadMatPlanData.occurrence`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.bindings`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.capture`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.binder`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.variables_eq`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.ordinary`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.projections`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.head_schema`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.schema_holds`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.needed`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.emitted_center`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.clause_child`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.child_site`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.child_requests`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.emitted_schema`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.child_schema`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.children`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.delta`
- `Yulang.GeneralNominalCenteredHeadMatPlanData.emitted_mem`
- `Yulang.GeneralNominalCenteredHeadMatSemanticCodes.same`
- `Yulang.GeneralNominalCenteredHeadMatSemanticCodes.encode_represents`
- `Yulang.GeneralNominalCenteredHeadMatSemanticCodes.encode_mem`
- `Yulang.GeneralNominalCenteredHeadMatStepDepthSupport.frame`
- `Yulang.GeneralNominalCenteredHeadMatStepDepthSupport.configuration_step`
- `Yulang.GeneralNominalCenteredHeadMatStepDepthSupport.configuration_trace`
- `Yulang.GeneralNominalCenteredHeadMatStepDepthSupport.plan_config`
- `Yulang.GeneralNominalCenteredHeadMatStepDepthSupport.installed_parents_finite`
- `Yulang.GeneralNominalCenteredHeadMatStepDepthSupport.reservations_finite`
- `Yulang.GeneralNominalCenteredHeadMatStepEnumeration.equate_sources`
- `Yulang.GeneralNominalCenteredHeadMatStepEnumeration.source_pool`
- `Yulang.GeneralNominalCenteredHeadMatStepEnumeration.slot_pool`
- `Yulang.GeneralNominalCenteredHeadMatStepEnumeration.sites_enumerated`
- `Yulang.GeneralNominalCenteredHeadMatEmissionCodes.canonical_emitted`
- `Yulang.GeneralNominalCenteredHeadMatEmissionCodes.encode_emitted`
- `Yulang.GeneralNominalCenteredHeadMatEmissionCodes.emitted_mem`
- `Yulang.GeneralNominalCenteredHeadMatGroundCover.centers_enumerated`
- `Yulang.GeneralNominalCenteredHeadMatGroundCover.accessible_of_depth_bound`
- `Yulang.GeneralNominalCenteredHeadMatGroundCover.ground_cover`
- `Yulang.GeneralNominalCenteredHeadMatGroundCover.progress`
- `Yulang.GeneralNominalCenteredHeadMatLabelDomain.covered`
- `Yulang.GeneralNominalCenteredHeadMatLabelDomain.quote_not_deferred`
- `Yulang.GeneralNominalCenteredHeadMatLabelDomain.no_old_closed_term`
- `Yulang.GeneralNominalCenteredHeadMatLabelDomain.total_of_covered`
