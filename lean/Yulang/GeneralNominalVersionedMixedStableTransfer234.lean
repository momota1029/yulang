import Yulang.GeneralNominalVersionedMixedTerminalStable234
set_option backward.isDefEq.respectTransparency false
/-! Conditional stability transfer retaining the actual current legacy cache.
It does not assert unconditional preservation of old Stable. -/
namespace Yulang.GeneralNominalVersionedMixedStableTransfer234
open GeneralNominalVersionedJournal232
variable {roles : Roles.RoleDecls} {state : State roles}

theorem installable
    (cache : GeneralNominalCenteredHeadMatStepObservations.CacheSound state.legacy state.core.erased.current.context.state)
    (given : GeneralNominalVersionedMixedKernel234.Installable registry state effect) :
    GeneralNominalVersionedKernel232.Installable registry state effect :=
  ⟨given.registry_eq,given.snapshot_eq,given.safe,cache,given.materialized,given.choice,
    given.positions,given.alternatives,given.common⟩

theorem stable
    (old : GeneralNominalVersionedKernel232.Stable registry state root)
    (cache : GeneralNominalCenteredHeadMatStepObservations.CacheSound state.legacy state.core.erased.current.context.state)
    (point : GeneralNominalReobservationSteps.PointClosed state.core.erased.current.context.state)
    (headless : GeneralNominalVersionedMixedTerminalStable234.HeadlessUnknown state) :
    GeneralNominalVersionedMixedKernel234.Stable registry state root := by
  intro focus generated after action
  cases action with
  | administrative action =>
    cases action with
    | enqueue linked absent => exact old _ generated _ (.administrative (.enqueue focus linked absent))
    | equate first last one two equal novel => exact old _ generated _ (.administrative (.equate focus first last one two equal novel))
    | refresh context certificate identity member unknown known =>
      exact GeneralNominalVersionedMixedTerminalStable234.no_refresh headless certificate member unknown known
    | reobserve revision certificate improved =>
      exact GeneralNominalReobservationSteps.pointClosed_no_revision point revision improved
  | refresh focus context certificate identity member unknown known =>
    exact GeneralNominalVersionedMixedTerminalStable234.no_refresh headless certificate member unknown known
  | install effect enabled novel => exact old _ generated _ (.install effect (installable cache enabled) novel)
  | merge first last one two inputs novel => exact old _ generated _ (.merge first last one two inputs novel)

theorem headless_of_known (valid : Models state model)
    (known : ∀ identity ∈ GeneralNominalState.sources state.core.erased.current.context.state,
      GeneralNominalState.Known state.core.erased.current.context.state identity) :
    GeneralNominalVersionedMixedTerminalStable234.HeadlessUnknown state :=
  ⟨model,valid,fun identity member unknown => False.elim (unknown (known identity member))⟩

end Yulang.GeneralNominalVersionedMixedStableTransfer234
