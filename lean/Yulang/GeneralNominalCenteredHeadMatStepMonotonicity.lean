import Yulang.GeneralNominalCenteredHeadMatStepTrace

namespace Yulang.GeneralNominalCenteredHeadMatStepMonotonicity
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralNominalCenteredHeadMatStepKernel
variable {roles : Roles.RoleDecls} {before after : State roles}

def installed_refines (enabled : Installable registry before effect) :
    GeneralNominalRefinements.Refines before.core.erased.current.context.state
      (install before effect).core.erased.current.context.state := by
  have refinement := GeneralNominalRefinements.installed effect.plan.packet.registry effect.plan.packet.context
    effect.plan.packet.site.occurrence effect.plan.packet.declaration effect.plan.packet.bounds
  have same := effect.frame.context_eq.trans
    (congrArg (fun state => state.erased.current.context) enabled.snapshot_eq)
  conv at refinement => lhs; rw [same]
  exact refinement

theorem raw_models (action : At registry before focus after)
    (valid : GeneralNominalState.Models after.core.erased.current.context.state model) :
    GeneralNominalState.Models before.core.erased.current.context.state model := by
  cases action with
  | administrative action =>
    cases action with
    | enqueue => exact valid
    | refresh context certificate source member unknown known =>
      exact GeneralNominalRefinements.models certificate.refines model valid
    | equate => exact (GeneralNominalState.extend_models ..).mp valid |>.1
    | reobserve revision certificate improved => exact certificate.raw model valid
  | refresh focus context certificate source member unknown known =>
    exact GeneralNominalRefinements.models certificate.refines model valid
  | install effect enabled novel => exact GeneralNominalRefinements.models (installed_refines enabled) model valid
  | merge => exact (GeneralNominalState.extend_models ..).mp valid |>.1

theorem known (action : At registry before focus after) (identity : Nat)
    (prior : GeneralNominalState.Known before.core.erased.current.context.state identity) :
    GeneralNominalState.Known after.core.erased.current.context.state identity := by
  cases action with
  | administrative action =>
    cases action with
    | enqueue | equate => exact prior
    | refresh context certificate source member unknown known => exact certificate.refines.known identity prior
    | reobserve revision certificate improved => exact (GeneralNominalReobservationSteps.revision_known revision identity).mpr prior
  | refresh focus context certificate source member unknown known => exact certificate.refines.known identity prior
  | install effect enabled novel => exact (installed_refines enabled).known identity prior
  | merge => exact prior

theorem point (action : At registry before focus after)
    (prior : GeneralNominalReobservationOrder.Point before.core.erased.current identity) :
    GeneralNominalReobservationOrder.Point after.core.erased.current identity := by
  cases action with
  | administrative action =>
    cases action with
    | enqueue | equate => exact prior
    | refresh context certificate source member unknown known => exact GeneralNominalReobservationOrder.point_refines certificate.refines prior
    | reobserve revision certificate improved =>
      obtain ⟨slot,same,point⟩ := prior
      exact ⟨slot,same,improved.1 slot point⟩
  | refresh focus context certificate source member unknown known => exact GeneralNominalReobservationOrder.point_refines certificate.refines prior
  | install effect enabled novel => exact GeneralNominalReobservationOrder.point_refines (installed_refines enabled) prior
  | merge => exact prior

theorem edges (action : At registry before focus after) :
    before.core.erased.current.edges ⊆ after.core.erased.current.edges := by
  cases action with
  | administrative action => cases action <;> exact fun _ member => member
  | refresh | merge => exact fun _ member => member
  | install => exact fun _ member => List.mem_append_left _ member

theorem committed (step : Step registry root before after) (prior : Committed before plan) : Committed after plan :=
  ⟨fun model valid => prior.1 model (stepModels step valid),
    fun child member => edges step.choose_spec.2 (prior.2 child member)⟩

end Yulang.GeneralNominalCenteredHeadMatStepMonotonicity
