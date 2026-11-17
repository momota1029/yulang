import Yulang.GeneralNominalVersionedInstallStep232
import Yulang.GeneralNominalVersionedRefresh232
import Yulang.GeneralDictionaryDefaultKernel208
set_option backward.isDefEq.respectTransparency false
/-! Executable-state migration fragment: legacy execution is permitted only
before any versioned records, then explicit versioned installs and structurally
certified observations. This is NOT the full I44 successor solver; in particular
its installation relation has not yet been tied to all V8/K2 eligibility guards. -/
namespace Yulang.GeneralNominalVersionedMigration232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)

inductive Step (registry : Registry) (root : Occurrence roles) : State roles → State roles → Prop
  | legacyPrefix : GeneralDictionaryDefaultKernel208.Step registry root before after →
      Step registry root (lift before) (lift after)
  | install : GeneralNominalVersionedInstallStep232.Step registry root before after → Step registry root before after
  | refresh (focus : Occurrence roles) (context : GeneralNominalCandidates.Context) :
      Generated before.core.erased.current root focus →
      GeneralNominalCenteredHeadMatStepRefresh.Refresh before.legacy context →
      (source : Nat) → source ∈ GeneralNominalState.sources before.core.erased.current.context.state →
      ¬ GeneralNominalState.Known before.core.erased.current.context.state source →
      GeneralNominalState.Known context.state source →
      Step registry root before (GeneralNominalVersionedRefresh232.refresh before context)
  | reobserve (focus : Occurrence roles)
      (revision : GeneralNominalReobservationSteps.Revision before.core.erased.current) :
      Generated before.core.erased.current root focus →
      GeneralNominalCenteredHeadMatStepRefresh.Reobserve before.legacy revision →
      GeneralNominalReobservationSteps.Improves revision →
      Step registry root before (GeneralNominalVersionedRefresh232.reobserve before revision)

theorem step_models (step : Step registry root before after) (valid : Models after model) :
    Models before model := by
  cases step with
  | legacyPrefix old =>
    exact (lift_models _ model).mpr
      (GeneralDictionaryDefaultKernel208.stepModels old ((lift_models _ model).mp valid))
  | install action => exact GeneralNominalVersionedInstallStep232.step_models action valid
  | refresh focus context generated certificate source member unknown known =>
    exact (GeneralNominalVersionedRefresh232.refresh_models certificate model).mp valid
  | reobserve focus revision generated certificate improved =>
    exact (GeneralNominalVersionedRefresh232.reobserve_models certificate model).mp valid

theorem lift_path (path : B4Target.Steps (GeneralDictionaryDefaultKernel208.Step registry root) before after) :
    B4Target.Steps (Step registry root) (lift before) (lift after) := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact .tail ih (.legacyPrefix step)

theorem steps_models (path : B4Target.Steps (Step registry root) before after) (valid : Models after model) :
    Models before model := by
  induction path with
  | refl => exact valid
  | tail path step ih => exact ih (step_models step valid)

def Reachable (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles)
    (state : State roles) : Prop :=
  B4Target.Steps (Step registry root) (initial context root) state

theorem reachable_step (path : Reachable registry context root before)
    (step : Step registry root before after) : Reachable registry context root after := .tail path step

theorem source_models (path : Reachable registry context root state) (valid : Models state model) :
    GeneralNominalState.Models context.state model :=
  ((initial_models context root model).mp (steps_models path valid)).1

end Yulang.GeneralNominalVersionedMigration232
