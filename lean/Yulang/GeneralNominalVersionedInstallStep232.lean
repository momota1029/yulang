import Yulang.GeneralNominalVersionedInstallProperties232
set_option backward.isDefEq.respectTransparency false
/-! A concrete nonredundant installation relation, not yet the complete
successor solver kernel. Scheduling, all administrative rules, K2 priority,
and global termination must still be connected to the unchanged V8 classifier. -/
namespace Yulang.GeneralNominalVersionedInstallStep232
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Generated)

def Committed (state : State roles) (plan : Plan roles) : Prop :=
  (∀ model, Models state model → GeneralNominalVersionedPlans231.Holds plan model ∧
    GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan model) ∧
  ∀ child ∈ GeneralNominalVersionedFrame231.children plan.packet,
    (plan.packet.site.occurrence,child) ∈ state.core.erased.current.edges

structure Enabled (registry : Registry) (state : State roles) (effect : Effect roles) : Prop where
  registry_eq : effect.registry = registry
  snapshot_eq : effect.snapshot = state.core
  common : ∃ model, InstallationModels state effect model

inductive Step (registry : Registry) (root : Occurrence roles) : State roles → State roles → Prop
  | install (effect : Effect roles) : Enabled registry before effect →
      Generated before.core.erased.current root effect.plan.packet.site.occurrence →
      ¬ Committed before effect.plan → Step registry root before (install before effect)

theorem step_models (step : Step registry root before after) (valid : Models after model) :
    Models before model := by
  cases step with
  | install effect enabled _ _ => exact GeneralNominalVersionedInstall232.step_models enabled.snapshot_eq valid

theorem step_inhabited (step : Step registry root before after) : ∃ model, Models after model := by
  cases step with
  | install effect enabled _ _ =>
    obtain ⟨model,valid⟩ := enabled.common
    exact ⟨model,(install_models enabled.snapshot_eq).mpr valid⟩

theorem installed_committed (state : State roles) (effect : Effect roles) :
    Committed (install state effect) effect.plan := by
  constructor
  · intro model valid
    exact ⟨valid.2.1 _ (List.mem_cons_self ..),(valid.2.2 _ (List.mem_cons_self ..)).2⟩
  · exact fun _ member => installed_child member

theorem no_identical_reinstall :
    ¬ (¬ Committed (install state effect) effect.plan) := fun novel => novel (installed_committed state effect)

theorem generated_preserved (step : Step registry root before after)
    (given : Generated before.core.erased.current root focus) :
    Generated after.core.erased.current root focus := by
  cases step with
  | install => exact GeneralNominalVersionedInstallProperties232.generated_preserved given

theorem steps_models (path : B4Target.Steps (Step registry root) before after)
    (valid : Models after model) : Models before model := by
  induction path with
  | refl => exact valid
  | tail path step ih => exact ih (step_models step valid)

end Yulang.GeneralNominalVersionedInstallStep232
