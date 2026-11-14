import Yulang.GeneralNominalCenteredHeadStepCoverage
import Yulang.GeneralNominalCenteredHeadStepBoundary

/-! The prospective conflict predicate requires a positive current model.
An inconsistent live journal therefore cannot itself witness that predicate.
This limitation applies in particular after an inconsistent merge. -/
namespace Yulang.GeneralNominalCenteredHeadStepEmptyModels
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadStepBoundary
variable {roles : Roles.RoleDecls} {state : State roles}

theorem empty_no_conflict (empty : ¬ ∃ model, Models state model) (registry : Registry) (root : Occurrence roles) (key) :
    ¬ OutputConflict registry state root key := fun conflict => empty (conflict_inhabited conflict)

theorem empty_no_install (empty : ¬ ∃ model, Models state model) (registry : Registry) (plan : Plan roles) (support) :
    ¬ Installable registry state plan support := by
  intro enabled
  obtain ⟨model,valid,_⟩ := enabled.common
  exact empty ⟨model,valid⟩

theorem empty_safe_unique_selected (empty : ¬ ∃ model, Models state model)
    (safe : B4TargetV6.SafeKnown (boundary roles) registry state root)
    (unique : GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context root key children) :
    Local registry state root (.selected key children) :=
  .selected safe unique (empty_no_conflict empty registry root key)

theorem merge_empty_iff (first last : Site roles) (support) :
    (¬ ∃ model, Models (merge state first last support) model) ↔
      ¬ ∃ model, Models state model ∧
        PresenceNormalForm.All CommonNominalFullCarrier.model model
          (GeneralNominalDemandMerging.outputAtoms first.observed last.observed) ∧
        ∀ effect ∈ state.effects, effect.Live (GeneralNominalCenteredSteps.merge state.core first last support) model := by
  apply not_congr
  apply exists_congr
  intro model
  exact GeneralNominalCenteredHeadStepCoverage.merge_models state first last support model

end Yulang.GeneralNominalCenteredHeadStepEmptyModels
