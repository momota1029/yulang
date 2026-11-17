import Yulang.GeneralNominalVersionedKernel232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedEquate234
open GeneralNominalVersionedJournal232 GeneralNominalVersionedAdministrative232
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state : State roles}

theorem models_iff (equal : GeneralNominalVersionedKernel232.Equal state first last) (model : Assignment) :
    Models (equate state first last) model ↔ Models state model := by
  constructor
  · exact equate_models
  · intro valid
    obtain ⟨legacy,plans,effects⟩ := valid
    refine ⟨?_,plans,?_⟩
    · refine ⟨(GeneralNominalState.extend_models ..).mpr ⟨legacy.1,?_⟩,
        legacy.2.1,legacy.2.2.1,legacy.2.2.2.1,legacy.2.2.2.2.1,?_⟩
      · exact (GeneralNominalCaptureMerges.equations_exact model first (.var last)).mpr
          (equal model ⟨legacy,plans,effects⟩)
      · intro effect member
        have pair := legacy.2.2.2.2.2 effect member
        exact ⟨pair.1,GeneralNominalCenteredHeadMatEffects.restrict
          (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
            (before := (equate state first last).core) (after := state.core)
            (fun _ h => h) (fun _ h => h)) pair.2⟩
    · intro effect member
      have pair := effects effect member
      exact ⟨pair.1,live_restrict
        (GeneralNominalCenteredHeadStepEffects.requests_subset_of_sites_aliases
          (before := (equate state first last).core) (after := state.core)
          (fun _ h => h) (fun _ h => h)) pair.2⟩

theorem feedback_equal : GeneralNominalFeedbackSteps.RawEqual (equate state first last).core.erased.current first last :=
  GeneralNominalFeedbackSteps.equate_feedback _ first last

end Yulang.GeneralNominalVersionedEquate234
