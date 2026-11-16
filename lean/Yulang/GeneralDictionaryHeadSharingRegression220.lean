import Yulang.GeneralDictionaryHeadSharingBoundary220
import Yulang.GeneralDictionaryGroundCopy218SaturatedRefutation
import Yulang.GeneralDictionaryDefaultAvailability208

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryHeadSharingRegression220
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryHeadSharingConflict220
open GeneralDictionaryHeadSharingBoundary220 (boundary Local)
open GeneralDictionaryGroundCopy218Source
open GeneralDictionaryGroundCopy218Install (model childSite)
open GeneralDictionaryGroundCopy218SaturatedRefutation (final final_models final_selected final_reachable final_shape)

theorem final_frames : ∃ plan, GeneralNominalCenteredHeadOutputs.Frame registry final.core childSite.occurrence 1 plan := by
  obtain ⟨plan,frame,_⟩ := GeneralDictionaryDefaultAvailability208.selected_frame final_reachable final_selected
  exact ⟨plan,frame⟩

theorem final_no_sharing : ¬ Feasible registry final childSite.occurrence 1 := by
  rintro ⟨given,valid,plan,frame,holds⟩
  obtain ⟨atoms,good,equal⟩ := final_shape
  rw [equal] at valid frame
  exact GeneralDictionaryGroundCopy218SaturatedState.impossible given valid plan frame
    (GeneralDictionaryHeadSharing220.agreement_of_holds plan given holds)

theorem final_conflict : Conflict sourceRegistry final childSite.occurrence := by
  have unique : B4TargetV7.Unique (GeneralDictionaryDefaultBoundary208.boundary roles)
      sourceRegistry final childSite.occurrence 1 [] := by
    have prior := (B4TargetV7.selected_iff.mp final_selected).1
    cases prior with
    | selected safe unique clear => exact unique
  exact ⟨1,[],unique,⟨model,final_models⟩,final_frames,final_no_sharing⟩

theorem final_rejected : Local sourceRegistry final childSite.occurrence .rejected :=
  GeneralDictionaryHeadSharingBoundary220.conflict_rejected final_conflict

theorem final_not_pending : ¬ Local sourceRegistry final childSite.occurrence .pending :=
  GeneralDictionaryHeadSharingBoundary220.conflict_not_pending final_conflict

theorem final_not_selected (key children) : ¬ Local sourceRegistry final childSite.occurrence (.selected key children) :=
  GeneralDictionaryHeadSharingBoundary220.conflict_not_selected final_conflict

end Yulang.GeneralDictionaryHeadSharingRegression220
