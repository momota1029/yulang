import Yulang.GeneralMixedCompoundPointSafe308
import Yulang.GeneralNominalVersionedMixedResolver236

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 15000000
namespace Yulang.GeneralMixedCompoundPointOutcome308
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry declaration checked)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralMixedCompoundPointFirstPlan308 (candidateModel)
open GeneralMixedCompoundPointViewTrust308 (observed)
open GeneralMixedCompoundPointRoot308 (plan packet frame held models_observed child_exact)
open GeneralMixedCompoundPointSites308 (equal_outputs)
open GeneralMixedCompoundPointEvidence308 (ready class_effects local_certificate witnessed_request no_recursive_root)
open GeneralMixedCompoundPointSafe308 (unique safe)
open GeneralMixedCompoundPointAdmin308 (child_ready)
open GeneralMixedCompoundPointChild308 (reachable known no_inspection_pending no_survivor)
open GeneralNominalVersionedDiagnostic232 (OutputConflict SharingConflict)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary Local)
open CommonRoleOutermostResolver

theorem output_clear :
    ¬ OutputConflict registry observed root declaration.id := by
  intro conflict
  exact conflict.2 ⟨candidateModel,models_observed,
    ⟨⟨_,unique⟩,plan,frame,ready,GeneralNominalVersionedDiagnostic232.head_equations
      (held _ models_observed),class_effects⟩⟩

theorem sharing_clear : ¬ SharingConflict registry observed root := by
  rintro ⟨key,kids,chosen,_,bad⟩
  have same := (unique.2 key kids chosen.1).1
  subst key
  exact bad.2.2 ⟨candidateModel,models_observed,plan,frame,
    GeneralNominalVersionedHeadSharing232.packet_holds _ _ (held _ models_observed)⟩

theorem merged_clear :
    ¬ GeneralNominalVersionedMergedConflict232.MergedOutputConflict observed root :=
  GeneralNominalVersionedMergedConflict232.models_exclude_conflict models_observed
    (fun focus _ => equal_outputs _ focus) (equal_outputs _ root)

theorem local_root : Local sourceRegistry observed root (.selected declaration.id [childSite.occurrence]) := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  have chosen : GeneralNominalVersionedDiagnostic232.Local registry observed root
      (.selected declaration.id (GeneralNominalVersionedFrame231.children packet)) :=
    .ordinary sharing_clear (.ordinary merged_clear (.selected safe unique output_clear))
  rw [child_exact] at chosen
  exact chosen

theorem local_child : Local sourceRegistry observed childSite.occurrence .rejected := by
  apply GeneralNominalVersionedMixedSourceBoundary234.local_iff.mpr
  apply GeneralNominalVersionedMixedBoundary234.local_iff.mpr
  have noSharing : ¬ (GeneralNominalVersionedDiagnostic232.boundary roles).SharingConflict registry observed childSite.occurrence := by
    rintro ⟨key,kids,choice,_⟩
    exact no_survivor key kids choice.1
  apply B4TargetV8.Local.ordinary noSharing
  classical
  by_cases merge : (GeneralNominalVersionedDiagnostic232.boundary roles).toV7.MergedOutputConflict registry observed childSite.occurrence
  · apply B4TargetV7.Local.mergedRejected merge
    rintro ⟨_,key,kids,_,_,one,_,_⟩
    exact no_survivor key kids one
  · apply B4TargetV7.Local.ordinary merge
    apply B4TargetV6.Local.rejected
    refine ⟨known,Or.inr (Or.inr ⟨?_,Or.inl no_survivor⟩)⟩
    rintro (pending|absent)
    · exact no_inspection_pending pending
    · exact absent child_ready

theorem tree :
    GeneralNominalVersionedMixedResolver236.tree ⟨rfl,checked⟩ reachable root =
      .selected declaration.id [.rejected] :=
  (GeneralNominalVersionedMixedResolver236.tree_exact ⟨rfl,checked⟩ reachable root _).mpr
    (.selected local_root (.cons (.rejected local_child) .nil))

theorem result :
    classification (GeneralNominalVersionedMixedResolver236.tree ⟨rfl,checked⟩ reachable root) = .rejected := by
  rw [tree]
  rfl

private theorem selected_inv {focus : GeneralSourceDictionaries.Occurrence roles} {outcome}
    (h : B4TargetV8.Classify (boundary roles) sourceRegistry observed focus outcome) :
    ∀ payload, outcome = .selected payload →
      ∃ key kids dictionaries,
        Local sourceRegistry observed focus (.selected key kids) ∧
        All₂ (fun child d => B4TargetV8.Classify (boundary roles) sourceRegistry observed child (.selected d))
          kids dictionaries :=
  match h with
  | .pending _ => fun _ eq => nomatch eq
  | .rejected _ => fun _ eq => nomatch eq
  | .ambiguous _ => fun _ eq => nomatch eq
  | .selected choice kids => fun _ _ => ⟨_,_,_,choice,kids⟩

theorem result_not_selected (payload : GeneralDictionaryReadback.Payload) :
    ¬ B4TargetV8.Classify (boundary roles) sourceRegistry observed root (.selected payload) := by
  intro selected
  obtain ⟨key,kids,_,choice,children⟩ := selected_inv selected payload rfl
  have shape := B4TargetV8.local_functional choice local_root
  cases shape
  cases children with
  | cons chosen _ =>
    obtain ⟨_,_,_,picked,_⟩ := selected_inv chosen _ rfl
    cases B4TargetV8.local_functional picked local_child

end Yulang.GeneralMixedCompoundPointOutcome308
