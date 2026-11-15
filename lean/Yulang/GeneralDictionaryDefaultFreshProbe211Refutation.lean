import Yulang.GeneralDictionaryDefaultFreshProbe211Conflict
import Yulang.GeneralDictionaryDefaultProduction208

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultFreshProbe211Refutation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralDictionaryDefaultFreshProbe211Source GeneralDictionaryDefaultFreshProbe211Install
open GeneralDictionaryDefaultFreshProbe211State GeneralDictionaryDefaultFreshProbe211Stable
open GeneralDictionaryDefaultFreshProbe211Conflict
open GeneralNominalCenteredHeadAllocMergedConflict
open GeneralNominalSaturationState (Alias)
open GeneralNominalCenteredHeadMatStepJournal (Models)

 theorem c_ne_a : cSite.occurrence.identity ≠ aSite.occurrence.identity := by
  intro same
  have key := (GeneralNominalIdentities.source_identity snapshot.seed _ _).mp same
  have bad := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) key
  contradiction
 theorem c_ne_b : cSite.occurrence.identity ≠ bSite.occurrence.identity := by
  intro same
  have key := (GeneralNominalIdentities.source_identity snapshot.seed _ _).mp same
  have bad := congrArg (fun key : GeneralNominalIdentities.Origin => key.2.2.2.1) key
  contradiction

 theorem isolated (path : Alias (stage atoms).core.erased.current one two) :
    one = focus.identity ↔ two = focus.identity := by
  induction path with
  | refl => exact Iff.rfl
  | edge member =>
      cases List.mem_singleton.mp member
      exact iff_of_false (Ne.symm c_ne_a) (Ne.symm c_ne_b)
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

 theorem not_merged : ¬ MergedClass (stage atoms) focus := by
  rintro ⟨first,last,member,_,alias⟩
  cases List.mem_singleton.mp member
  exact (Ne.symm c_ne_a) ((isolated alias).mp rfl)

 theorem selected_stage (good : Good atoms) (supported : Supported atoms) :
    GeneralNominalCenteredHeadAllocV7Boundary.Local sourceRegistry (stage atoms) focus (.selected 39 []) :=
  .ordinary (fun conflict => not_merged conflict.1) (selected good supported)

 theorem corrected_selected : GeneralDictionaryDefaultBoundary208.Local sourceRegistry final focus (.selected 39 []) := by
  apply GeneralDictionaryDefaultBoundary208.local_iff.mpr
  obtain ⟨atoms,good,supported,same⟩ := final_shape
  rw [same]
  exact selected_stage good supported

 theorem corrected_reachable : B4TargetV7.Reachable
    (GeneralDictionaryDefaultBoundary208.boundary roles) sourceRegistry root final :=
  GeneralDictionaryDefaultBoundary208.old_reachable final_reachable

 theorem corrected_stable : GeneralDictionaryDefaultBoundary208.Stable sourceRegistry final focus := by
  intro target generated after action
  cases action with
  | administrative action => exact final_stable_focus target generated after (.administrative action)
  | refresh target context certificate source member unknown known =>
      exact final_stable_focus target generated _ (.refresh target context certificate source member unknown known)
  | merge first last one two same novel =>
      exact final_stable_focus first.occurrence generated _ (.merge first last one two same novel)
  | install effect enabled novel =>
      obtain ⟨model,valid,_⟩ := enabled.common
      exact final_empty ⟨model,valid⟩

 theorem not_recorded : ¬ GeneralDictionaryDefaultProduction208.Recorded final focus 39 [] := by
  obtain ⟨atoms,_,_,same⟩ := final_shape
  rw [same]
  rintro ⟨p,member,_,key,_⟩
  cases List.mem_singleton.mp member
  cases key

 /-- This refutes the stronger completion helper, not GeneratedChildren or EvidenceNode. -/
 theorem not_freshCompletion : ¬ GeneralDictionaryDefaultProduction208.FreshCompletion roles := by
  intro complete
  obtain ⟨effect,_,_,_,_,_,extension⟩ := complete sourceRegistry ⟨rfl,source_checked⟩
    final root focus 39 [] corrected_reachable (Or.inr final_generated)
    corrected_stable corrected_selected not_recorded
  obtain ⟨model,valid,_⟩ := extension.2
  exact final_empty ⟨model,valid⟩

 theorem evidence_vacuous : B4SkeletonV7.EvidenceAt
    (GeneralDictionaryDefaultBoundary208.boundary roles) sourceRegistry final root := by
  intro model valid
  exact False.elim (final_empty ⟨model,valid⟩)

 theorem children_vacuous : ∀ child ∈ ([] : List (Occurrence roles)),
    (GeneralDictionaryDefaultBoundary208.boundary roles).Generated sourceRegistry final root child := by
  intro child member; cases member

end Yulang.GeneralDictionaryDefaultFreshProbe211Refutation
