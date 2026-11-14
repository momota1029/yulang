import Yulang.GeneralNominalNonleafAdministrative193
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalNonleafChild193
open GeneralNominalNonleafPlan193 GeneralNominalNonleafInstallation193 GeneralNominalNonleafSafety193 GeneralNominalNonleafAdministrative193
open GeneralNominalExamples (registry displayRoot displayChild model intDisplay int_display_checked)
open GeneralDeclarationExamples (roles display display_checked)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadCandidates
open GeneralNominalCenteredHeadOutputs

noncomputable abbrev childPacket : GeneralNominalSaturationState.Packet roles :=
  ⟨registry,current,GeneralNominalSharedEmission.childSite packet displayChild,intDisplay,int_display_checked,[((1 : Fin 2),(1 : Fin 2))]⟩
noncomputable abbrev childPlan : Plan roles := ⟨childPacket,centerSite,rfl⟩

theorem survivor : Survivor registry current displayChild 3 [] := by
  have old := GeneralDictionarySupportRecursiveClassification.leaf_selected
  cases old with
  | selected _ unique => exact old_survivor_head unique.1

theorem prepared : Prepared registry current displayChild intDisplay := by
  obtain ⟨_,d,visible,check,key,_,bounds,located,ready,_⟩ := survivor
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · exact ready
  · cases key
  · cases key

theorem wrong_failed : Failed registry current displayChild display := by
  refine ⟨prepared.1,prepared.2.2.1,[((1 : Fin 2),(1 : Fin 2))],rfl,?_,?_,Or.inl ?_⟩ <;> decide +kernel

theorem unique : Unique registry current displayChild 3 [] := by
  refine ⟨survivor,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,check,identity,role,bounds,located,ready,_⟩ := found
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · have same : key = 3 := identity.symm
    subst key
    exact ⟨rfl,survivor_children_functional GeneralNominalExamples.registry_checked copy survivor⟩
  · obtain ⟨_,_,_,bs,loc,finished,_⟩ := ready
    have equal := Option.some.inj (loc.symm.trans located)
    subst bs
    have equal := Option.some.inj located
    subst bounds
    exact False.elim ((by decide +kernel : (GeneralNominalRecursiveCandidates.report current display [((1 : Fin 2),(1 : Fin 2))]).conflicts ≠ []) finished.2.1)
  · contradiction

theorem frame : Frame registry finish.core displayChild 3 childPlan := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,by simp,rfl,rfl,prepared⟩
  · rw [raw_sites]; simp
  · rw [center_sites]; simp

theorem safe : B4TargetV6.SafeKnown (GeneralNominalCenteredHeadWFBoundary.boundary roles) registry finish displayChild := by
  have old := child_center_selected
  cases old with
  | selected oldSafe oldUnique =>
    refine ⟨survivor.1,oldSafe.2.1,?_,?_⟩
    · rintro (raw | ⟨_,_,_,_,_,_,_,_,_,_,_,cycle⟩)
      · exact oldSafe.2.2.1 (Or.inl raw)
      · exact centered_acyclic _ cycle
    · rintro (⟨_,d,visible,role,notFailed,notPrepared⟩ | legacy | decision | admin)
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
        rcases visible with rfl | rfl | rfl
        · exact notPrepared prepared
        · exact notFailed wrong_failed
        · contradiction
      · exact oldSafe.2.2.2 (Or.inl (Or.inr legacy))
      · exact decision child_decision
      · exact admin child_ready
end Yulang.GeneralNominalNonleafChild193
