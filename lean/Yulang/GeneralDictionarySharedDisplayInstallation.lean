import Yulang.GeneralNominalSharedExamples

/-! A real first installation in the certified-origin SharedSteps relation.
The packet has a where-child, so the installation is novel. This is an
inhabited prefix, not a proof of whole-program completion or a child dictionary. -/
namespace Yulang.GeneralDictionarySharedDisplayInstallation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralDeclarationExamples (roles display display_checked)
open GeneralNominalExamples (registry context displayRoot displayChild)
open GeneralNominalSupport (initial)
open GeneralNominalSharedExamples (packet)

abbrev start := GeneralNominalSupport.initial (context true) displayRoot
noncomputable def after := GeneralNominalSharedSteps.install start (packet false) []

theorem located : GeneralNominalRecursiveCandidates.arguments (context true) displayRoot =
    some [(0,0)] := by rfl

theorem prepared : GeneralNominalRecursiveCandidates.Prepared registry (context true)
    displayRoot display display_checked := by
  obtain ⟨_,candidate,visible,checked,identity,role,bounds,found,prepared,_⟩ :=
    GeneralNominalRecursiveExamples.display_survivor
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · cases identity
  · exact prepared
  · cases identity

theorem children : (packet false).children = [displayChild] := by
  obtain ⟨_,candidate,visible,checked,identity,role,bounds,found,_,emitted⟩ :=
    GeneralNominalRecursiveExamples.display_survivor
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · cases identity
  · have equal := Option.some.inj (located.symm.trans found)
    subst bounds
    exact emitted.symm
  · cases identity

theorem selected : GeneralNominalFeedbackK2.Local registry start.current displayRoot
    (.selected (packet false).declaration.id (packet false).children) := by
  rw [children]
  exact GeneralNominalSupportBoundary.selected_old GeneralNominalSupportExamples.display_selected

theorem installable : GeneralNominalFeedbackSteps.Installable registry start.current (packet false) := by
  have preparation := prepared
  obtain ⟨_,_,_,bounds,found,_,_,model,branch⟩ := preparation
  have equal := Option.some.inj (located.symm.trans found)
  subst bounds
  refine ⟨⟨rfl,rfl,by simp [start,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial],
    by simp,rfl,located,prepared,
    GeneralNominalFeedbackK2.selected_legacy selected,?_,?_,?_,?_⟩,selected,?_⟩
  · intro prior member; cases member
  · intro other member _
    have same := List.mem_singleton.mp member; subst other; exact .refl _
  · exact ⟨model,(initial_models ..).mpr
      (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ branch).1,branch⟩
  · exact GeneralNominalJointCandidates.initial_joint registry (context true) displayRoot
      display (by simp) display_checked rfl [(0,0)] located prepared model branch
  · intro other member _
    have same := List.mem_singleton.mp member; subst other; exact .refl _

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed start.current (packet false) := by
  intro committed
  have absent := committed.2 displayChild (by rw [children]; simp)
  cases absent

theorem step : GeneralNominalSharedSteps.Step registry displayRoot start after :=
  ⟨displayRoot,.root,.install (packet false) [] installable novel GeneralNominalSharedExamples.display_guard⟩

theorem inhabited : ∃ model, Models after.current model := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,⟨model,valid,branch⟩,_⟩ := installable.1
  exact ⟨model,(GeneralNominalSharedSteps.install_models (packet := packet false)
    (state := start) (support := []) rfl model).mpr ⟨valid,branch⟩⟩

/-- The successor really contains the new certified-emitter site. -/
theorem certified_child_site :
    GeneralNominalSharedEmission.childSite (packet false) displayChild ∈ after.current.sites := by
  change _ ∈ start.current.sites ++ (packet false).children.map (GeneralNominalSharedEmission.childSite (packet false))
  rw [children]
  simp

theorem generated_child : Generated after.current displayRoot displayChild := by
  apply Generated.child Generated.root
  change (displayRoot,displayChild) ∈ start.current.edges ++
    (packet false).children.map (fun child => ((packet false).site.occurrence,child))
  rw [children]
  simp [GeneralNominalDemandMerging.pointSite]

end Yulang.GeneralDictionarySharedDisplayInstallation
