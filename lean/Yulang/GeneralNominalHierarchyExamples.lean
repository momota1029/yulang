import Yulang.GeneralNominalRoleHierarchy
import Yulang.GeneralNominalActualInspectionExamples
import Yulang.GeneralDictionarySupportRecursiveExample

/-! Wrap(List Int) terminates under the actual-inspection Step. Its registry
still contains recursive Display declarations; only the reachable Wrap and
Container roles are stratified. The first step really emits a named child. -/
namespace Yulang.GeneralNominalHierarchyExamples
open GeneralDeclarations GeneralNominalSaturationState GeneralNominalRoleHierarchy
open GeneralDeclarationExamples (roles wrap wrap_checked)
open GeneralNominalExamples (registry context wrapRoot wrapChild)
open GeneralNominalSupport (initial)
open GeneralNominalSharedExamples (packet)
open GeneralNominalActualInspectionSteps (Step)

def active (role : Nat) : Prop := role = 1 ∨ role = 2
def rank (role : Nat) : Nat := if role = 1 then 1 else 0

theorem hierarchy : Hierarchy registry active rank := by
  constructor
  intro declaration visible live clause present
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · cases present
  · cases live with
    | inl impossible => cases impossible
    | inr impossible => cases impossible
  · cases List.mem_singleton.mp present
    exact ⟨Or.inr rfl,by decide +kernel⟩

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry (context true) wrapRoot where
  roles_agree := rfl
  metadata := GeneralDictionarySupportRecursiveExample.initial_source.metadata
  linked := GeneralDictionarySupportRecursiveExample.initial_source.linked
  intervals := fun _ _ _ => CommonNominalFullCarrier.subtype_refl _
  below_seed := GeneralDictionarySupportRecursiveExample.initial_source.below_seed
  unallocated := rfl

theorem point_source : GeneralNominalActualBudget.PointSource (context true) wrapRoot := by
  constructor
  · intro bounds present
    simp only [List.mem_cons,List.not_mem_nil,or_false] at present
    rcases present with rfl | rfl <;> rfl
  · intro slot descriptor recorded bounds present
    by_cases zero : slot = 0
    · subst slot
      cases Option.some.inj recorded
      cases List.mem_singleton.mp present
      rfl
    · simp [GeneralNominalExamples.state,zero] at recorded
  · intro slot descriptor recorded bounds present
    by_cases zero : slot = 0
    · subst slot
      cases Option.some.inj recorded
      cases List.mem_singleton.mp present
    · simp [GeneralNominalExamples.state,zero] at recorded
  · intro index; rfl

theorem wrap_accessible : Acc (fun next current => Step registry wrapRoot current next)
    (GeneralNominalSupport.initial (context true) wrapRoot) :=
  accessible GeneralNominalExamples.registry_checked hierarchy initial_source (Or.inl rfl)

theorem prepared : GeneralNominalRecursiveCandidates.Prepared registry (context true) wrapRoot wrap wrap_checked := by
  obtain ⟨_,candidate,visible,checked,identity,role,bounds,found,prepared,_⟩ :=
    GeneralNominalRecursiveExamples.wrap_survivor
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · cases identity
  · cases identity
  · exact prepared

theorem children : (packet true).children = [wrapChild] := by
  obtain ⟨_,candidate,visible,checked,identity,role,bounds,found,_,emitted⟩ :=
    GeneralNominalRecursiveExamples.wrap_survivor
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · cases identity
  · cases identity
  · have equal : bounds = [(0,0)] := Option.some.inj found.symm
    subst bounds
    exact emitted.symm

theorem selected : GeneralNominalFeedbackK2.Local registry (GeneralNominalSupport.initial (context true) wrapRoot).current wrapRoot
    (.selected (packet true).declaration.id (packet true).children) := by
  rw [children]
  exact GeneralNominalSupportBoundary.selected_old GeneralNominalSupportExamples.wrap_selected

theorem installable : GeneralNominalFeedbackSteps.Installable registry (GeneralNominalSupport.initial (context true) wrapRoot).current (packet true) := by
  obtain ⟨_,_,_,bounds,found,_,_,model,branch⟩ := prepared
  have equal : bounds = [(0,0)] := Option.some.inj found.symm
  subst bounds
  refine ⟨⟨rfl,rfl,by simp [GeneralNominalSupport.initial,GeneralNominalSaturationState.initial],
    by simp,rfl,rfl,prepared,GeneralNominalFeedbackK2.selected_legacy selected,?_,?_,?_,?_⟩,selected,?_⟩
  · intro prior member; cases member
  · intro other member _
    have same := List.mem_singleton.mp member; subst other; exact .refl _
  · exact ⟨model,(initial_models ..).mpr
      (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ branch).1,branch⟩
  · exact GeneralNominalJointCandidates.initial_joint registry (context true) wrapRoot
      wrap (by simp) wrap_checked rfl [(0,0)] rfl prepared model branch
  · intro other member _
    have same := List.mem_singleton.mp member; subst other; exact .refl _

theorem novel : ¬ GeneralNominalFeedbackSteps.Committed (GeneralNominalSupport.initial (context true) wrapRoot).current (packet true) := by
  intro committed
  have absent := committed.2 wrapChild (by rw [children]; simp)
  cases absent

theorem wrap_step : Step registry wrapRoot (GeneralNominalSupport.initial (context true) wrapRoot)
    (GeneralNominalSharedSteps.install (GeneralNominalSupport.initial (context true) wrapRoot) (packet true) []) :=
  ⟨wrapRoot,.root,.install (packet true) [] installable novel GeneralNominalActualInspectionExamples.wrap_guard⟩

theorem child_is_named : wrapChild.demand.outputs = [⟨1,GeneralNominalExamples.itemTarget⟩] := rfl

theorem after_wrap_accessible : Acc (fun next current => Step registry wrapRoot current next)
    (GeneralNominalSharedSteps.install (GeneralNominalSupport.initial (context true) wrapRoot) (packet true) []) :=
  wrap_accessible.inv wrap_step

end Yulang.GeneralNominalHierarchyExamples
