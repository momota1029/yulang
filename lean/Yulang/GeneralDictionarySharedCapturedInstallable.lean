import Yulang.GeneralDictionarySharedCapturedGuards
import Yulang.GeneralNominalSupportSiblings
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDictionarySharedCapturedInstallable
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveInspection GeneralDictionarySharedOutputBinderScope
open GeneralDictionarySharedCapturedTargets GeneralDictionarySharedCapturedGuards
open GeneralNominalRecursiveCandidates GeneralNominalSupport
open GeneralDeclarationExamples (roles)
local instance : NeZero source.base.slots := ⟨by change 3 ≠ 0; omega⟩
abbrev start : GeneralNominalSupport.Tracked roles := GeneralNominalSupport.initial context root
private theorem no_feedback (identity : Nat) : ¬ GeneralNominalFeedbackK2.Cycle start.current identity :=
  GeneralNominalOutputGrowthModels.feedback_acyclic start.current (GeneralNominalOutputGrowth.finiteModel 1)
    ((initial_models context root _).mpr ((GeneralNominalOutputGrowthModels.source_models 1 _).mpr
      (GeneralNominalOutputGrowth.finite_prefix_models 1))) (fun i => 2-i) (fun _ => rfl)
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) identity

private theorem no_root : ¬ GeneralNominalFeedbackK2.RootK2 start.current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,_,cycle,_⟩)
  · exact GeneralNominalOutputGrowthModels.raw_acyclic 1 slot
      (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

private theorem no_candidate : ¬ GeneralNominalFeedbackK2.CandidateK2 registry start.current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact GeneralNominalOutputGrowthModels.raw_acyclic 1 visited.1
      (GeneralNominalCycleK2.recurs_cycle _ _ cycle)
  · exact no_feedback _ cycle

theorem p_only (d : Declaration) (visible : d ∈ registry.declarations) (role : d.role = root.demand.role) : d=capturedProposal := by
  simp only [registry,List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · rfl
  · cases role

theorem selected_old : GeneralNominalFeedbackK2.Local registry start.current root (.selected capturedProposal.id packet.children) := by
  refine .selected ⟨root_ready,no_root,no_candidate,?_⟩ ⟨survivor,?_⟩
  · rintro (pending | ⟨_,legacy⟩)
    · obtain ⟨_,d,visible,certified,role,failed,missing⟩ := pending
      have same := p_only d visible role
      subst d
      exact missing prepared
    · rcases legacy with ⟨⟨_,_,_,slot,_,cycle⟩,_⟩ | ⟨⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩,_⟩
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle
        exact Fin.elim0 kind
      · obtain ⟨⟨kind,_,_⟩,_⟩ := cycle
        exact Fin.elim0 kind
  · intro key kids survivor
    have copy := survivor
    obtain ⟨_,d,visible,certified,identity,role,_⟩ := survivor
    have same := p_only d visible role
    subst d
    subst key
    exact ⟨rfl,survivor_children_functional registry registry_checked context root capturedProposal.id kids packet.children copy survivor⟩
theorem enabled : GeneralNominalFeedbackSteps.Installable registry start.current packet := by
  let model := GeneralDictionarySharedCapturedModel.model
  have valid := GeneralDictionarySharedCapturedModel.source_models
  refine ⟨⟨rfl,rfl,by simp [start,GeneralNominalSupport.initial,GeneralNominalSaturationState.initial,packet],by simp [registry],rfl,located,prepared,
    GeneralNominalFeedbackK2.selected_legacy selected_old,?_,?_,?_,?_⟩,selected_old,?_⟩
  · intro prior member; cases member
  · intro other member same
    have equal := List.mem_singleton.mp member
    subst other
    exact .refl _
  · exact ⟨model,(initial_models ..).mpr valid,GeneralDictionarySharedCapturedModel.branch_models⟩
  · exact GeneralNominalJointCandidates.initial_joint registry context root capturedProposal (by simp [registry]) captured_proposal_checked rfl [(0,0)] located prepared model (GeneralDictionarySharedCapturedModel.branch_models)
  · intro other member same
    have equal := List.mem_singleton.mp member
    subst other
    exact .refl _


theorem reads_exact : readsMany source
    (GeneralNominalInspection.queries source context.interpretation capturedProposal) [(0,0)] = [0,1] := by
  rw [queries]
  simp only [readsMany.eq_def,List.append_nil]
  rw [reads.eq_def]
  change 0 :: readsMany source [.nominal 0 [.variables [0]]] [(1,1)] = [0,1]
  rw [readsMany.eq_def]
  simp only [List.append_nil]
  rw [reads.eq_def]
  have empty : readsMany source [] [] = [] := by rw [readsMany.eq_def]
  simp only [empty,List.append_nil]
  change 0 :: (1 :: readsMany source [.variables [0]] [(2,2)]) = [0,1]
  simp only [readsMany.eq_def,reads.eq_def,List.append_nil,List.nil_append]

theorem decisions : DecisionGuard start registry root [] := by
  have head0 : Head source 0 (.nominal 0 1)
      (.nominal source.base 0 (GeneralNominalOutputGrowthModels.descriptor 1 0 (by decide +kernel))) :=
    Head.nominal (snapshot := source) 0 _ rfl
  have head1 : Head source 1 (.nominal 0 1)
      (.nominal source.base 1 (GeneralNominalOutputGrowthModels.descriptor 1 1 (by decide +kernel))) :=
    Head.nominal (snapshot := source) 1 _ rfl
  have ready0 : ReadyAt start [] 0 := source_ready start 0 _ _ _ head0 head0 []
  have ready1 : ReadyAt start [] 1 := source_ready start 1 _ _ _ head1 head1 []
  refine ⟨(by intro _ h; cases h),(fun _ => ready0),?_⟩
  intro d visible role bounds loc slot member
  have same := p_only d visible role
  subst d
  have equal := Option.some.inj (located.symm.trans loc)
  subst bounds
  change slot ∈ readsMany source
    (GeneralNominalInspection.queries source context.interpretation capturedProposal) [(0,0)] at member
  rw [reads_exact] at member
  rcases List.mem_cons.mp member with zero | one
  · subst slot; exact ready0
  · have eq := List.mem_singleton.mp one
    subst slot; exact ready1

end Yulang.GeneralDictionarySharedCapturedInstallable
