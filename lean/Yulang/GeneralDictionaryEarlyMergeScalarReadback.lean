import Yulang.GeneralDictionaryEarlyMergeScalarEvidence

/-! Real full three-node classification for the extended-registry alias fixture.
The successful classification and evidence do not by themselves prove Stable. -/
namespace Yulang.GeneralDictionaryEarlyMergeScalarReadback
open GeneralDictionaryEarlyMergeScalarExample GeneralDictionaryEarlyMergeScalarClassification
open GeneralDictionaryEarlyMergeScalarEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (context state model state_models listDescriptor displayRoot interpretation intDisplay int_display_checked)

private theorem metadata : Metadata registry current := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,catalogue,_⟩ := GeneralDictionaryEarlyMergeScalarEvidence.parent_instance model finish_model
  exact catalogue

private theorem linked : GeneralNominalState.Linked current.state displayRoot.demand := by
  constructor
  · intro index
    have member : 0 ∈ GeneralNominalState.sources current.state :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(0 : Fin 2),rfl⟩))))
    exact ⟨member,member⟩
  · intro output member; cases member

private theorem root_ready : ¬ GeneralNominalState.RootPending current.state displayRoot.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(0 : Fin 2),rfl,Or.inr ⟨listDescriptor,rfl⟩⟩

private theorem root_fresh : GeneralNominalAllocation.Fresh current.state registry displayRoot.identity := by
  intro key member _
  exact List.mem_append_right _ member

private theorem parent_prepared : Prepared registry current displayRoot declaration checked := by
  obtain ⟨decl,visible,check,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ := GeneralDictionaryEarlyMergeScalarEvidence.parent_instance model finish_model
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · exact ⟨catalogue,linked,root_fresh,bounds,located,finished,requested,model,branch⟩
  · contradiction

private theorem parent_survivor : Survivor registry current displayRoot 1 children := by
  obtain ⟨decl,visible,check,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ := GeneralDictionaryEarlyMergeScalarEvidence.parent_instance model finish_model
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · exact ⟨root_ready,declaration,by simp,checked,rfl,rfl,bounds,located,parent_prepared,emitted⟩
  · contradiction

private theorem wrong_failed : Failed registry current displayRoot intDisplay int_display_checked := by
  refine ⟨metadata,root_fresh,[((0 : Fin 2),(0 : Fin 2))],?_,?_,?_,Or.inl ?_⟩ <;> decide +kernel
private def height (source : Nat) : Nat := if source = 0 then 1 else 0
private theorem model_height (source : Nat) : (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

private theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle finish.current source :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model finish_model height model_height
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) source

private theorem raw_acyclic (slot : Fin current.state.base.slots) : ¬ GeneralNominalCycleK2.Cycle current.state slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge current.state first last →
      height last.val < height first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model finish_model.1
      exact GeneralNominalOutputGrowthModels.observation_decreases model height model_height _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path current.state first last → height last.val ≤ height first.val := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

private theorem no_raw_recurs (slot : Fin current.state.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt current.state slot := by
  rintro (⟨child,edge,path⟩ | ⟨cycle,_⟩)
  · exact raw_acyclic slot ⟨child,GeneralNominalCycleK2.direct_edge_sound edge,GeneralNominalCycleK2.direct_path_sound path⟩
  · exact raw_acyclic slot cycle

private theorem no_root (root : Occurrence roles) : ¬ GeneralNominalFeedbackK2.RootK2 finish.current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,index,cycle,_⟩)
  · exact no_raw_recurs slot cycle
  · exact acyclic _ cycle
private theorem no_candidate (root : Occurrence roles) : ¬ GeneralNominalFeedbackK2.CandidateK2 registry finish.current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw_recurs visited.1 cycle
  · exact acyclic _ cycle

private theorem no_legacy (root : Occurrence roles) :
    ¬ (GeneralNominalLocalBoundary.recursiveFields roles).RootK2 registry current root ∧
    ¬ (GeneralNominalLocalBoundary.recursiveFields roles).CandidateK2 registry current root := by
  constructor
  · rintro ⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩; exact Fin.elim0 kind
  · rintro ⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩; exact Fin.elim0 kind


private theorem all_heads (slot : Fin 2) :
    ∃ test observation, GeneralNominalSupport.Head (state true) ((state true).base.source slot) test observation ∧
      GeneralNominalSupport.Head current.state (current.state.base.source slot) test observation := by
  have bounded := slot.isLt
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero
    subst slot
    exact ⟨_,_,.nominal 0 listDescriptor rfl,GeneralNominalSupport.Head.nominal (snapshot := current.state) (0 : Fin 2) listDescriptor rfl⟩
  · have same : slot = (1 : Fin 2) := by apply Fin.ext; omega
    subst slot
    exact ⟨_,_,.scalar 1 .int rfl,GeneralNominalSupport.Head.scalar (snapshot := current.state) (1 : Fin 2) .int rfl⟩

private theorem guard (root : Occurrence roles) (slot : Fin 2)
    (args : ∀ index, root.demand.arguments index = (slot.val,slot.val)) :
    GeneralNominalSupport.DecisionGuard finish registry root [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    rw [show (root.demand.arguments index).1 = slot.val by rw [args index]]
    obtain ⟨test,observation,source,seen⟩ := all_heads slot
    exact GeneralNominalSupport.source_ready finish slot.val test observation observation source seen []
  · intro declaration visible role bounds located read member
    obtain ⟨test,observation,source,seen⟩ := all_heads read
    exact GeneralNominalSupport.source_ready finish read.val test observation observation source seen []




theorem parent_selected : GeneralNominalFeedbackK2.Local registry finish.current displayRoot (.selected 1 children) := by
  refine .selected ⟨root_ready,no_root _,no_candidate _,?_⟩ ⟨parent_survivor,?_⟩
  · rintro (⟨_,decl,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl
      · exact notPrepared parent_prepared
      · exact notFailed wrong_failed
    · exact legacy.elim (fun h => (no_legacy _).1 h.1) (fun h => (no_legacy _).2 h.1)
  · intro key cs given
    have original := given
    obtain ⟨_,decl,visible,check,identity,role,bounds,located,ready,_⟩ := given
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl
    · have equal : key = 1 := identity.symm; subst key
      exact ⟨rfl,survivor_children_functional registry registry_checked current displayRoot 1 cs children original parent_survivor⟩
    · exact False.elim (GeneralNominalLocalBoundary.recursive_failed_not_prepared registry current displayRoot intDisplay check wrong_failed ready)

theorem supported_parent : GeneralNominalSupportBoundary.Local registry finish displayRoot (.selected 1 children) :=
  GeneralNominalSupportBoundary.selected_supported parent_selected [] (guard displayRoot 0 (fun _ => rfl))

theorem classified : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
    registry finish displayRoot (.selected payload) := by
  have parent := (GeneralNominalSupportBoundary.local_correspondence registry finish displayRoot _).mpr supported_parent
  rw [children_exact] at parent
  have first := (GeneralNominalSupportBoundary.local_correspondence registry finish (child 10) _).mpr (supported_child 10)
  have last := (GeneralNominalSupportBoundary.local_correspondence registry finish (child 11) _).mpr (supported_child 11)
  cases parent with
  | selected safe unique =>
    apply B4TargetV3.Classify.selected safe unique
    cases first with
    | selected oneSafe oneUnique =>
      cases last with
      | selected twoSafe twoUnique =>
        exact .cons (.selected oneSafe oneUnique .nil) (.cons (.selected twoSafe twoUnique .nil) .nil)

theorem actual_classified_evidence :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot (.selected payload) ∧
    ∀ assignment, Models finish.current assignment →
      GeneralDictionaryRecursiveEvidence.Evidence registry current assignment displayRoot payload :=
  ⟨reachable,finish_model,classified,full_evidence⟩
end Yulang.GeneralDictionaryEarlyMergeScalarReadback
