import Yulang.GeneralDictionaryOutputMergeJointModels

/-! Actual local selection and recursive classification on the reached output
merge fixture. All decisions use the original support boundary, not a replacement
classifier. Stability and general V5 completeness are deliberately separate. -/
namespace Yulang.GeneralDictionaryOutputMergeClassification
open GeneralDictionaryOutputMergeSuccess
open GeneralDictionaryOutputMergeJointModels
open GeneralNominalExamples (context state model displayRoot listDescriptor)
open GeneralDeclarationExamples (roles constructors)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryOutputMergeAllModels

private theorem root_ready : ¬ GeneralNominalState.RootPending current.state displayRoot.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(0 : Fin 2),rfl,Or.inr ⟨listDescriptor,rfl⟩⟩

private theorem child_ready (n : Nat) : ¬ GeneralNominalState.RootPending current.state (child n).demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩

private def height (source : Nat) : Nat := if source = 0 then 1 else 0
private theorem model_height (source : Nat) : (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle finish.current source :=
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


theorem parent_prepared : Prepared registry current displayRoot declaration checked := by
  obtain ⟨d,visible,check,key,role,ready,rest⟩ := root_branch model finish_model
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · exact ready
  · contradiction

theorem child_prepared (n : Nat) (which : n = 10 ∨ n = 11) :
    Prepared registry current (child n) terminal terminal_checked := by
  obtain ⟨d,visible,check,key,role,ready,rest⟩ := child_branch model finish_model n which
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · contradiction
  · exact ready

theorem parent_survivor : Survivor registry current displayRoot 1 [child 10,child 11] := by
  obtain ⟨d,visible,check,key,role,bounds,located,finished,ready,emitted,metadata,branch⟩ :=
    GeneralDictionaryOutputMergeAllModels.current_parent_instance model finish_model
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · exact ⟨root_ready,declaration,by simp,check,key,role,bounds,located,parent_prepared,emitted⟩
  · contradiction

theorem child_survivor (n : Nat) (which : n = 10 ∨ n = 11) :
    Survivor registry current (child n) 7 [] := by
  obtain ⟨d,visible,check,key,role,bounds,located,finished,ready,emitted,metadata,branch⟩ :=
    GeneralDictionaryOutputMergeAllModels.current_terminal_instance model finish_model n which
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · contradiction
  · exact ⟨child_ready n,terminal,by simp,check,key,role,bounds,located,child_prepared n which,emitted⟩

theorem parent_selected : GeneralNominalFeedbackK2.Local registry finish.current displayRoot
    (.selected 1 [child 10,child 11]) := by
  refine .selected ⟨root_ready,no_root _,no_candidate _,?_⟩ ⟨parent_survivor,?_⟩
  · rintro (⟨_,d,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl
      · exact notPrepared parent_prepared
      · contradiction
    · exact legacy.elim (fun h => (no_legacy _).1 h.1) (fun h => (no_legacy _).2 h.1)
  · intro key children given
    have original := given
    obtain ⟨_,d,visible,check,identity,role,bounds,located,ready,_⟩ := given
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl
    · have equal : key = 1 := identity.symm
      subst key
      exact ⟨rfl,survivor_children_functional registry registry_checked current displayRoot 1 children
        [child 10,child 11] original parent_survivor⟩
    · contradiction

theorem child_selected (n : Nat) (which : n = 10 ∨ n = 11) :
    GeneralNominalFeedbackK2.Local registry finish.current (child n) (.selected 7 []) := by
  refine .selected ⟨child_ready n,no_root _,no_candidate _,?_⟩ ⟨child_survivor n which,?_⟩
  · rintro (⟨_,d,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl
      · contradiction
      · exact notPrepared (child_prepared n which)
    · exact legacy.elim (fun h => (no_legacy _).1 h.1) (fun h => (no_legacy _).2 h.1)
  · intro key children given
    have original := given
    obtain ⟨_,d,visible,check,identity,role,bounds,located,ready,_⟩ := given
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl
    · contradiction
    · have equal : key = 7 := identity.symm
      subst key
      exact ⟨rfl,survivor_children_functional registry registry_checked current (child n) 7 children []
        original (child_survivor n which)⟩

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


theorem supported_parent_selected : GeneralNominalSupportBoundary.Local registry finish displayRoot
    (.selected 1 [child 10,child 11]) :=
  GeneralNominalSupportBoundary.selected_supported parent_selected [] (guard displayRoot 0 (fun _ => rfl))

theorem supported_child_selected (n : Nat) (which : n = 10 ∨ n = 11) :
    GeneralNominalSupportBoundary.Local registry finish (child n) (.selected 7 []) :=
  GeneralNominalSupportBoundary.selected_supported (child_selected n which) [] (guard (child n) 1 (fun _ => rfl))

theorem classified : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
    registry finish displayRoot (.selected GeneralDictionaryOutputMergeRootEvidence.rootPayload) := by
  have parent := (GeneralNominalSupportBoundary.local_correspondence registry finish displayRoot _).mpr supported_parent_selected
  have first := (GeneralNominalSupportBoundary.local_correspondence registry finish (child 10) _).mpr
    (supported_child_selected 10 (Or.inl rfl))
  have last := (GeneralNominalSupportBoundary.local_correspondence registry finish (child 11) _).mpr
    (supported_child_selected 11 (Or.inr rfl))
  cases parent with
  | selected safe unique =>
    apply B4TargetV3.Classify.selected safe unique
    cases first with
    | selected firstSafe firstUnique =>
      cases last with
      | selected lastSafe lastUnique =>
        exact .cons (.selected firstSafe firstUnique .nil) (.cons (.selected lastSafe lastUnique .nil) .nil)

/-- Actual classification and universal source semantics agree on this one
inhabited reachable fixture. This theorem does not include Stable. -/
theorem reachable_classified_full_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish displayRoot
      (.selected GeneralDictionaryOutputMergeRootEvidence.rootPayload) ∧
    ∀ m, Models finish.current m →
      GeneralDictionaryRecursiveEvidence.Evidence registry current m displayRoot
        GeneralDictionaryOutputMergeRootEvidence.rootPayload :=
  ⟨reachable,finish_model,classified,GeneralDictionaryOutputMergeAllModels.full_dictionary⟩

end Yulang.GeneralDictionaryOutputMergeClassification
