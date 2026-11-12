import Yulang.GeneralDictionaryEarlyMergeScalarExample
import Yulang.GeneralDictionaryScalarLeaf

/-! Lossless diagnostics at the actual merged snapshot; no stability claim. -/
namespace Yulang.GeneralDictionaryEarlyMergeScalarClassification
open GeneralDictionaryEarlyMergeScalarExample
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (context state model state_models listDescriptor displayRoot interpretation intDisplay int_display_checked)
noncomputable abbrev current := finish.current.context

theorem parent_instance : GeneralDictionaryRecursiveEvidence.Instance registry current model displayRoot 1 children := by
  have old := GeneralDictionaryRecursiveEvidence.survivor_instance_of_branch registry registry_checked (context true)
    model displayRoot 1 children survivor declaration (by simp) checked rfl [(0,0)] rfl
    (branch model (state_models true))
  exact GeneralDictionaryOrdinaryTrace.instance_extension registry (context true) current
    (GeneralDictionaryOrdinaryTrace.extension_trans (GeneralDictionaryOrdinaryTrace.packet_extension packet)
      (GeneralDictionaryOrdinaryTrace.merge_extension before.current (site 10) (site 11)))
    model finish_model.1 displayRoot 1 children old

private theorem metadata : Metadata registry current := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,catalogue,_⟩ := parent_instance
  exact catalogue

private theorem leaf_ready (n : Nat) : ¬ GeneralNominalState.RootPending current.state (child n).demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩

private theorem sources_shape (source : Nat) (member : source ∈ GeneralNominalState.sources current.state) :
    source = 0 ∨ source = 1 ∨ source ∈ GeneralNominalAllocation.reserved (state true) registry displayRoot.identity := by
  simp only [GeneralNominalState.sources] at member
  change source ∈ (([0,1] ++ [0,1]) ++ GeneralNominalAllocation.reserved (state true) registry displayRoot.identity ++ []) ++ _ at member
  rcases List.mem_append.mp member with before | ordinary
  · simp only [List.append_nil] at before
    rcases List.mem_append.mp before with base | allocated
    · simp at base; rcases base with h | h | h | h <;> simp [h]
    · exact Or.inr (Or.inr allocated)
  · have shape : current.state.ordinary.flatMap GeneralNominalState.atomSources = [1,1,0,0,0,0,1,1] := by decide +kernel
    rw [shape] at ordinary
    simp at ordinary
    rcases ordinary with h | h | h <;> simp [h]

private theorem fresh (root : Nat) : GeneralNominalAllocation.Fresh current.state registry root := by
  intro key member collision
  rcases sources_shape _ collision with zero | one | allocated
  · have above := GeneralNominalIdentities.source_above_seed (state true).seed key
    change GeneralNominalIdentities.source (state true).seed key = 0 at zero
    omega
  · have above := GeneralNominalIdentities.source_above_seed (state true).seed key
    change GeneralNominalIdentities.source (state true).seed key = 1 at one
    have seed : (state true).seed = 1 := rfl
    omega
  · obtain ⟨old,owned,equal⟩ := List.mem_map.mp allocated
    have same := (GeneralNominalIdentities.source_identity (state true).seed old key).mp equal
    subst old
    exact List.mem_append_right _ owned

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



noncomputable def shape (n : Nat) : GeneralDictionaryScalarLeaf.ScalarLeafShape current (child n) intDisplay where
  terminal := rfl
  outputs := rfl
  role := rfl
  slot := ⟨1,by decide +kernel⟩
  base := .int
  noNominal := rfl
  head := rfl
  inputs := rfl
  query := by
    simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
      GeneralDeclarationPatterns.normalize]
    change GeneralNominalInspection.translate GeneralDeclarationExamples.constructors interpretation (.app 2 []) = .scalar .int
    simp [GeneralNominalInspection.translate,interpretation]
  located := rfl

private theorem linked (n : Nat) : GeneralNominalState.Linked current.state (child n).demand := by
  constructor
  · intro index
    have member : 1 ∈ GeneralNominalState.sources current.state :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
        (List.mem_ofFn.mpr ⟨(1 : Fin 2),rfl⟩))))
    exact ⟨member,member⟩
  · intro output member; cases member

private theorem leaf_prepared (n : Nat) : Prepared registry current (child n) intDisplay int_display_checked := by
  refine ⟨metadata,linked n,fresh _,[((1 : Fin 2),(1 : Fin 2))],rfl,?_,?_,model,?_⟩
  · change Finished (report current intDisplay [((shape n).slot,(shape n).slot)])
    rw [GeneralDictionaryScalarLeaf.report_exact current (child n) intDisplay (shape n)]
    exact ⟨rfl,rfl,rfl⟩
  · exact GeneralDictionaryScalarLeaf.ready current registry (child n) intDisplay int_display_checked (shape n)
  · exact GeneralDictionaryScalarLeaf.branch_models current registry (child n) intDisplay int_display_checked (shape n) model finish_model.1

private theorem leaf_survivor (n : Nat) : Survivor registry current (child n) 3 [] := by
  refine ⟨leaf_ready n,intDisplay,by simp,int_display_checked,rfl,rfl,[((1 : Fin 2),(1 : Fin 2))],rfl,leaf_prepared n,?_⟩
  exact (GeneralDictionaryLinearLeaf.children_empty current registry (child n) intDisplay int_display_checked rfl _).symm

private theorem child_failed (n : Nat) : Failed registry current (child n) declaration checked := by
  refine ⟨metadata,fresh _,[((1 : Fin 2),(1 : Fin 2))],rfl,?_,?_,Or.inl ?_⟩ <;> decide +kernel

theorem child_selected (n : Nat) : GeneralNominalFeedbackK2.Local registry finish.current (child n) (.selected 3 []) := by
  refine .selected ⟨leaf_ready n,no_root _,no_candidate _,?_⟩ ⟨leaf_survivor n,?_⟩
  · rintro (⟨_,decl,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl
      · exact notFailed (child_failed n)
      · exact notPrepared (leaf_prepared n)
    · exact legacy.elim (fun h => (no_legacy _).1 h.1) (fun h => (no_legacy _).2 h.1)
  · intro key cs given
    have original := given
    obtain ⟨_,decl,visible,check,identity,role,bounds,located,ready,_⟩ := given
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl
    · exact False.elim (GeneralNominalLocalBoundary.recursive_failed_not_prepared registry current (child n) declaration check (child_failed n) ready)
    · have equal : key = 3 := identity.symm; subst key
      exact ⟨rfl,survivor_children_functional registry registry_checked current (child n) 3 cs [] original (leaf_survivor n)⟩

theorem supported_child (n : Nat) : GeneralNominalSupportBoundary.Local registry finish (child n) (.selected 3 []) :=
  GeneralNominalSupportBoundary.selected_supported (child_selected n) [] (guard (child n) 1 (fun _ => rfl))
end GeneralDictionaryEarlyMergeScalarClassification
