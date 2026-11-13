import Yulang.GeneralDictionaryObservedCompleteStable

namespace Yulang.GeneralDictionaryObservedCompleteClassification
open GeneralDictionaryObservedCompleteExample GeneralDictionaryObservedCompleteInstallation
open GeneralDictionaryObservedCompleteEvidence GeneralDictionaryObservedCompleteFinalEvidence
open GeneralDictionaryObservedCompleteClosure GeneralDictionaryObservedCompleteStable
open GeneralNominalExamples (model listDescriptor intDisplay int_display_checked)
open GeneralDeclarationExamples (roles)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

private theorem sources_shape (id : Nat) (member : id ∈ GeneralNominalState.sources current.state) :
    id = 0 ∨ id = 1 ∨ id ∈ GeneralNominalAllocation.reserved source registry root.identity := by
  simp only [GeneralNominalState.sources] at member
  change id ∈ (([0,1] ++ [0,1]) ++ GeneralNominalAllocation.reserved source registry root.identity) ++ _ at member
  rcases List.mem_append.mp member with before | ordinary
  · rcases List.mem_append.mp before with base | allocated
    · simp at base; rcases base with h | h | h | h <;> simp [h]
    · exact Or.inr (Or.inr allocated)
  · have shape : current.state.ordinary.flatMap GeneralNominalState.atomSources = [1,1,0,0,0,0,1,1] := by decide +kernel
    rw [shape] at ordinary
    simp at ordinary
    rcases ordinary with h | h | h <;> simp [h]

private theorem fresh (identity : Nat) : GeneralNominalAllocation.Fresh current.state registry identity := by
  intro key member collision
  rcases sources_shape _ collision with zero | one | allocated
  · have above := GeneralNominalIdentities.source_above_seed source.seed key
    change GeneralNominalIdentities.source source.seed key = 0 at zero
    omega
  · have above := GeneralNominalIdentities.source_above_seed source.seed key
    change GeneralNominalIdentities.source source.seed key = 1 at one
    have seed : source.seed = 1 := rfl
    omega
  · obtain ⟨old,owned,equal⟩ := List.mem_map.mp allocated
    have same := (GeneralNominalIdentities.source_identity source.seed old key).mp equal
    subst old
    exact List.mem_append_right _ owned

private def height (source : Nat) : Nat := if source = 0 then 1 else 0
private theorem model_height (source : Nat) : (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle installed.current source :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model (models_of_source model source_models) height model_height
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) source

private theorem raw_acyclic (slot : Fin current.state.base.slots) : ¬ GeneralNominalCycleK2.Cycle current.state slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge current.state first last →
      height last.val < height first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model (models_of_source model source_models).1
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

private theorem no_root (root : Occurrence roles) : ¬ GeneralNominalFeedbackK2.RootK2 installed.current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,index,cycle,_⟩)
  · exact no_raw_recurs slot cycle
  · exact acyclic _ cycle
private theorem no_candidate (root : Occurrence roles) : ¬ GeneralNominalFeedbackK2.CandidateK2 registry installed.current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw_recurs visited.1 cycle
  · exact acyclic _ cycle

private theorem no_legacy (root : Occurrence roles) :
    ¬ (GeneralNominalLocalBoundary.recursiveFields roles).RootK2 registry current root ∧
    ¬ (GeneralNominalLocalBoundary.recursiveFields roles).CandidateK2 registry current root := by
  constructor
  · rintro ⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩; exact Fin.elim0 kind
  · rintro ⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩; exact Fin.elim0 kind


private theorem linked_parent : GeneralNominalState.Linked current.state root.demand := by
  constructor
  · intro index
    have member : 0 ∈ GeneralNominalState.sources current.state :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(0 : Fin 2),rfl⟩)))
    exact ⟨member,member⟩
  · intro output member
    have same := List.mem_singleton.mp member
    subst output
    exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(1 : Fin 2),rfl⟩)))

private theorem child_args (index : Fin (roles child.demand.role).arity) :
    child.demand.arguments index = (1,1) := by decide +revert +kernel

private theorem linked_child : GeneralNominalState.Linked current.state child.demand := by
  constructor
  · intro index
    have member : 1 ∈ GeneralNominalState.sources current.state :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(1 : Fin 2),rfl⟩)))
    have args := child_args index
    rw [args]
    exact ⟨member,member⟩
  · intro output member; cases member

private theorem parent_ready : ¬ GeneralNominalState.RootPending current.state root.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(0 : Fin 2),rfl,Or.inr ⟨listDescriptor,rfl⟩⟩

private theorem child_ready : ¬ GeneralNominalState.RootPending current.state child.demand := by
  rintro ⟨index,unknown⟩
  have args := child_args index
  rw [args] at unknown
  exact unknown ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩

private theorem parent_prepared : Prepared registry current root declaration checked := by
  obtain ⟨decl,visible,check,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ := final_parent_instance model (models_of_source model source_models)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · exact ⟨catalogue,linked_parent,fresh _,bounds,located,finished,requested,model,branch⟩
  · contradiction

private theorem child_prepared : Prepared registry current child intDisplay int_display_checked := by
  obtain ⟨decl,visible,check,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ := final_child_instance model (models_of_source model source_models)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · contradiction
  · exact ⟨catalogue,linked_child,fresh _,bounds,located,finished,requested,model,branch⟩

private theorem parent_survivor : Survivor registry current root declaration.id children := by
  obtain ⟨decl,visible,check,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ := final_parent_instance model (models_of_source model source_models)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · exact ⟨parent_ready,declaration,by simp,checked,rfl,rfl,bounds,located,parent_prepared,emitted⟩
  · contradiction

private theorem child_survivor : Survivor registry current child intDisplay.id [] := by
  obtain ⟨decl,visible,check,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ := final_child_instance model (models_of_source model source_models)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · contradiction
  · exact ⟨child_ready,intDisplay,by simp,int_display_checked,rfl,rfl,bounds,located,child_prepared,emitted⟩

private theorem registry_checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro decl member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl
  · exact checked
  · exact int_display_checked

theorem parent_selected : GeneralNominalFeedbackK2.Local registry installed.current root (.selected declaration.id children) := by
  refine .selected ⟨parent_ready,no_root _,no_candidate _,?_⟩ ⟨parent_survivor,?_⟩
  · rintro (⟨_,decl,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl
      · exact notPrepared parent_prepared
      · cases role
    · exact legacy.elim (fun h => (no_legacy _).1 h.1) (fun h => (no_legacy _).2 h.1)
  · intro key kids original
    have preserve := original
    obtain ⟨_,decl,visible,check,identity,role,bounds,located,ready,emitted⟩ := original
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl
    · have found : arguments current root = some [((0 : Fin 2),(0 : Fin 2))] := rfl
      have equal := Option.some.inj (located.symm.trans found)
      subst bounds
      have equalKey : key = declaration.id := identity.symm
      subst key
      exact ⟨rfl,survivor_children_functional registry registry_checked current root declaration.id kids children preserve parent_survivor⟩
    · cases role

theorem child_selected : GeneralNominalFeedbackK2.Local registry installed.current child (.selected intDisplay.id []) := by
  refine .selected ⟨child_ready,no_root _,no_candidate _,?_⟩ ⟨child_survivor,?_⟩
  · rintro (⟨_,decl,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl
      · cases role
      · exact notPrepared child_prepared
    · exact legacy.elim (fun h => (no_legacy _).1 h.1) (fun h => (no_legacy _).2 h.1)
  · rintro key kids ⟨_,decl,visible,check,identity,role,bounds,located,ready,emitted⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl
    · cases role
    · exact ⟨identity.symm,emitted.trans (GeneralDictionaryLinearLeaf.children_empty current registry child intDisplay check rfl _)⟩

private theorem all_heads (slot : Fin 2) :
    ∃ test observation, GeneralNominalSupport.Head source (source.base.source slot) test observation ∧
      GeneralNominalSupport.Head current.state (current.state.base.source slot) test observation := by
  have bounded := slot.isLt
  by_cases zero : slot.val = 0
  · have same : slot = 0 := Fin.ext zero
    subst slot
    exact ⟨_,_,.nominal 0 listDescriptor rfl,GeneralNominalSupport.Head.nominal (snapshot := current.state) (0 : Fin 2) listDescriptor rfl⟩
  · have same : slot = (1 : Fin 2) := by apply Fin.ext; omega
    subst slot
    exact ⟨_,_,.scalar 1 .int rfl,GeneralNominalSupport.Head.scalar (snapshot := current.state) (1 : Fin 2) .int rfl⟩

private theorem guard (focus : Occurrence roles) (slot : Fin 2)
    (args : ∀ index, focus.demand.arguments index = (slot.val,slot.val)) :
    GeneralNominalSupport.DecisionGuard installed registry focus [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index
    rw [show (focus.demand.arguments index).1 = slot.val by rw [args index]]
    obtain ⟨test,observation,old,seen⟩ := all_heads slot
    exact GeneralNominalSupport.source_ready installed slot.val test observation observation old seen []
  · intro decl visible role bounds located read member
    obtain ⟨test,observation,old,seen⟩ := all_heads read
    exact GeneralNominalSupport.source_ready installed read.val test observation observation old seen []

theorem supported_parent : GeneralNominalSupportBoundary.Local registry installed root (.selected declaration.id children) :=
  GeneralNominalSupportBoundary.selected_supported parent_selected [] (guard root 0 (fun _ => rfl))

theorem supported_child : GeneralNominalSupportBoundary.Local registry installed child (.selected intDisplay.id []) :=
  GeneralNominalSupportBoundary.selected_supported child_selected [] (guard child 1 child_args)

theorem classified : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
    registry installed root (.selected payload) := by
  have parent := (GeneralNominalSupportBoundary.local_correspondence registry installed root _).mpr supported_parent
  rw [children_exact] at parent
  have leaf := (GeneralNominalSupportBoundary.local_correspondence registry installed child _).mpr supported_child
  cases parent with
  | selected safe unique =>
    apply B4TargetV3.Classify.selected safe unique
    cases leaf with
    | selected leafSafe leafUnique => exact .cons (.selected leafSafe leafUnique .nil) .nil

theorem stable_classified_named_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry root installed ∧
    Models installed.current model ∧ GeneralNominalSupportSteps.Stable registry installed root ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry installed root (.selected payload) ∧
    root.demand.outputs ≠ [] ∧ children.length = 1 ∧
    ∀ assignment, Models installed.current assignment → GeneralDictionaryRecursiveEvidence.Evidence registry current assignment root payload :=
  ⟨installed_reachable,models_of_source model source_models,stable,classified,named_request_present,actual_children_count,final_evidence⟩

end Yulang.GeneralDictionaryObservedCompleteClassification
