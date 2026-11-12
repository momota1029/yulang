import Yulang.GeneralDictionarySupportRecursiveExample

/-! Concrete current-context classification of the actual recursive support
installation. This does not claim general termination or stable V5 execution. -/
namespace Yulang.GeneralDictionarySupportRecursiveClassification
open GeneralDictionarySupportRecursiveExample
open GeneralNominalExamples
open GeneralDeclarationExamples (roles display wrap display_checked)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection

noncomputable abbrev current := finish.current.context

private theorem metadata : Metadata registry current := by
  obtain ⟨m,valid⟩ := final_inhabited
  obtain ⟨_,_,_,_,_,_,_,_,_,_,catalogue,_⟩ := parent_instance m valid
  exact catalogue

private theorem linked (root : Occurrence roles) (slot : Fin 2)
    (args : ∀ index, root.demand.arguments index = (slot.val,slot.val))
    (outputs : root.demand.outputs = []) : GeneralNominalState.Linked current.state root.demand := by
  constructor
  · intro index
    rw [args index]
    have member : slot.val ∈ GeneralNominalState.sources current.state :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨slot,rfl⟩)))
    exact ⟨member,member⟩
  · intro output member; rw [outputs] at member; cases member

private theorem root_ready : ¬ GeneralNominalState.RootPending current.state displayRoot.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(0 : Fin 2),rfl,Or.inr ⟨listDescriptor,rfl⟩⟩
private theorem leaf_ready : ¬ GeneralNominalState.RootPending current.state displayChild.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(1 : Fin 2),rfl,Or.inl (by decide +kernel)⟩

private theorem root_fresh : GeneralNominalAllocation.Fresh current.state registry displayRoot.identity := by
  intro key member _
  exact List.mem_append_right _ member

private theorem sources_shape (source : Nat) (member : source ∈ GeneralNominalState.sources current.state) :
    source = 0 ∨ source = 1 ∨ source ∈ GeneralNominalAllocation.reserved (state true) registry displayRoot.identity := by
  simp only [GeneralNominalState.sources] at member
  change source ∈ (([0,1] ++ [0,1]) ++ GeneralNominalAllocation.reserved (state true) registry displayRoot.identity) ++ _ at member
  rcases List.mem_append.mp member with before | ordinary
  · rcases List.mem_append.mp before with base | allocated
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

private theorem parent_prepared : Prepared registry current displayRoot display display_checked := by
  obtain ⟨m,valid⟩ := final_inhabited
  obtain ⟨decl,visible,checked,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ := parent_instance m valid
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · contradiction
  · exact ⟨catalogue,linked displayRoot 0 (fun _ => rfl) rfl,root_fresh,bounds,located,finished,requested,m,branch⟩
  · contradiction

private theorem leaf_prepared : Prepared registry current displayChild intDisplay int_display_checked := by
  obtain ⟨m,valid⟩ := final_inhabited
  have old := ((GeneralNominalFeedbackSites.install_models start.current packet
    (GeneralNominalFeedbackSites.emitted packet) rfl m).mp valid).1.1
  have rule := GeneralDictionaryOrdinaryTrace.instance_extension registry (context true)
    current (GeneralDictionaryOrdinaryTrace.packet_extension packet) m valid.1
    displayChild 3 [] (leaf_instance m old)
  obtain ⟨decl,visible,checked,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ := rule
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · exact ⟨catalogue,linked displayChild 1 (fun _ => rfl) rfl,fresh _,bounds,located,finished,requested,m,branch⟩
  · contradiction
  · contradiction


private theorem display_query (ctx : Context)
    (catalogue : ctx.state.constructors = GeneralDeclarationExamples.constructors)
    (meaning : ctx.interpretation = interpretation) :
    GeneralNominalInspection.queries ctx.state ctx.interpretation display = [.nominal 0 [.variables [0]]] := by
  simp [GeneralNominalInspection.queries,Declaration.normalHead,GeneralDeclarationPatterns.normalizeArgs,
    GeneralDeclarationPatterns.normalize,GeneralNominalInspection.translate,catalogue,meaning,interpretation]

/-- The concrete installation adds only consequences of its source context. -/
theorem models_of_source (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models (state true) m) : Models finish.current m := by
  apply (GeneralNominalFeedbackSites.install_models start.current packet
    (GeneralNominalFeedbackSites.emitted packet) rfl m).mpr
  refine ⟨(initial_models ..).mpr valid,?_⟩
  have branch := GeneralNominalUnaryCaptureFacts.private_models (context true) registry displayRoot display
    0 listDescriptor rfl 0 rfl (1,1) rfl (display_query _ rfl rfl) m valid
  refine ⟨branch.1,branch.2,?_⟩
  change GeneralNominalMaterialization.Models (context true).state display _ _ (generated registry (context true) displayRoot display display_checked [(0,0)]) m
  rw [GeneralNominalRecursiveExamples.display_schema registry (context true) displayRoot rfl display_checked [(0,0)]]
  exact GeneralNominalMaterialization.empty_models ..

/-- A concrete separating model, not merely a vacuous universal model claim. -/
theorem current_model : Models finish.current model := models_of_source model (state_models true)

private def height (source : Nat) : Nat := if source = 0 then 1 else 0
private theorem model_height (source : Nat) : (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle finish.current source :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model current_model height model_height
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) source

private theorem raw_acyclic (slot : Fin current.state.base.slots) : ¬ GeneralNominalCycleK2.Cycle current.state slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge current.state first last →
      height last.val < height first.val := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model current_model.1
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

private theorem parent_survivor : Survivor registry current displayRoot 1 [displayChild] := by
  obtain ⟨decl,visible,checked,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ := parent_instance model current_model
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl | rfl
  · contradiction
  · exact ⟨root_ready,display,by simp,display_checked,rfl,rfl,bounds,located,parent_prepared,emitted⟩
  · contradiction
private theorem leaf_survivor : Survivor registry current displayChild 3 [] := by
  refine ⟨leaf_ready,intDisplay,by simp,int_display_checked,rfl,rfl,[((1 : Fin 2),(1 : Fin 2))],?_,leaf_prepared,?_⟩
  · decide +kernel
  · decide +kernel

private theorem wrong_parent_failed : Failed registry current displayRoot intDisplay int_display_checked := by
  refine ⟨metadata,root_fresh,[((0 : Fin 2),(0 : Fin 2))],?_,?_,?_,Or.inl ?_⟩ <;> decide +kernel
private theorem wrong_leaf_failed : Failed registry current displayChild display display_checked := by
  refine ⟨metadata,fresh _,[((1 : Fin 2),(1 : Fin 2))],?_,?_,?_,Or.inl ?_⟩ <;> decide +kernel

theorem parent_selected : GeneralNominalFeedbackK2.Local registry finish.current displayRoot (.selected 1 [displayChild]) := by
  refine .selected ⟨root_ready,no_root _,no_candidate _,?_⟩ ⟨parent_survivor,?_⟩
  · rintro (⟨_,decl,visible,checked,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl | rfl
      · exact notFailed wrong_parent_failed
      · exact notPrepared parent_prepared
      · contradiction
    · exact legacy.elim (fun h => (no_legacy _).1 h.1) (fun h => (no_legacy _).2 h.1)
  · intro key children given
    have original := given
    obtain ⟨_,decl,visible,checked,identity,role,bounds,located,ready,_⟩ := given
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl | rfl
    · exact False.elim (GeneralNominalLocalBoundary.recursive_failed_not_prepared registry current displayRoot intDisplay checked wrong_parent_failed ready)
    · have equal : key = 1 := identity.symm
      subst key
      exact ⟨rfl,survivor_children_functional registry registry_checked current displayRoot 1 children [displayChild] original parent_survivor⟩
    · contradiction

theorem leaf_selected : GeneralNominalFeedbackK2.Local registry finish.current displayChild (.selected 3 []) := by
  refine .selected ⟨leaf_ready,no_root _,no_candidate _,?_⟩ ⟨leaf_survivor,?_⟩
  · rintro (⟨_,decl,visible,checked,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
      rcases visible with rfl | rfl | rfl
      · exact notPrepared leaf_prepared
      · exact notFailed wrong_leaf_failed
      · contradiction
    · exact legacy.elim (fun h => (no_legacy _).1 h.1) (fun h => (no_legacy _).2 h.1)
  · intro key children given
    have original := given
    obtain ⟨_,decl,visible,checked,identity,role,bounds,located,ready,_⟩ := given
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl | rfl
    · have equal : key = 3 := identity.symm
      subst key
      exact ⟨rfl,survivor_children_functional registry registry_checked current displayChild 3 children [] original leaf_survivor⟩
    · exact False.elim (GeneralNominalLocalBoundary.recursive_failed_not_prepared registry current displayChild display checked wrong_leaf_failed ready)
    · contradiction


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

theorem supported_parent_selected : GeneralNominalSupportBoundary.Local registry finish displayRoot (.selected 1 [displayChild]) :=
  GeneralNominalSupportBoundary.selected_supported parent_selected [] (guard displayRoot 0 (fun _ => rfl))

theorem supported_leaf_selected : GeneralNominalSupportBoundary.Local registry finish displayChild (.selected 3 []) :=
  GeneralNominalSupportBoundary.selected_supported leaf_selected [] (guard displayChild 1 (fun _ => rfl))

/-- Actual current local classification, not just a stored packet or semantic
instance; all nodes use the same unchanged source-supported V5 boundary. -/
theorem classified : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
    registry finish displayRoot (.selected (.node 1 [.node 3 []])) := by
  have parent := (GeneralNominalSupportBoundary.local_correspondence registry finish displayRoot _).mpr supported_parent_selected
  have leaf := (GeneralNominalSupportBoundary.local_correspondence registry finish displayChild _).mpr supported_leaf_selected
  cases parent with
  | selected safe unique =>
    apply B4TargetV3.Classify.selected safe unique
    cases leaf with
    | selected leafSafe leafUnique => exact .cons (.selected leafSafe leafUnique .nil) .nil

/-- The concrete reachable final journal is inhabited and classifies the same
recursive payload whose source semantics hold in every final journal model.
Stability is deliberately not asserted. -/
theorem reachable_classified_dictionary :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot (.selected (.node 1 [.node 3 []])) ∧
    ∀ m, Models finish.current m → GeneralDictionaryRecursiveEvidence.Evidence registry current m displayRoot (.node 1 [.node 3 []]) :=
  ⟨actual_reachable,current_model,classified,final_recursive_evidence⟩

end Yulang.GeneralDictionarySupportRecursiveClassification
