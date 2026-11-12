import Yulang.GeneralDictionaryEarlyMergeExample

/-! Lossless diagnostics at the actual merged snapshot; no stability claim. -/
namespace Yulang.GeneralDictionaryEarlyMergeDiagnostics
open GeneralDictionaryEarlyMergeExample
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDeclarationExamples (roles)
open GeneralNominalExamples (context state model state_models listDescriptor displayRoot interpretation)
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

private theorem linked : GeneralNominalState.Linked current.state displayRoot.demand := by
  constructor
  · intro index
    have member : 0 ∈ GeneralNominalState.sources current.state :=
      List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(0 : Fin 2),rfl⟩)))
    exact ⟨member,member⟩
  · intro output member; cases member

private theorem root_ready : ¬ GeneralNominalState.RootPending current.state displayRoot.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(0 : Fin 2),rfl,Or.inr ⟨listDescriptor,rfl⟩⟩
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

private theorem parent_prepared : Prepared registry current displayRoot declaration checked := by
  obtain ⟨decl,visible,check,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ := parent_instance
  have eq := List.mem_singleton.mp visible; subst decl
  exact ⟨catalogue,linked,fresh _,bounds,located,finished,requested,model,branch⟩
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


private theorem parent_survivor : Survivor registry current displayRoot 1 children := by
  obtain ⟨decl,visible,check,key,role,bounds,located,finished,requested,emitted,catalogue,branch⟩ := parent_instance
  have eq := List.mem_singleton.mp visible; subst decl
  exact ⟨root_ready,declaration,by simp,checked,rfl,rfl,bounds,located,parent_prepared,emitted⟩

private theorem child_failed (n : Nat) : Failed registry current (child n) declaration checked := by
  refine ⟨metadata,fresh _,[((1 : Fin 2),(1 : Fin 2))],rfl,?_,?_,Or.inl ?_⟩ <;> decide +kernel

theorem parent_selected : GeneralNominalFeedbackK2.Local registry finish.current displayRoot (.selected 1 children) := by
  refine .selected ⟨root_ready,no_root _,no_candidate _,?_⟩ ⟨parent_survivor,?_⟩
  · rintro (⟨_,decl,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · have eq := List.mem_singleton.mp visible; subst decl; exact notPrepared parent_prepared
    · exact legacy.elim (fun h => (no_legacy _).1 h.1) (fun h => (no_legacy _).2 h.1)
  · intro key cs given
    have original := given
    obtain ⟨_,decl,visible,check,identity,_⟩ := given
    have eq := List.mem_singleton.mp visible; subst decl
    have equal : key = 1 := identity.symm; subst key
    exact ⟨rfl,survivor_children_functional registry registry_checked current displayRoot 1 cs children original parent_survivor⟩

theorem child_rejected (n : Nat) : GeneralNominalFeedbackK2.Local registry finish.current (child n) .rejected := by
  refine .rejected ⟨leaf_ready n,Or.inr (Or.inr ⟨?_,?_⟩)⟩
  · rintro (⟨_,decl,visible,check,role,notFailed,notPrepared⟩ | ⟨_,legacy⟩)
    · have eq := List.mem_singleton.mp visible; subst decl; exact notFailed (child_failed n)
    · exact legacy.elim (fun h => (no_legacy _).1 h.1) (fun h => (no_legacy _).2 h.1)
  · intro key cs given
    obtain ⟨_,decl,visible,check,identity,role,bounds,located,prepared,_⟩ := given
    have eq := List.mem_singleton.mp visible; subst decl
    exact GeneralNominalLocalBoundary.recursive_failed_not_prepared registry current (child n) declaration check (child_failed n) prepared
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


theorem supported_parent : GeneralNominalSupportBoundary.Local registry finish displayRoot (.selected 1 children) :=
  GeneralNominalSupportBoundary.selected_supported parent_selected [] (guard displayRoot 0 (fun _ => rfl))

theorem supported_child (n : Nat) : GeneralNominalSupportBoundary.Local registry finish (child n) .rejected := by
  cases child_rejected n with
  | rejected reason =>
    refine .rejected ⟨reason.1,?_⟩
    rcases reason.2 with root | candidate | ⟨notPending,noSurvivor⟩
    · exact Or.inl root
    · exact Or.inr (Or.inl candidate)
    · refine Or.inr (Or.inr ⟨?_,noSurvivor⟩)
      rintro (old | pending)
      · exact notPending old
      · exact pending ⟨[],guard (child n) 1 (fun _ => rfl)⟩

open CommonRoleOutermostResolver

theorem diagnostic : Resolves
    (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish)
    displayRoot (.selected 1 [.rejected,.rejected]) := by
  have parent := (GeneralNominalSupportBoundary.local_correspondence registry finish displayRoot _).mpr supported_parent
  rw [children_exact] at parent
  exact .selected parent (.cons (.rejected ((GeneralNominalSupportBoundary.local_correspondence registry finish (child 10) _).mpr (supported_child 10)))
    (.cons (.rejected ((GeneralNominalSupportBoundary.local_correspondence registry finish (child 11) _).mpr (supported_child 11))) .nil))

private theorem selected_local {v : B4Target.Vocabulary} (b : B4Target.SourceBoundary v)
    (r : v.Registry) (s : v.State) (d : v.Demand) (dictionary : Dictionary)
    (given : B4TargetV3.Classify b r s d (.selected dictionary)) :
    ∃ key children, B4TargetV3.Local b r s d (.selected key children) := by
  cases given with
  | selected safe unique all => exact ⟨_,_,.selected safe unique⟩

private theorem classify_cases {v : B4Target.Vocabulary} (b : B4Target.SourceBoundary v)
    (r : v.Registry) (s : v.State) (d : v.Demand) (outcome : Result)
    (given : B4TargetV3.Classify b r s d outcome) :
    B4TargetV3.Local b r s d .pending ∨ B4TargetV3.Local b r s d .rejected ∨
      B4TargetV3.Local b r s d .ambiguous ∨ ∃ key children dictionaries,
      B4TargetV3.Local b r s d (.selected key children) ∧
      All₂ (fun child dictionary => B4TargetV3.Classify b r s child (.selected dictionary)) children dictionaries := by
  cases given with
  | pending p => exact Or.inl (.pending p)
  | inspectionPending ready p root candidate => exact Or.inl (.inspectionPending ready p root candidate)
  | rejected reason => exact Or.inr (Or.inl (.rejected reason))
  | ambiguous safe one two distinct => exact Or.inr (Or.inr (Or.inl (.ambiguous safe one two distinct)))
  | selected safe unique all => exact Or.inr (Or.inr (Or.inr ⟨_,_,_,.selected safe unique,all⟩))

theorem child_no_dictionary (n : Nat) (dictionary : Dictionary) :
    ¬ B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish
      (child n) (.selected dictionary) := by
  intro classified
  obtain ⟨key,children,rule⟩ := selected_local (v := GeneralNominalSupportBoundary.vocabulary roles) (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish (child n) dictionary classified
  have localRule := (GeneralNominalSupportBoundary.local_correspondence registry finish (child n) _).mp rule
  have impossible := GeneralNominalLocalBoundary.local_functional (supported_child n) localRule
  cases impossible

/-- No four-way result may collapse the selected parent's failed where leaves
into a parent rejection. The complete diagnostic tree remains available. -/
theorem root_no_classify (outcome : Result) :
    ¬ B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish displayRoot outcome := by
  intro classified
  rcases classify_cases (v := GeneralNominalSupportBoundary.vocabulary roles) (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish displayRoot outcome classified with pending | rejected | ambiguous | ⟨key,cs,ds,rule,all⟩
  · have localRule := (GeneralNominalSupportBoundary.local_correspondence registry finish displayRoot _).mp pending
    have impossible := GeneralNominalLocalBoundary.local_functional supported_parent localRule
    cases impossible
  · have localRule := (GeneralNominalSupportBoundary.local_correspondence registry finish displayRoot _).mp rejected
    have impossible := GeneralNominalLocalBoundary.local_functional supported_parent localRule
    cases impossible
  · have localRule := (GeneralNominalSupportBoundary.local_correspondence registry finish displayRoot _).mp ambiguous
    have impossible := GeneralNominalLocalBoundary.local_functional supported_parent localRule
    cases impossible
  · have localRule := (GeneralNominalSupportBoundary.local_correspondence registry finish displayRoot _).mp rule
    have same := GeneralNominalLocalBoundary.local_functional supported_parent localRule
    have lists : children = cs := by cases same; rfl
    rw [← lists,children_exact] at all
    cases all with
    | cons first rest => exact child_no_dictionary 10 _ first

theorem reachable_diagnostic :
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot finish ∧
    Models finish.current model ∧ finish.current.packets ≠ [] ∧ finish.current.aliases ≠ [] ∧
    Resolves (B4TargetV3.Local (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry finish)
      displayRoot (.selected 1 [.rejected,.rejected]) ∧
    ∀ outcome, ¬ B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
      registry finish displayRoot outcome :=
  ⟨reachable,finish_model,actual_early_merge.2.2.1,actual_early_merge.2.2.2,diagnostic,root_no_classify⟩

end Yulang.GeneralDictionaryEarlyMergeDiagnostics
