import Yulang.GeneralDictionaryOutputMergeRefreshEvidence

/-! Actual support classification survives the four-slot exact refresh.
This is the next reachable state, not a readback-only or model-only surrogate.
No stability or global V5 completeness theorem is asserted. -/
namespace Yulang.GeneralDictionaryOutputMergeRefreshClassification
open GeneralDictionaryOutputMergeSuccess
open GeneralDictionaryOutputMergeJointModels
open GeneralNominalExamples (context state model displayRoot listDescriptor)
open GeneralDeclarationExamples (roles constructors)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryOutputMergeAllModels
open GeneralDictionaryOutputMergeRefresh
open GeneralDictionaryOutputMergeRefreshEvidence

noncomputable abbrev nextContext := refreshedContext

private theorem prepared_from_old {root : Occurrence roles} {d : Declaration}
    {checked : DeclarationChecked registry.constructors roles d} {key : Nat} {children : List (Occurrence roles)}
    (old : Prepared registry GeneralDictionaryOutputMergeFeedback.next.current.context root d checked)
    (rule : GeneralDictionaryRecursiveEvidence.Instance registry nextContext model root key children)
    (dvisible : d ∈ registry.declarations) (identity : d.id = key) : Prepared registry nextContext root d checked := by
  obtain ⟨metadata,linked,fresh,_⟩ := old
  obtain ⟨decl,visible,check,keyeq,role,bounds,located,finished,ready,emitted,metadataNew,branch⟩ := rule
  have same : decl = d := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible dvisible
    rcases visible with rfl | rfl <;> rcases dvisible with rfl | rfl
    · rfl
    · have impossible : (1 : Nat) = 7 := keyeq.trans identity.symm; contradiction
    · have impossible : (7 : Nat) = 1 := keyeq.trans identity.symm; contradiction
    · rfl
  subst decl
  refine ⟨metadataNew,?_,?_,bounds,located,finished,ready,model,branch⟩
  · constructor
    · intro i
      exact ⟨(sources_exact _).mpr (linked.1 i).1,(sources_exact _).mpr (linked.1 i).2⟩
    · intro output member
      exact (sources_exact _).mpr (linked.2 output member)
  · intro origin member collision
    exact fresh origin member ((sources_exact _).mp collision)

private theorem root_ready : ¬ GeneralNominalState.RootPending nextContext.state displayRoot.demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(0 : Fin 4),rfl,Or.inr ⟨descriptor,rfl⟩⟩

private theorem child_ready (n : Nat) : ¬ GeneralNominalState.RootPending nextContext.state (child n).demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(1 : Fin 4),rfl,Or.inl (by decide +kernel)⟩

private def height (source : Nat) : Nat := if source = 0 then 1 else 0
private theorem model_height (source : Nat) : (model source).1 = GeneralNominalOutputGrowth.tower (height source) := by
  by_cases zero : source = 0 <;> simp [height,zero,GeneralNominalOutputGrowth.tower] <;> rfl

theorem acyclic (source : Nat) : ¬ GeneralNominalFeedbackK2.Cycle refreshed.current source :=
  GeneralNominalOutputGrowthModels.feedback_acyclic _ model inhabited height model_height
    (by rintro _ _ ⟨_,_,⟨kind,_,_,_⟩,_,_⟩; exact Fin.elim0 kind) source

private theorem raw_acyclic (slot : Fin nextContext.state.base.slots) : ¬ GeneralNominalCycleK2.Cycle nextContext.state slot := by
  have decreasing : ∀ first last, GeneralNominalMixedRecurrence.Edge nextContext.state first last →
      height (nextContext.state.base.source last) < height (nextContext.state.base.source first) := by
    intro first last edge
    rcases edge with ⟨kind,_,_,_⟩ | argument
    · exact Fin.elim0 kind
    · obtain ⟨descriptor,recorded,index,actual,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument model inhabited.1
      exact GeneralNominalOutputGrowthModels.observation_decreases model height model_height _ _ _ _ actual seen same
  have paths : ∀ first last, GeneralNominalMixedRecurrence.Path nextContext.state first last → height (nextContext.state.base.source last) ≤ height (nextContext.state.base.source first) := by
    intro first last path
    induction path with
    | nil => exact Nat.le_refl _
    | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decreasing _ _ edge))
  rintro ⟨next,edge,path⟩
  have smaller := decreasing _ _ edge
  have larger := paths _ _ path
  omega

private theorem no_raw_recurs (slot : Fin nextContext.state.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt nextContext.state slot := by
  rintro (⟨child,edge,path⟩ | ⟨cycle,_⟩)
  · exact raw_acyclic slot ⟨child,GeneralNominalCycleK2.direct_edge_sound edge,GeneralNominalCycleK2.direct_path_sound path⟩
  · exact raw_acyclic slot cycle

private theorem no_root (root : Occurrence roles) : ¬ GeneralNominalFeedbackK2.RootK2 refreshed.current root := by
  rintro (⟨_,_,_,slot,_,cycle⟩ | ⟨_,_,index,cycle,_⟩)
  · exact no_raw_recurs slot cycle
  · exact acyclic _ cycle
private theorem no_candidate (root : Occurrence roles) : ¬ GeneralNominalFeedbackK2.CandidateK2 registry refreshed.current root := by
  rintro (⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ | ⟨_,_,_,_,_,_,_,_,visited,_,cycle,_⟩)
  · exact no_raw_recurs visited.1 cycle
  · exact acyclic _ cycle

private theorem no_legacy (root : Occurrence roles) :
    ¬ (GeneralNominalLocalBoundary.recursiveFields roles).RootK2 registry nextContext root ∧
    ¬ (GeneralNominalLocalBoundary.recursiveFields roles).CandidateK2 registry nextContext root := by
  constructor
  · rintro ⟨_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩; exact Fin.elim0 kind
  · rintro ⟨_,_,_,_,_,_,_,_,_,_,⟨⟨kind,_,_⟩,_⟩⟩; exact Fin.elim0 kind


theorem parent_prepared : Prepared registry nextContext displayRoot declaration checked := by
  exact prepared_from_old GeneralDictionaryOutputMergeFeedbackClassification.parent_prepared
    (GeneralDictionaryOutputMergeRefreshEvidence.parent_instance model inhabited) (by simp) rfl

theorem child_prepared (n : Nat) (which : n = 10 ∨ n = 11) :
    Prepared registry nextContext (child n) terminal terminal_checked := by
  exact prepared_from_old (GeneralDictionaryOutputMergeFeedbackClassification.child_prepared n which)
    (GeneralDictionaryOutputMergeRefreshEvidence.terminal_instance model inhabited n which) (by simp) rfl

theorem parent_survivor : Survivor registry nextContext displayRoot 1 [child 10,child 11] := by
  obtain ⟨d,visible,check,key,role,bounds,located,finished,ready,emitted,metadata,branch⟩ :=
    GeneralDictionaryOutputMergeRefreshEvidence.parent_instance model inhabited
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · exact ⟨root_ready,declaration,by simp,check,key,role,bounds,located,parent_prepared,emitted⟩
  · contradiction

theorem child_survivor (n : Nat) (which : n = 10 ∨ n = 11) :
    Survivor registry nextContext (child n) 7 [] := by
  obtain ⟨d,visible,check,key,role,bounds,located,finished,ready,emitted,metadata,branch⟩ :=
    GeneralDictionaryOutputMergeRefreshEvidence.terminal_instance model inhabited n which
  simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
  rcases visible with rfl | rfl
  · contradiction
  · exact ⟨child_ready n,terminal,by simp,check,key,role,bounds,located,child_prepared n which,emitted⟩

theorem parent_selected : GeneralNominalFeedbackK2.Local registry refreshed.current displayRoot
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
      exact ⟨rfl,survivor_children_functional registry registry_checked nextContext displayRoot 1 children
        [child 10,child 11] original parent_survivor⟩
    · contradiction

theorem child_selected (n : Nat) (which : n = 10 ∨ n = 11) :
    GeneralNominalFeedbackK2.Local registry refreshed.current (child n) (.selected 7 []) := by
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
      exact ⟨rfl,survivor_children_functional registry registry_checked nextContext (child n) 7 children []
        original (child_survivor n which)⟩

private theorem ready_low (slot : Fin 4) (low : slot = 0 ∨ slot = 1) :
    GeneralNominalSupport.ReadyAt refreshed [] (snapshot.base.source slot) := by
  rcases low with rfl | rfl
  · exact GeneralNominalSupport.source_ready refreshed 0 _ _ _
      (GeneralNominalSupport.Head.nominal (snapshot := state true) (0 : Fin 2) listDescriptor rfl) (GeneralNominalSupport.Head.nominal (snapshot := snapshot) (0 : Fin 4) descriptor rfl) []
  · exact GeneralNominalSupport.source_ready refreshed 1 _ _ _
      (GeneralNominalSupport.Head.scalar (snapshot := state true) (1 : Fin 2) .int rfl) (GeneralNominalSupport.Head.scalar (snapshot := snapshot) (1 : Fin 4) .int rfl) []

private theorem parent_guard : GeneralNominalSupport.DecisionGuard refreshed registry displayRoot [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index; exact ready_low 0 (Or.inl rfl)
  · intro d visible role bounds located read member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl
    · have found : arguments nextContext displayRoot = some [((0 : Fin 4),0)] := by decide +kernel
      have same := Option.some.inj (located.symm.trans found)
      subst bounds
      apply ready_low read
      change read ∈ GeneralNominalSupport.readsMany snapshot
        (GeneralNominalInspection.queries snapshot refreshedContext.interpretation declaration) [((0 : Fin 4),0)] at member
      have shape : GeneralNominalSupport.readsMany snapshot
          (GeneralNominalInspection.queries snapshot refreshedContext.interpretation declaration) [((0 : Fin 4),0)] = [0] := by
        decide +kernel
      rw [shape] at member
      exact Or.inl (List.mem_singleton.mp member)
    · contradiction

private theorem child_guard (n : Nat) : GeneralNominalSupport.DecisionGuard refreshed registry (child n) [] := by
  refine ⟨(by intro _ impossible; cases impossible),?_,?_⟩
  · intro index; exact ready_low 1 (Or.inr rfl)
  · intro d visible role bounds located read member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at visible
    rcases visible with rfl | rfl
    · contradiction
    · have found : arguments nextContext (child n) = some [((1 : Fin 4),1)] := by
        change arguments nextContext (GeneralDictionaryJointMergeExample.root 0 0) = _
        decide +kernel
      have same := Option.some.inj (located.symm.trans found)
      subst bounds
      change read ∈ GeneralNominalSupport.readsMany snapshot
        (GeneralNominalInspection.queries snapshot refreshedContext.interpretation terminal) [((1 : Fin 4),1)] at member
      have shape : GeneralNominalSupport.readsMany snapshot
          (GeneralNominalInspection.queries snapshot refreshedContext.interpretation terminal) [((1 : Fin 4),1)] = [] := by
        decide +kernel
      rw [shape] at member
      cases member


theorem supported_parent_selected : GeneralNominalSupportBoundary.Local registry refreshed displayRoot
    (.selected 1 [child 10,child 11]) :=
  GeneralNominalSupportBoundary.selected_supported parent_selected [] parent_guard

theorem supported_child_selected (n : Nat) (which : n = 10 ∨ n = 11) :
    GeneralNominalSupportBoundary.Local registry refreshed (child n) (.selected 7 []) :=
  GeneralNominalSupportBoundary.selected_supported (child_selected n which) [] (child_guard n)

theorem classified : B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary
    registry refreshed displayRoot (.selected GeneralDictionaryOutputMergeRootEvidence.rootPayload) := by
  have parent := (GeneralNominalSupportBoundary.local_correspondence registry refreshed displayRoot _).mpr supported_parent_selected
  have first := (GeneralNominalSupportBoundary.local_correspondence registry refreshed (child 10) _).mpr
    (supported_child_selected 10 (Or.inl rfl))
  have last := (GeneralNominalSupportBoundary.local_correspondence registry refreshed (child 11) _).mpr
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
    B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot refreshed ∧
    Models refreshed.current model ∧
    B4TargetV3.Classify (GeneralNominalSupportBoundary.boundary roles).toSourceBoundary registry refreshed displayRoot
      (.selected GeneralDictionaryOutputMergeRootEvidence.rootPayload) ∧
    ∀ m, Models refreshed.current m →
      GeneralDictionaryRecursiveEvidence.Evidence registry nextContext m displayRoot
        GeneralDictionaryOutputMergeRootEvidence.rootPayload :=
  ⟨GeneralDictionaryOutputMergeRefresh.reachable,inhabited,classified,full_dictionary⟩

end Yulang.GeneralDictionaryOutputMergeRefreshClassification
