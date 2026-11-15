import Yulang.GeneralNominalCenteredHeadAllocV7MergeRegression

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalCenteredHeadAllocV7ParentBaseline
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters CommonNominalFullCarrier
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalCenteredHeadAllocMergeSource GeneralNominalCenteredHeadAllocMergeInstall
open GeneralNominalCenteredHeadAllocMergeState GeneralNominalCenteredHeadAllocMergeStable
open GeneralNominalCenteredHeadAllocMergedConflict
open GeneralNominalSaturationState (Alias)
abbrev current (atoms) := (stage atoms).core.erased.current.context

theorem parent_fresh : GeneralNominalAllocation.Fresh (current atoms).state registry root.identity := by
  intro key member _
  exact List.mem_append_right _ member

theorem parent_report : report (current atoms) declaration [((0 : Fin 1),(0 : Fin 1))] =
    { inspected := [((0 : Fin 1),(0 : Fin 1))], checked := [((0 : Fin 1),(0 : Fin 1)),((0 : Fin 1),(0 : Fin 1))] } :=
  by
    have queryCurrent : GeneralNominalInspection.queries (current atoms).state (current atoms).interpretation declaration = [.scalar .int] := by
      have constructors : (current atoms).state.constructors = snapshot.constructors := rfl
      have interpretation : (current atoms).interpretation = context.interpretation := rfl
      simpa only [GeneralNominalInspection.queries,constructors,interpretation] using query
    have nominal : (current atoms).state.nominals (0 : Fin 1) = none := rfl
    have head : (current atoms).state.view.heads (0 : Fin 1) = .scalar .int := rfl
    unfold report
    rw [queryCurrent]
    simp [inspectMany,inspect,Report.visit,Report.append,nominal,head]

theorem parent_head_model (good : Good atoms) :
    GeneralNominalCenteredHeadCandidates.HeadModels registry (current atoms) root declaration [((0 : Fin 1),(0 : Fin 1))] uniform := by
  constructor
  · unfold privateState
    rw [parent_report]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨raw_uniform good,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · exact PresenceNormalForm.all_nil _ _
    · simp [selfChecks,PresenceNormalForm.All]; exact subtype_refl _
  · rw [parent_report]; simp [ProjectionModels]

theorem parent_prepared (good : Good atoms) :
    GeneralNominalCenteredHeadCandidates.Prepared registry (current atoms) root declaration := by
  refine ⟨source.metadata,⟨?_,by intro output member; cases member⟩,parent_fresh,
    [((0 : Fin 1),(0 : Fin 1))],rfl,?_,uniform,parent_head_model good⟩
  · intro index
    change Fin 1 at index
    have zero : index = (0 : Fin 1) := Subsingleton.elim _ _
    subst index
    constructor <;> exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_ofFn.mpr ⟨(0 : Fin 1),rfl⟩)))
  · rw [parent_report]; exact ⟨rfl,rfl,rfl⟩

theorem parent_known : ¬ GeneralNominalState.RootPending (current atoms).state (GeneralNominalCenteredHeadCandidates.inputs root).demand := by
  rintro ⟨index,unknown⟩
  exact unknown ⟨(0 : Fin 1),rfl,Or.inl (by intro h; cases h)⟩

noncomputable abbrev childrenAt (atoms) := GeneralNominalAllocation.children (current atoms).state registry
  (GeneralNominalCenteredHeadCandidates.inputs root) declaration declaration_checked
  (bindings (current atoms).state (report (current atoms) declaration [((0 : Fin 1),(0 : Fin 1))]))

theorem parent_children : childrenAt atoms = children := by
  unfold childrenAt
  rw [parent_report]
  change GeneralNominalAllocation.children (current atoms).state registry root declaration declaration_checked [] = children
  change _ = GeneralNominalAllocation.children snapshot registry root declaration declaration_checked packet.bindings
  rw [bindings_empty]
  rfl

theorem parent_survivor (good : Good atoms) :
    GeneralNominalCenteredHeadCandidates.Survivor registry (current atoms) root 37 children :=
  ⟨parent_known,declaration,List.mem_cons_self,declaration_checked,rfl,rfl,[((0 : Fin 1),(0 : Fin 1))],rfl,
    parent_prepared good,parent_children.symm⟩

theorem parent_unique (good : Good atoms) :
    GeneralNominalCenteredHeadCandidates.Unique registry (current atoms) root 37 children := by
  refine ⟨parent_survivor good,?_⟩
  intro key kids found
  have copy := found
  obtain ⟨_,d,visible,_,identity,role,_⟩ := found
  cases parent_only visible role
  cases identity
  exact ⟨rfl,GeneralNominalCenteredHeadCandidates.survivor_children_functional checked copy (parent_survivor good)⟩

theorem parent_ready : GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady (stage atoms) root := by
  refine ⟨⟨plan.input,List.mem_cons_self,rfl⟩,?_⟩
  intro first one _ last two same
  exact merges_closed one two same

theorem parent_safe (good : Good atoms) :
    B4TargetV6.SafeKnown (GeneralNominalCenteredHeadAllocBoundary.boundary roles) sourceRegistry (stage atoms) root := by
  refine ⟨parent_known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old
      exact GeneralNominalCenteredHeadAllocMergeConflict.no_raw_recurs good slot cycle
    · exact empty_models good.2 cycle.2
    · exact empty_models good.2 cycle.2
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old
      exact GeneralNominalCenteredHeadAllocMergeConflict.no_raw_recurs good visited.1 cycle
    · exact empty_models good.2 cycle.2
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases parent_only visible role; exact unprepared (parent_prepared good)
    · exact unclosed parent_ready

theorem parent_old_selected (good : Good atoms) :
    GeneralNominalCenteredHeadAllocBoundary.Local sourceRegistry (stage atoms) root (.selected 37 children) :=
  .selected (parent_safe good) (parent_unique good) (fun conflict => empty_models good.2
    (by obtain ⟨model,valid,_⟩ := conflict.1; exact ⟨model,valid⟩))

theorem parent_isolated (path : Alias (stage atoms).core.erased.current one two) :
    one = root.identity ↔ two = root.identity := by
  induction path with
  | refl => exact Iff.rfl
  | edge member =>
    cases List.mem_singleton.mp member
    exact iff_of_false (Nat.ne_of_gt a_above_root) (Nat.ne_of_gt b_above_root)
  | symm _ ih => exact ih.symm
  | trans _ _ one two => exact one.trans two

theorem parent_not_merged : ¬ MergedClass (stage atoms) root := by
  rintro ⟨first,last,member,_,alias⟩
  cases List.mem_singleton.mp member
  exact (Nat.ne_of_gt a_above_root) ((parent_isolated alias).mp rfl)

theorem parent_selected (good : Good atoms) :
    GeneralNominalCenteredHeadAllocV7Boundary.Local sourceRegistry (stage atoms) root (.selected 37 children) :=
  .ordinary (fun conflict => parent_not_merged conflict.1) (parent_old_selected good)

theorem final_parent_selected :
    GeneralNominalCenteredHeadAllocV7Boundary.Local sourceRegistry final root (.selected 37 children) := by
  obtain ⟨atoms,good,_,same⟩ := final_shape
  rw [same]; exact parent_selected good

theorem not_headBaseline : ¬ GeneralNominalCenteredHeadAllocV7Completion.HeadBaseline roles := by
  intro baseline
  obtain ⟨model,valid,_⟩ := baseline sourceRegistry ⟨rfl,source_checked⟩ final root root 37 children final_reachable final_parent_selected
  exact GeneralNominalCenteredHeadAllocMergeConflict.final_empty ⟨model,valid⟩

theorem not_selectedCompletion : ¬ GeneralNominalCenteredHeadAllocV7Completion.SelectedCompletion roles := by
  intro completion
  obtain ⟨effect,_,_,_,_,_,_,model,valid,_⟩ :=
    completion sourceRegistry ⟨rfl,source_checked⟩ final root root 37 children final_reachable final_parent_selected
  exact GeneralNominalCenteredHeadAllocMergeConflict.final_empty ⟨model,valid⟩

theorem parent_packet_recorded : plan.packet ∈ final.core.erased.current.packets := by
  obtain ⟨atoms,_,_,same⟩ := final_shape
  rw [same]; exact List.mem_singleton_self _

theorem parent_children_recorded : ∀ child ∈ children, (root,child) ∈ final.core.erased.current.edges := by
  obtain ⟨atoms,_,_,same⟩ := final_shape
  rw [same]
  intro child member
  exact List.mem_map.mpr ⟨child,member,rfl⟩

/-- A selected ancestor keeps its already-generated children while a descendant
reports a type error. Completion cannot demand a new full model there. -/
theorem stable_selected_counterexample :
    (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles).Checked sourceRegistry ∧
    (GeneralNominalCenteredHeadAllocV7Boundary.boundary roles).Initial sourceRegistry root start ∧
    GeneralNominalCenteredHeadMatStepJournal.Models start witness ∧
    B4Target.Steps (GeneralNominalCenteredHeadAllocV7Boundary.Step sourceRegistry root) start final ∧
    GeneralNominalCenteredHeadAllocV7Boundary.Stable sourceRegistry final root ∧
    GeneralNominalCenteredHeadAllocV7Boundary.Local sourceRegistry final root (.selected 37 children) ∧
    GeneralNominalCenteredHeadAllocV7Boundary.Local sourceRegistry final aSite.occurrence .rejected ∧
    (∀ child ∈ children, (root,child) ∈ final.core.erased.current.edges) ∧
    ¬ ∃ model, GeneralNominalCenteredHeadMatStepJournal.Models final model :=
  ⟨⟨rfl,source_checked⟩,initial_source,inhabited,GeneralNominalCenteredHeadAllocMergeConflict.final_trace,
    final_stable,final_parent_selected,GeneralNominalCenteredHeadAllocV7MergeRegression.final_rejected,
    parent_children_recorded,GeneralNominalCenteredHeadAllocMergeConflict.final_empty⟩

end Yulang.GeneralNominalCenteredHeadAllocV7ParentBaseline
