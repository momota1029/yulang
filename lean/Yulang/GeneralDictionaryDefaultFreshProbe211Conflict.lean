import Yulang.GeneralDictionaryDefaultFreshProbe211Stable

set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralDictionaryDefaultFreshProbe211Conflict
open GeneralDeclarations GeneralDeclarationPatterns GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection CommonNominalFullCarrier
open GeneralDictionaryDefaultFreshProbe211Source GeneralDictionaryDefaultFreshProbe211Install
open GeneralDictionaryDefaultFreshProbe211State GeneralDictionaryDefaultFreshProbe211Stable
open GeneralNominalCenteredHeadMatStepJournal

abbrev chosen := GeneralNominalCenteredHeadAllocEncoding.declaration sibling
abbrev focus := cSite.occurrence
abbrev current (atoms) := (stage atoms).core.erased.current.context

theorem chosen_checked : DeclarationChecked registry.constructors roles chosen :=
  GeneralNominalCenteredHeadAllocEncoding.declaration_checked sibling_checked

theorem chosen_only (visible : d ∈ registry.declarations) (role : d.role = focus.demand.role) : d = chosen := by
  rcases List.mem_cons.mp visible with same | member
  · subst d; cases role
  · rcases List.mem_cons.mp member with rfl | member
    · cases role
    · exact List.mem_singleton.mp member

theorem fresh (supported : Supported atoms) : GeneralNominalAllocation.Fresh (current atoms).state registry focus.identity := by
  intro key member collision
  have owned := source_owned supported collision
  have invocation : key.1 = focus.identity := by
    change key ∈ [_,_,_,_,_] at member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rfl
  rcases owned with zero | ⟨old,prior,equal⟩
  · have above := GeneralNominalIdentities.source_above_seed snapshot.seed key
    change GeneralNominalIdentities.source snapshot.seed key = 0 at zero
    rw [zero] at above
    exact False.elim (Nat.not_lt_zero _ above)
  · change GeneralNominalIdentities.source snapshot.seed old = GeneralNominalIdentities.source snapshot.seed key at equal
    have keys := (GeneralNominalIdentities.source_identity snapshot.seed old key).mp equal
    have bad := prior.symm.trans ((congrArg Prod.fst keys).trans invocation)
    exact False.elim (Nat.ne_of_lt c_above_root bad)

theorem empty_report : report (current atoms) chosen [] = {} := by
  simp [report,GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,
    chosen,GeneralNominalCenteredHeadAllocEncoding.declaration,inspectMany]

theorem chosen_head_model (good : Good atoms) :
    GeneralNominalCenteredHeadCandidates.HeadModels registry (current atoms) focus chosen [] uniform := by
  constructor
  · unfold privateState
    rw [empty_report]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨raw_uniform good,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · exact PresenceNormalForm.all_nil _ _
    · exact PresenceNormalForm.all_nil _ _
  · rw [empty_report]; simp [ProjectionModels]

theorem prepared (good : Good atoms) (supported : Supported atoms) :
    GeneralNominalCenteredHeadCandidates.Prepared registry (current atoms) focus chosen := by
  refine ⟨source.metadata,⟨?_,?_⟩,fresh supported,[],rfl,?_,uniform,chosen_head_model good⟩
  · intro index; exact Fin.elim0 index
  · intro output member; cases member
  · rw [empty_report]; exact ⟨rfl,rfl,rfl⟩

theorem known : ¬ GeneralNominalState.RootPending (current atoms).state (GeneralNominalCenteredHeadCandidates.inputs focus).demand := by
  rintro ⟨index,_⟩; exact Fin.elim0 index

theorem survivor (good : Good atoms) (supported : Supported atoms) :
    GeneralNominalCenteredHeadCandidates.Survivor registry (current atoms) focus 39 [] :=
  ⟨known,chosen,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _)),chosen_checked,rfl,rfl,[],rfl,
    prepared good supported,by
      simp [GeneralNominalAllocation.children,GeneralDictionaryEmissionPlans.children,GeneralCanonicalChildOrder.canonicalEmit,
        GeneralCanonicalChildOrder.canonicalDeclaration,GeneralCanonicalChildOrder.canonicalRequirements,
        chosen,GeneralNominalCenteredHeadAllocEncoding.declaration,GeneralDeclarationDemands.emitAll]⟩

theorem unique (good : Good atoms) (supported : Supported atoms) :
    GeneralNominalCenteredHeadCandidates.Unique registry (current atoms) focus 39 [] := by
  refine ⟨survivor good supported,?_⟩
  intro key children found
  have copy := found
  obtain ⟨_,d,visible,_,identity,role,_⟩ := found
  cases chosen_only visible role
  cases identity
  exact ⟨rfl,GeneralNominalCenteredHeadCandidates.survivor_children_functional checked copy (survivor good supported)⟩

theorem no_raw_recurs (good : Good atoms) (slot : Fin (current atoms).state.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt (current atoms).state slot := by
  intro cycle
  obtain ⟨next,edge,_⟩ := GeneralNominalCycleK2.recurs_cycle _ _ cycle
  rcases edge with ⟨kind,_,_,_⟩ | argument
  · exact Fin.elim0 kind
  · obtain ⟨descriptor,recorded,_⟩ := GeneralNominalMixedRecurrence.actual_edge_sound _ _ _ argument uniform (raw_uniform good)
    cases recorded

theorem administrative_ready : GeneralNominalCenteredHeadMatStepLocal.AdministrativeReady (stage atoms) focus := by
  refine ⟨⟨cSite,List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))),rfl⟩,?_⟩
  intro first one _ last two same
  exact merges_closed one two same

theorem safe (good : Good atoms) (supported : Supported atoms) :
    B4TargetV6.SafeKnown (GeneralNominalCenteredHeadMatStepBoundary.boundary roles) registry (stage atoms) focus := by
  refine ⟨known,?_,?_,?_⟩
  · rintro (old | (⟨index,cycle⟩ | ⟨site,present,same,index,cycle⟩))
    · obtain ⟨_,_,_,slot,_,cycle⟩ := old; exact no_raw_recurs good slot cycle
    · exact empty_models good.2 cycle.2
    · exact empty_models good.2 cycle.2
  · rintro (old | ⟨candidate,framed,entry,member,cycle⟩)
    · obtain ⟨_,_,_,_,_,_,_,_,visited,_,cycle⟩ := old; exact no_raw_recurs good visited.1 cycle
    · exact empty_models good.2 cycle.2
  · rintro (⟨_,d,visible,role,_,unprepared⟩ | unclosed)
    · cases chosen_only visible role; exact unprepared (prepared good supported)
    · exact unclosed administrative_ready

theorem selected (good : Good atoms) (supported : Supported atoms) :
    GeneralNominalCenteredHeadAllocBoundary.Local sourceRegistry (stage atoms) focus (.selected 39 []) :=
  GeneralNominalCenteredHeadAllocBoundary.local_iff.mpr
    (.selected (safe good supported) (unique good supported) (fun conflict => empty_models good.2
      (by obtain ⟨model,valid,_⟩ := conflict.1; exact ⟨model,valid⟩)))

theorem final_selected : GeneralNominalCenteredHeadAllocBoundary.Local sourceRegistry final focus (.selected 39 []) := by
  obtain ⟨atoms,good,supported,same⟩ := final_shape
  rw [same]; exact selected good supported

theorem final_empty : ¬ ∃ model, Models final model := by
  obtain ⟨atoms,good,_,same⟩ := final_shape
  rw [same]; exact empty_models good.2

theorem final_generated : GeneralNominalSaturationState.Generated final.core.erased.current root focus := by
  obtain ⟨atoms,_,_,same⟩ := final_shape
  rw [same]
  exact .child .root (by
    change (root,focus) ∈ [] ++ children.map (fun child => (root,child))
    exact List.mem_map.mpr ⟨focus,by rw [children_exact]; simp,rfl⟩)

theorem final_stable_focus : GeneralNominalCenteredHeadAllocBoundary.Stable sourceRegistry final focus :=
  (GeneralNominalCenteredHeadMatStepKernel.closure final_exit.2).2 focus final_generated

theorem not_headBaseline : ¬ GeneralNominalCenteredHeadAllocCompletion.HeadBaseline roles := by
  intro baseline
  obtain ⟨model,valid,_⟩ := baseline sourceRegistry ⟨rfl,source_checked⟩ final root focus 39 [] final_reachable final_selected
  exact final_empty ⟨model,valid⟩

theorem not_selectedCompletion : ¬ GeneralNominalCenteredHeadAllocCompletion.SelectedCompletion roles := by
  intro completion
  obtain ⟨effect,_,_,_,_,_,_,model,valid,_⟩ :=
    completion sourceRegistry ⟨rfl,source_checked⟩ final root focus 39 [] final_reachable final_selected
  exact final_empty ⟨model,valid⟩

theorem final_raw : GeneralNominalState.Models final.core.erased.current.context.state uniform := by
  obtain ⟨atoms,good,_,same⟩ := final_shape
  rw [same]; exact raw_uniform good

theorem final_trace : B4Target.Steps
    (GeneralNominalCenteredHeadAllocBoundary.Step sourceRegistry root) start final := by
  have firstSteps : B4Target.Steps (GeneralNominalCenteredHeadAllocBoundary.Step sourceRegistry root) start merged :=
    .tail (.tail .refl install_step) merge_step
  have extend : ∀ next, B4Target.Steps (GeneralNominalCenteredHeadAllocBoundary.Step sourceRegistry root) merged next →
      B4Target.Steps (GeneralNominalCenteredHeadAllocBoundary.Step sourceRegistry root) start next := by
    intro next path
    induction path with
    | refl => exact firstSteps
    | tail _ action ih => exact .tail ih action
  exact extend final final_exit.1

theorem final_no_leaf_packet :
    ¬ ∃ packet ∈ final.core.erased.current.packets, packet.declaration.id = 39 := by
  obtain ⟨atoms,_,_,same⟩ := final_shape
  rw [same]
  rintro ⟨packet,member,identity⟩
  cases List.mem_singleton.mp member
  cases identity

theorem final_no_installable (effect : Effect roles) :
    ¬ GeneralNominalCenteredHeadMatStepKernel.Installable registry final effect := by
  intro enabled
  obtain ⟨model,valid,_⟩ := enabled.common
  exact final_empty ⟨model,valid⟩

theorem final_no_outputConflict :
    ¬ GeneralNominalCenteredHeadMatStepLocal.OutputConflict registry final focus 39 := by
  rintro ⟨⟨model,valid,_⟩,_⟩
  exact final_empty ⟨model,valid⟩

/-- A checked ground source with an inhabited initial and installed state reaches
an actual terminal selected generated demand with an empty corrected journal. -/
theorem stable_selected_counterexample :
    (GeneralNominalCenteredHeadAllocBoundary.boundary roles).Checked sourceRegistry ∧
    (GeneralNominalCenteredHeadAllocBoundary.boundary roles).Initial sourceRegistry root start ∧
    Models start witness ∧ Models installed witness ∧
    B4Target.Steps (GeneralNominalCenteredHeadAllocBoundary.Step sourceRegistry root) start final ∧
    GeneralNominalCenteredHeadAllocBoundary.Stable sourceRegistry final focus ∧
    GeneralNominalSaturationState.Generated final.core.erased.current root focus ∧
    GeneralNominalCenteredHeadAllocBoundary.Local sourceRegistry final focus (.selected 39 []) ∧
    GeneralNominalState.Models final.core.erased.current.context.state uniform ∧
    ¬ ∃ model, Models final model :=
  ⟨⟨rfl,source_checked⟩,initial_source,inhabited,installed_models,final_trace,
    final_stable_focus,final_generated,final_selected,final_raw,final_empty⟩

end Yulang.GeneralDictionaryDefaultFreshProbe211Conflict
