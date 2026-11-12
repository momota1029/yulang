import Yulang.GeneralDictionaryOutputMergeFeedbackClassification

/-! A further exact refresh after equality feedback. Both emitted output IDs,
already forced to int, acquire their own scalar slots in one exact refresh.
The old nominal descriptor and independent row coordinates are retained.
Concrete progress only: no final Stable or general V5 completeness is claimed. -/
namespace Yulang.GeneralDictionaryOutputMergeRefresh
open GeneralDictionaryOutputMergeSuccess GeneralDictionaryOutputMergeFeedback
open GeneralNominalExamples (displayRoot listDescriptor)
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalSaturationState
open Core.PresenceGeneration (TyTerm)
open GeneralSourceState (equationAtoms)
abbrev embed : Fin 2 → Fin 4 := fun i => ⟨i.val,by omega⟩
noncomputable abbrev source : Fin 4 → Nat := fun i => if i.val < 2 then i.val else if i.val = 2 then outputTarget 10 else outputTarget 11
abbrev rowSource : Fin 4 → Nat := fun i => if i.val < 2 then i.val else 0
abbrev heads : Fin 4 → GeneralSourceState.Head (fun i : Fin 0 => Fin.elim0 i : Fin 0 → GeneralSourceState.Shape 4) :=
  fun i => if i = 0 then .unresolved else .scalar .int
noncomputable abbrev base : GeneralSourceState.State where
  slots := 4
  source := source
  source_injective := by
    intro a b eq
    have big := GeneralDictionaryOutputMergeRawModel.output_above_one 10
    have big11 := GeneralDictionaryOutputMergeRawModel.output_above_one 11
    have distinct := output_targets_distinct
    have ha := a.isLt
    have hb := b.isLt
    apply Fin.ext
    dsimp only [source] at eq
    split at eq <;> (try split at eq) <;> (try split at eq) <;> (try split at eq) <;> omega
  rowSource := rowSource
  ordinary := equationAtoms 1 (.base .int) ++ (equationAtoms 2 (.base .int) ++ equationAtoms 3 (.base .int))
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := heads
  intervals := [(0,0),(1,1)]
  heads_sound := by
    intro m valid slot term recorded
    by_cases zero : slot = 0
    · simp [heads,zero,GeneralSourceState.Head.equation] at recorded
    · have same : term = .base .int := by simpa [heads,zero,GeneralSourceState.Head.equation] using recorded.symm
      subst term
      have cases : slot = 1 ∨ slot = 2 ∨ slot = 3 := by
        have h : slot.val = 1 ∨ slot.val = 2 ∨ slot.val = 3 := by
          have := slot.isLt
          have : slot.val ≠ 0 := fun h => zero (Fin.ext h)
          omega
        rcases h with h | h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Or.inl (Fin.ext h))
        · exact Or.inr (Or.inr (Fin.ext h))
      rcases cases with rfl | rfl | rfl
      · exact (GeneralSourceState.equationAtoms_exact ..).mp (fun a member => valid a (List.mem_append_left _ member))
      · exact (GeneralSourceState.equationAtoms_exact ..).mp (fun a member => valid a (List.mem_append_right _ (List.mem_append_left _ member)))
      · exact (GeneralSourceState.equationAtoms_exact ..).mp (fun a member => valid a (List.mem_append_right _ (List.mem_append_right _ member)))
  intervals_sound := by
    intro m _ pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact Common.subtype_refl _
noncomputable abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun i => if i = 0 then .deferred .unresolved else .scalar .int
  checked := by
    intro slot term recorded
    by_cases zero : slot = 0
    · simp [zero,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded
    · have same : term = .base .int := by simpa [zero,GeneralNormalizedObservation.Head.term] using recorded.symm
      subst term
      exact .head (by simp [heads,zero,GeneralSourceState.Head.equation])
abbrev descriptor : GeneralNominalState.Descriptor 4 := ⟨0,⟨[.type],0⟩,[.type (1,1)],rfl⟩
noncomputable abbrev snapshot : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun i => if i = 0 then some descriptor else none
  catalogue := by
    intro slot d recorded
    split at recorded
    · cases Option.some.inj recorded; rfl
    · cases recorded
  bodies_opaque := by
    intro slot d recorded
    by_cases zero : slot = 0
    · subst slot; rfl
    · simp [zero] at recorded
  seed := next.current.context.state.seed
  allocated := next.current.context.state.allocated
  reserved := next.current.context.state.reserved
  ordinary := next.current.context.state.ordinary
noncomputable abbrev refreshedContext : GeneralNominalCandidates.Context := ⟨snapshot,GeneralNominalExamples.interpretation⟩
noncomputable abbrev refreshed : GeneralNominalSupport.Tracked roles :=
  {next with current := regenerate next.current refreshedContext}
private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have := i.isLt
  apply Or.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  omega
noncomputable def refines : GeneralNominalRefinements.Refines next.current.context.state snapshot := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · refine ⟨embed,?_,?_,?_,?_,?_⟩
    · intro i; rcases fin2_cases i with rfl | rfl <;> rfl
    · intro i; rcases fin2_cases i with rfl | rfl <;> rfl
    · intro atom member
      change atom ∈ equationAtoms (1 : Fin 2) (.base .int) at member
      rcases List.mem_cons.mp member with eq | member
      · rw [eq]; exact List.mem_append_left _ (List.mem_cons_self ..)
      · have eq := List.mem_singleton.mp member
        rw [eq]; exact List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    · intro i known
      rcases fin2_cases i with rfl | rfl
      · exact False.elim (known rfl)
      · decide +kernel
    · intro pair member
      change pair ∈ ([(0,0),(1,1)] : List (Fin 2 × Fin 2)) at member
      rcases List.mem_cons.mp member with eq | member
      · rw [eq]; exact List.mem_cons_self ..
      · have eq := List.mem_singleton.mp member
        rw [eq]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
  · intro i term recorded
    rcases fin2_cases i with rfl | rfl
    · cases recorded
    · cases Option.some.inj recorded
      exact .head rfl
  · intro i d recorded
    rcases fin2_cases i with rfl | rfl
    · cases Option.some.inj recorded
      rfl
    · cases recorded
  · intro atom member; exact member
  · rintro id ⟨i,same,known⟩
    refine ⟨embed i,?_,?_⟩
    · rcases fin2_cases i with rfl | rfl <;> exact same
    · rcases fin2_cases i with rfl | rfl
      · exact Or.inr ⟨descriptor,rfl⟩
      · exact Or.inl (by decide +kernel)
  · intro id member; exact member
  · intro id member; exact member


private theorem fin4_cases (i : Fin 4) : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by
  have := i.isLt
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases h with h | h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Or.inl (Fin.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Fin.ext h)))

theorem snapshot_models (m : GeneralNominalCommonBridge.Assignment)
    (valid : Models next.current m) : GeneralNominalState.Models snapshot m := by
  have sourceInt := source_int m ((next_models m).mp valid)
  have outputInt11 := GeneralDictionaryOutputMergeAllModels.output_scalar m ((next_models m).mp valid) 11 (Or.inr rfl)
  have outputInt := GeneralDictionaryOutputMergeAllModels.output_scalar m ((next_models m).mp valid) 10 (Or.inl rfl)
  refine ⟨⟨?_,?_,?_⟩,?_,valid.1.2.2⟩
  · intro atom member
    change atom ∈ equationAtoms (1 : Fin 4) (.base .int) ++ (equationAtoms (2 : Fin 4) (.base .int) ++ equationAtoms (3 : Fin 4) (.base .int)) at member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_cons.mp member with eq | member
      · rw [eq]; exact sourceInt.1
      · rw [List.mem_singleton.mp member]; exact sourceInt.2
    · rcases List.mem_append.mp member with member | member
      · rcases List.mem_cons.mp member with eq | member
        · rw [eq]; exact outputInt.1
        · rw [List.mem_singleton.mp member]; exact outputInt.2
      · rcases List.mem_cons.mp member with eq | member
        · rw [eq]; exact outputInt11.1
        · rw [List.mem_singleton.mp member]; exact outputInt11.2
  · intro slot term recorded
    rcases fin4_cases slot with rfl | rfl | rfl | rfl
    · cases recorded
    · cases Option.some.inj recorded; exact sourceInt
    · cases Option.some.inj recorded; exact outputInt
    · cases Option.some.inj recorded; exact outputInt11
  · intro pair member
    rcases List.mem_cons.mp member with eq | member
    · rw [eq]; exact CommonNominalFullCarrier.subtype_refl _
    · rw [List.mem_singleton.mp member]; exact CommonNominalFullCarrier.subtype_refl _
  · intro slot d recorded
    rcases fin4_cases slot with rfl | rfl | rfl | rfl
    · cases Option.some.inj recorded
      obtain ⟨args,fits,equal⟩ := valid.1.2.1 (0 : Fin 2) listDescriptor rfl
      refine ⟨args,?_,equal⟩
      change GeneralNominalState.FitsAll next.current.context.state.base m [.type ((1 : Fin 2),(1 : Fin 2))] args at fits
      change GeneralNominalState.FitsAll base m [.type ((1 : Fin 4),1)] args
      cases fits with
      | @cons parameter value parameters values head tail =>
        cases tail
        apply GeneralNominalState.FitsAll.cons _ .nil
        cases value <;> exact head
    · cases recorded
    · cases recorded
    · cases recorded

theorem output_member : outputTarget 10 ∈ GeneralNominalState.sources next.current.context.state := by
  apply List.mem_append_left
  apply List.mem_append_right
  exact output_reserved 10 (Or.inl rfl)

theorem output_member11 : outputTarget 11 ∈ GeneralNominalState.sources next.current.context.state := by
  apply List.mem_append_left
  apply List.mem_append_right
  exact output_reserved 11 (Or.inr rfl)

noncomputable def certificate : GeneralNominalCycleSteps.Refresh next.current refreshedContext where
  refines := refines
  interpretation := rfl
  exact := snapshot_models
  support := by
    intro id member
    simp only [GeneralNominalState.sources,List.mem_append] at member ⊢
    rcases member with ((type | row) | reserved) | ordinary
    · obtain ⟨slot,same⟩ := List.mem_ofFn.mp type
      rcases fin4_cases slot with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(0 : Fin 2),same⟩)))
      · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(1 : Fin 2),same⟩)))
      · subst id
        simpa only [source,show ¬ (2 : Fin 4).val < 2 by decide,ite_false,show (2 : Fin 4).val = 2 by rfl,ite_true,Nat.lt_irrefl,ite_false,GeneralNominalState.sources,List.mem_append] using output_member
      · subst id
        simpa only [source,show ¬ (3 : Fin 4).val < 2 by decide,show ¬ (3 : Fin 4).val = 2 by decide,ite_false,GeneralNominalState.sources,List.mem_append] using output_member11
    · obtain ⟨slot,same⟩ := List.mem_ofFn.mp row
      rcases fin4_cases slot with rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨(0 : Fin 2),same⟩)))
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨(1 : Fin 2),same⟩)))
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨(0 : Fin 2),same⟩)))
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨(0 : Fin 2),same⟩)))
    · exact Or.inl (Or.inr reserved)
    · exact Or.inr ordinary

theorem output_unknown : ¬ GeneralNominalState.Known next.current.context.state (outputTarget 10) := by
  rintro ⟨slot,same,_⟩
  have bound := slot.isLt
  have big := GeneralDictionaryOutputMergeRawModel.output_above_one 10
  change slot.val = outputTarget 10 at same
  change slot.val < 2 at bound
  omega

theorem output_known : GeneralNominalState.Known snapshot (outputTarget 10) :=
  ⟨(2 : Fin 4),rfl,Or.inl (by decide +kernel)⟩

theorem output_known11 : GeneralNominalState.Known snapshot (outputTarget 11) :=
  ⟨(3 : Fin 4),rfl,Or.inl (by decide +kernel)⟩

theorem both_outputs_known : GeneralNominalState.Known snapshot (outputTarget 10) ∧
    GeneralNominalState.Known snapshot (outputTarget 11) := ⟨output_known,output_known11⟩

theorem actual_step : GeneralNominalSupportSteps.Step registry displayRoot next refreshed :=
  ⟨displayRoot,.root,.administrative displayRoot refreshed.current
    (.refresh displayRoot refreshedContext certificate (outputTarget 10) output_member output_unknown output_known)⟩

theorem not_stable : ¬ GeneralNominalSupportSteps.Stable registry next displayRoot := by
  intro halted
  exact halted _ actual_step.choose_spec.1 _ actual_step.choose_spec.2

theorem models_exact (m : GeneralNominalCommonBridge.Assignment) :
    Models refreshed.current m ↔ Models next.current m :=
  GeneralNominalCycleSteps.refresh_models certificate m

theorem inhabited : Models refreshed.current GeneralNominalExamples.model :=
  (models_exact _).mpr next_inhabited

theorem sourceformed : GeneralNominalSupportSteps.SourceFormed registry displayRoot refreshed :=
  .update next_sourceformed actual_step

theorem reachable : B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary roles) registry displayRoot refreshed := by
  obtain ⟨initial,started,path⟩ := next_reachable
  exact ⟨initial,started,.tail path actual_step⟩

/-- The complete root evidence remains valid in the pre-refresh context for
EVERY post-refresh model. Current-context transport is deliberately not claimed. -/
theorem prior_context_evidence (m : GeneralNominalCommonBridge.Assignment)
    (valid : Models refreshed.current m) :
    GeneralDictionaryRecursiveEvidence.Evidence registry next.current.context m displayRoot
      GeneralDictionaryOutputMergeRootEvidence.rootPayload :=
  next_evidence m ((models_exact m).mp valid)


/-- Slot growth represents an existing named output; it introduces no new
source identity and preserves the separate old type and row coordinates. -/
theorem sources_exact (id : Nat) :
    id ∈ GeneralNominalState.sources snapshot ↔
      id ∈ GeneralNominalState.sources next.current.context.state :=
  ⟨certificate.support id,GeneralNominalRefinements.sources refines id⟩

theorem genuine_observation_progress :
    next.current.context.state.base.slots = 2 ∧ snapshot.base.slots = 4 ∧
    ¬ GeneralNominalState.Known next.current.context.state (outputTarget 10) ∧
    GeneralNominalState.Known snapshot (outputTarget 10) :=
  ⟨rfl,rfl,output_unknown,output_known⟩

end Yulang.GeneralDictionaryOutputMergeRefresh
