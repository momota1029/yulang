import Yulang.GeneralDictionaryReservedSuccessorBoundary

/-! A real carrier-extension refresh makes the reserved nominal output observable.
No final Stable or arbitrary normalization claim is made. -/
namespace Yulang.GeneralDictionaryReservedNominalRefresh
open GeneralDictionaryFiniteObservedExampleReserved
open GeneralDictionaryFiniteObservedExampleReservedPositive
open GeneralDictionaryReservedEqualityStep
open GeneralDictionaryFiniteObservedExample (registry interpretation constructors arguments)
open GeneralDeclarationExamples (roles)
open GeneralNominalSaturationState
open Core.PresenceGeneration (TyTerm)
open GeneralSourceState (equationAtoms)
open CommonNominalFullCarrier
abbrev embed : Fin 2 → Fin 3 := fun i => ⟨i.val,by omega⟩
abbrev source : Fin 3 → Nat := Fin.val
abbrev rowSource : Fin 3 → Nat := fun i => if i.val < 2 then i.val else 0
abbrev heads : Fin 3 → GeneralSourceState.Head (fun i : Fin 0 => Fin.elim0 i : Fin 0 → GeneralSourceState.Shape 3) :=
  fun i => if i = 1 then .scalar .int else .unresolved
abbrev base : GeneralSourceState.State where
  slots := 3
  source := source
  source_injective := fun _ _ h => Fin.ext h
  rowSource := rowSource
  ordinary := equationAtoms 1 (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := heads
  intervals := [(0,0),(1,1)]
  heads_sound := by
    intro m valid slot term recorded
    by_cases one : slot = 1
    · subst slot
      have same : term = .base .int := by simpa [heads,GeneralSourceState.Head.equation] using recorded.symm
      subst term
      exact (GeneralSourceState.equationAtoms_exact ..).mp valid
    · simp [heads,one,GeneralSourceState.Head.equation] at recorded
  intervals_sound := by
    intro m _ pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact Common.subtype_refl _
abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun i => if i = 1 then .scalar .int else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases one : slot = 1
    · subst slot
      have same : term = .base .int := by simpa [GeneralNormalizedObservation.Head.term] using recorded.symm
      subst term
      exact .head rfl
    · simp [one,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded
abbrev descriptor : GeneralNominalState.Descriptor 3 :=
  ⟨0,⟨[.type,.type,.type],0⟩,[.type (1,1),.type (1,1),.type (1,1)],rfl⟩
noncomputable abbrev snapshot : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun i => if i = 1 then none else some descriptor
  catalogue := by
    intro slot d recorded
    split at recorded
    · cases recorded
    · cases Option.some.inj recorded; rfl
  bodies_opaque := by
    intro slot d recorded
    by_cases one : slot = 1
    · simp [one] at recorded
    · simp [one]
  seed := after.current.context.state.seed
  allocated := after.current.context.state.allocated
  reserved := after.current.context.state.reserved
  ordinary := after.current.context.state.ordinary
noncomputable abbrev refreshedContext : GeneralNominalCandidates.Context := ⟨snapshot,interpretation⟩
noncomputable abbrev refreshed : GeneralNominalSupport.Tracked roles :=
  {after with current := regenerate after.current refreshedContext}
private theorem fin2_cases (i : Fin 2) : i = 0 ∨ i = 1 := by
  have := i.isLt
  apply Or.imp (fun h => Fin.ext h) (fun h => Fin.ext h)
  omega
noncomputable def refines : GeneralNominalRefinements.Refines after.current.context.state snapshot := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,rfl,rfl⟩
  · refine ⟨embed,?_,?_,?_,?_,?_⟩
    · intro i; rcases fin2_cases i with rfl | rfl <;> rfl
    · intro i; rcases fin2_cases i with rfl | rfl <;> rfl
    · intro atom member
      change atom ∈ equationAtoms (1 : Fin 2) (.base .int) at member
      rcases List.mem_cons.mp member with eq | member
      · rw [eq]; exact List.mem_cons_self ..
      · have eq := List.mem_singleton.mp member
        rw [eq]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
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



private theorem fin3_cases (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by have := i.isLt; omega
  rcases h with h | h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Or.inl (Fin.ext h))
  · exact Or.inr (Or.inr (Fin.ext h))

private theorem nominal_fits (m : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current m) : GeneralNominalState.FitsAll base m descriptor.arguments arguments := by
  obtain ⟨args,fits,equal⟩ := valid.1.2.1 (0 : Fin 2) GeneralDictionaryFiniteObservedExample.descriptor rfl
  have scalar := valid.1.1.2.1 (1 : Fin 2) (.base .int) rfl
  exact .cons scalar (.cons scalar (.cons scalar .nil))

theorem snapshot_models (m : GeneralNominalCommonBridge.Assignment)
    (valid : Models after.current m) : GeneralNominalState.Models snapshot m := by
  have scalar := valid.1.1.2.1 (1 : Fin 2) (.base .int) rfl
  refine ⟨⟨?_,?_,?_⟩,?_,valid.1.2.2⟩
  · intro atom member
    change atom ∈ equationAtoms (1 : Fin 3) (.base .int) at member
    rcases List.mem_cons.mp member with eq | member
    · rw [eq]; exact scalar.1
    · rw [List.mem_singleton.mp member]; exact scalar.2
  · intro slot term recorded
    rcases fin3_cases slot with rfl | rfl | rfl
    · cases recorded
    · cases Option.some.inj recorded; exact scalar
    · cases recorded
  · intro pair member
    rcases List.mem_cons.mp member with eq | member
    · rw [eq]; exact subtype_refl _
    · rw [List.mem_singleton.mp member]; exact subtype_refl _
  · intro slot d recorded
    rcases fin3_cases slot with rfl | rfl | rfl
    · cases Option.some.inj recorded
      exact ⟨arguments,nominal_fits m valid,GeneralDictionaryReservedOutputEquality.source_equal m ((models_iff m).mp valid)⟩
    · cases recorded
    · cases Option.some.inj recorded
      exact ⟨arguments,nominal_fits m valid,GeneralDictionaryReservedOutputEquality.output_equal m ((models_iff m).mp valid)⟩

theorem output_member : 2 ∈ GeneralNominalState.sources after.current.context.state := by
  apply List.mem_append_left
  apply List.mem_append_right
  change 2 ∈ [2]
  exact List.mem_singleton_self _

noncomputable def certificate : GeneralNominalCycleSteps.Refresh after.current refreshedContext where
  refines := refines
  interpretation := rfl
  exact := snapshot_models
  support := by
    intro id member
    simp only [GeneralNominalState.sources,List.mem_append] at member ⊢
    rcases member with ((type | row) | reserved) | ordinary
    · obtain ⟨slot,same⟩ := List.mem_ofFn.mp type
      rcases fin3_cases slot with rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(0 : Fin 2),same⟩)))
      · exact Or.inl (Or.inl (Or.inl (List.mem_ofFn.mpr ⟨(1 : Fin 2),same⟩)))
      · subst id; exact Or.inl (Or.inr (List.mem_singleton_self _))
    · obtain ⟨slot,same⟩ := List.mem_ofFn.mp row
      rcases fin3_cases slot with rfl | rfl | rfl
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨(0 : Fin 2),same⟩)))
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨(1 : Fin 2),same⟩)))
      · exact Or.inl (Or.inl (Or.inr (List.mem_ofFn.mpr ⟨(0 : Fin 2),same⟩)))
    · exact Or.inl (Or.inr reserved)
    · exact Or.inr ordinary

theorem output_known : GeneralNominalState.Known snapshot 2 :=
  ⟨(2 : Fin 3),rfl,Or.inr ⟨descriptor,rfl⟩⟩

theorem refresh_step : GeneralNominalValueSteps.Step registry root after refreshed :=
  ⟨root,.root,.administrative root _ (.refresh root refreshedContext certificate 2 output_member
    GeneralDictionaryReservedSuccessorBoundary.output_not_known output_known)⟩

theorem equality_successor_not_stable : ¬ GeneralNominalValueSteps.Stable registry after root := by
  intro stable
  exact stable refresh_step.choose refresh_step.choose_spec.1 refreshed refresh_step.choose_spec.2

theorem refreshed_models (m : GeneralNominalCommonBridge.Assignment) :
    Models refreshed.current m ↔ Models after.current m := GeneralNominalCycleSteps.refresh_models certificate m

theorem refreshed_reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root refreshed := by
  obtain ⟨start,initial,path⟩ := reachable
  exact ⟨start,initial,.tail path refresh_step⟩
theorem refreshed_inhabited : Models refreshed.current positive :=
  (refreshed_models positive).mpr ((models_iff positive).mpr installed_models)
end Yulang.GeneralDictionaryReservedNominalRefresh
