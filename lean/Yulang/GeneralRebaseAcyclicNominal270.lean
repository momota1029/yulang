import Yulang.GeneralRebaseOriginRepresentative270
import Yulang.GeneralRebaseVariantNominalFixture270

/-! Finite nominal-to-scalar journal. The negative semantic recurrence
answer depends on checking negative edge observations, not missing ones. -/
namespace Yulang.GeneralRebaseAcyclicNominal270
open GeneralDeclarationExamples (roles constructors)
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralSourceState (equationAtoms equationAtoms_exact)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier
open GeneralRebaseOriginRepresentative270

abbrev shapes : Fin 0 → GeneralSourceState.Shape 2 := Fin.elim0
abbrev heads : Fin 2 → GeneralSourceState.Head shapes :=
  fun slot => if slot = 1 then .scalar .int else .unresolved

abbrev base : GeneralSourceState.State where
  slots := 2
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := equationAtoms 1 (.base .int)
  kinds := 0
  shapes := shapes
  shapes_injective := fun i => Fin.elim0 i
  heads := heads
  intervals := [(1,1)]
  heads_sound := by
    intro assignment valid slot term recorded
    by_cases one : slot = 1
    · subst slot
      have same : (.base .int : TyTerm (Fin 2)) = term := by
        simpa [heads,GeneralSourceState.Head.equation] using recorded
      subst term
      exact (equationAtoms_exact ..).mp valid
    · simp [heads,one,GeneralSourceState.Head.equation] at recorded
  intervals_sound := by
    intro assignment _ pair member
    cases List.mem_singleton.mp member
    exact Common.subtype_refl _

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := fun i => Fin.elim0 i
  canonical := fun kind => Fin.elim0 kind
  heads := fun slot => if slot = 1 then .scalar .int else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases one : slot = 1
    · subst slot
      have same : (.base .int : TyTerm (Fin 2)) = term := by
        simpa [GeneralNormalizedObservation.Head.term] using recorded
      subst term
      exact .head rfl
    · simp [one,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded

abbrev descriptor : GeneralNominalState.Descriptor 2 := ⟨0,⟨[.type],0⟩,[.type (1,1)],rfl⟩

abbrev state : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => if slot = 0 then some descriptor else none
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

abbrev model : GeneralNominalCommonBridge.Assignment := fun identity =>
  (if identity = 0 then nominal 0 [.inl (.base .int)] else .base .int,Common.rowEmpty)

theorem state_models : GeneralNominalState.Models state model := by
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro atom member
    change atom ∈ equationAtoms (1 : Fin 2) (.base .int) at member
    simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact subtype_refl _
  · intro slot term recorded
    by_cases one : slot = 1
    · subst slot
      have same : (.base .int : TyTerm (Fin 2)) = term := by
        simpa [heads,GeneralSourceState.Head.equation] using recorded
      subst term
      exact ⟨subtype_refl _,subtype_refl _⟩
    · simp [heads,one,GeneralSourceState.Head.equation] at recorded
  · intro pair member
    cases List.mem_singleton.mp member
    exact subtype_refl _
  · intro slot d recorded
    by_cases zero : slot = 0
    · subst slot
      have same : descriptor = d := Option.some.inj recorded; subst d
      exact ⟨[.inl (.base .int)],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,
        ⟨subtype_refl _,subtype_refl _⟩⟩
    · simp [state,zero] at recorded

abbrev context : GeneralNominalCandidates.Context := ⟨state,GeneralNominalExamples.interpretation⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles :=
 ⟨100,⟨0,fun _ => (0,0),[],by intro _ h; cases h⟩⟩
abbrev journal := GeneralNominalVersionedJournal232.initial context root

theorem full_model : GeneralNominalVersionedJournal232.Models journal model :=
 (GeneralNominalVersionedJournal232.initial_models ..).mpr
   ⟨state_models,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩

def points (i : Fin 2) : GeneralRebaseStructuralOrigin270.Slots journal := i

theorem coverage : GeneralRebaseMixedOriginWindow270.check journal points = true := by decide +kernel

theorem projected_name : representative journal (.nominal (.source 0) 0 0) = some (points 1) := by decide +kernel
theorem projected_vs_parent : compare journal (.nominal (.source 0) 0 0) (.source 0) = some false := by decide +kernel
theorem calculated_no_loop : (window journal points).probe 0 0 = some false := by decide +kernel
theorem calculated_leaf : (window journal points).probe 0 1 = some true := by decide +kernel
theorem calculated_no_return : (window journal points).probe 1 0 = some false := by decide +kernel
theorem calculated_leaf_terminal : (window journal points).probe 1 1 = some false := by decide +kernel
theorem calculated_acyclic : query journal points (.source 0) = some false := by decide +kernel

theorem actual_no_cycle : ¬ GeneralNominalVersionedCycles232.Cyclic journal (.source 0) := by
 have known := query_sound journal points coverage ⟨model,full_model⟩ (.source 0)
 rw [calculated_acyclic] at known
 exact known

end Yulang.GeneralRebaseAcyclicNominal270
