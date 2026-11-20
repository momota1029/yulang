import Yulang.GeneralRebaseCompiledInstall277

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralGeneratedNestedSource299
open GeneralDeclarationExamples (roles constructors display)
open GeneralNominalExamples (registry registry_checked interpretation intDisplay)
open GeneralSourceState (equationAtoms)
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralSourceDictionaries (Occurrence)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)

abbrev shapes (i : Fin 0) : GeneralSourceState.Shape 3 := Fin.elim0 i

def heads (slot : Fin 3) : GeneralSourceState.Head shapes :=
  if slot = 2 then .scalar .int else .unresolved

abbrev base : GeneralSourceState.State where
  slots := 3
  source := Fin.val
  source_injective := fun _ _ eq => Fin.ext eq
  rowSource := Fin.val
  ordinary := equationAtoms 2 (.base .int)
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  heads := heads
  intervals := [(0,0),(1,1),(2,2)]
  heads_sound := by
    intro m valid slot term equation
    by_cases scalar : slot = 2
    · subst slot
      have eq : (.base .int : TyTerm (Fin 3)) = term := by
        simpa [heads,GeneralSourceState.Head.equation] using equation
      subst term
      exact (GeneralSourceState.equationAtoms_exact ..).mp valid
    · simp [heads,scalar,GeneralSourceState.Head.equation] at equation
  intervals_sound := by
    intro m _ pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> exact Common.subtype_refl _

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 0
  shapes := Fin.elim0
  shapes_injective := by intro i; exact Fin.elim0 i
  canonical := by intro i; exact Fin.elim0 i
  heads := fun slot => if slot = 2 then .scalar .int else .deferred .unresolved
  checked := by
    intro slot term found
    by_cases scalar : slot = 2
    · subst slot
      have eq : (.base .int : TyTerm (Fin 3)) = term := by
        simpa [GeneralNormalizedObservation.Head.term] using found
      subst term
      exact .head rfl
    · simp [scalar,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at found

def listDescriptor (argument : Fin 3) : GeneralNominalState.Descriptor 3 :=
  ⟨0,⟨[.type],0⟩,[.type (argument,argument)],rfl⟩

abbrev snapshot : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => if slot = 0 then some (listDescriptor 1)
    else if slot = 1 then some (listDescriptor 2) else none
  catalogue := by
    intro slot desc found
    split at found
    · cases Option.some.inj found; rfl
    · split at found
      · cases Option.some.inj found; rfl
      · cases found
  bodies_opaque := by
    intro slot desc found
    by_cases h : slot = 0
    · subst slot; rfl
    · by_cases h2 : slot = 1
      · subst slot; rfl
      · simp [h,h2] at found
  seed := 2

abbrev context : GeneralNominalCandidates.Context := ⟨snapshot,interpretation⟩

abbrev root : Occurrence roles := ⟨100,⟨0,fun _ => (0,0),[],by intro _ h; cases h⟩⟩
abbrev initial := GeneralNominalVersionedJournal232.initial context root

abbrev intTy : Ty := .base .int
abbrev listTy : Ty := nominal 0 [.inl intTy]
abbrev nestedTy : Ty := nominal 0 [.inl listTy]

def model : Assignment := fun i =>
  ((if i=0 then nestedTy else if i=1 then listTy else intTy),Common.rowEmpty)

theorem snapshot_model : GeneralNominalState.Models snapshot model := by
  refine ⟨⟨?_,?_,?_⟩,?_,by simp [PresenceNormalForm.All]⟩
  · intro atom member
    change atom ∈ equationAtoms (2 : Fin 3) (.base .int) at member
    simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl <;> exact subtype_refl _
  · intro slot term equation
    change (heads slot).equation = some term at equation
    by_cases scalar : slot = 2
    · subst slot
      have eq : (.base .int : TyTerm (Fin 3)) = term := by
        simpa [heads,GeneralSourceState.Head.equation] using equation
      subst term
      exact ⟨subtype_refl _,subtype_refl _⟩
    · simp [heads,scalar,GeneralSourceState.Head.equation] at equation
  · intro pair member
    simp only [base,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> exact subtype_refl _
  · intro slot desc found
    by_cases first : slot = 0
    · subst slot
      have eq : listDescriptor 1 = desc := Option.some.inj found
      subst desc
      exact ⟨[.inl listTy],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,⟨subtype_refl _,subtype_refl _⟩⟩
    · by_cases second : slot = 1
      · subst slot
        have eq : listDescriptor 2 = desc := Option.some.inj found
        subst desc
        exact ⟨[.inl intTy],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,⟨subtype_refl _,subtype_refl _⟩⟩
      · simp [snapshot,first,second] at found

theorem initial_model : Models initial model := by
  apply (GeneralNominalVersionedJournal232.initial_models ..).mpr
  exact ⟨snapshot_model,GeneralNominalCenters.point_root_holds _ _ (fun _ => rfl) _⟩

theorem read_nominals :
    snapshot.nominals (0 : Fin 3) = some (listDescriptor 1) ∧
      snapshot.nominals (1 : Fin 3) = some (listDescriptor 2) ∧
      snapshot.view.heads (2 : Fin 3) = .scalar .int := ⟨rfl,rfl,rfl⟩

end Yulang.GeneralGeneratedNestedSource299
