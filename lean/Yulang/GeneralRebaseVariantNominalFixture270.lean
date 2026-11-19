import Yulang.GeneralRebaseMixedOriginWindow270
import Yulang.GeneralRebaseOriginExecutable269
import Yulang.GeneralNominalUnaryCaptureFacts
import Yulang.GeneralNominalExamples
import Yulang.CommonNominalFullGuardedClosure

/-! A checked synthetic variant/nominal recursive snapshot for the finite
semantic-origin window, with an explicit regular model. Surface source
reachability is not part of this fixture. -/
namespace Yulang.GeneralRebaseVariantNominalFixture270

open GeneralDeclarationExamples (roles constructors display display_checked)
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralSourceState (equationAtoms equationAtoms_exact)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier

abbrev shapes : Fin 1 → GeneralSourceState.Shape 2 := fun _ => .variant 7
abbrev heads : Fin 2 → GeneralSourceState.Head shapes :=
  fun slot => if slot = 0 then .structural 0 (fun _ => 1) else .unresolved

abbrev base : GeneralSourceState.State where
  slots := 2
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := equationAtoms 0 (.variant 7 (.var 1))
  kinds := 1
  shapes := shapes
  shapes_injective := by intro i j _; exact Subsingleton.elim _ _
  heads := heads
  intervals := [(0,0),(1,1)]
  heads_sound := by
    intro assignment valid slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have same : (.variant 7 (.var 1) : TyTerm (Fin 2)) = term := by
        simpa [heads,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term] using recorded
      subst term
      exact (equationAtoms_exact ..).mp valid
    · simp [heads,zero,GeneralSourceState.Head.equation] at recorded
  intervals_sound := by
    intro assignment _ pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact Common.subtype_refl _

abbrev view : GeneralNormalizedObservation.Snapshot base where
  kinds := 1
  shapes := fun _ => .variant 7
  shapes_injective := by intro i j _; exact Subsingleton.elim _ _
  canonical := by intro i; simp [GeneralNormalizedObservation.Shape.Canonical]
  heads := fun slot => if slot = 0 then .structural 0 (fun _ => 1) else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have same : (.variant 7 (.var 1) : TyTerm (Fin 2)) = term := by
        simpa [GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Shape.term,
          GeneralNormalizedObservation.Shape.arity] using recorded
      subst term
      exact .head rfl
    · simp [zero,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at recorded

abbrev descriptor : GeneralNominalState.Descriptor 2 := ⟨0,⟨[.type],0⟩,[.type (0,0)],rfl⟩

abbrev state : GeneralNominalState.State where
  base := base
  view := view
  constructors := constructors
  nominals := fun slot => if slot = 1 then some descriptor else none
  catalogue := by
    intro slot d recorded
    split at recorded
    · have same := Option.some.inj recorded; subst d; rfl
    · cases recorded
  bodies_opaque := by
    intro slot d recorded
    by_cases one : slot = 1
    · subst slot; rfl
    · simp [one] at recorded

abbrev body : CommonNominalFullGuardedClosure.Body 2 0 := fun index =>
  if index = 0 then .variant 7 (.inl 1) else .nominal 0 [.inl (.inl 0)]

abbrev value := CommonNominalFullGuardedClosure.instantiate body Fin.elim0
abbrev model : GeneralNominalCommonBridge.Assignment := fun identity =>
  (if identity = 0 then value 0 else value 1,Common.rowEmpty)

theorem variant_equation : Equivalent (value 0) (variant 7 (value 1)) := by
  have equation := CommonNominalFullGuardedClosure.all_parameter_sound body Fin.elim0 (0 : Fin 2)
  simpa [CommonNominalFullGuardedClosure.equation,CommonNominalFullGuardedClosure.valueReference,
    CommonNominalSyntax.Layer.map,body,variant] using equation

theorem list_equation : Equivalent (value 1) (nominal 0 [.inl (value 0)]) := by
  have equation := CommonNominalFullGuardedClosure.all_parameter_sound body Fin.elim0 (1 : Fin 2)
  simpa [CommonNominalFullGuardedClosure.equation,CommonNominalFullGuardedClosure.valueReference,
    CommonNominalSyntax.Layer.map,body,nominal] using equation

theorem state_models : GeneralNominalState.Models state model := by
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro atom member
    change atom ∈ equationAtoms (0 : Fin 2) (.variant 7 (.var 1)) at member
    simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact variant_equation.1
    · exact variant_equation.2
  · intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have same : (.variant 7 (.var 1) : TyTerm (Fin 2)) = term := by
        simpa [heads,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term] using recorded
      subst term
      exact variant_equation
    · simp [heads,zero,GeneralSourceState.Head.equation] at recorded
  · intro pair member
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl <;> exact subtype_refl _
  · intro slot d recorded
    by_cases one : slot = 1
    · subst slot
      have same : descriptor = d := Option.some.inj recorded; subst d
      exact ⟨[.inl (value 0)],.cons ⟨subtype_refl _,subtype_refl _⟩ .nil,list_equation⟩
    · simp [state,one] at recorded

abbrev context : GeneralNominalCandidates.Context := ⟨state,GeneralNominalExamples.interpretation⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles :=
 ⟨100,⟨0,fun _ => (0,0),[],by intro _ h; cases h⟩⟩
abbrev journal := GeneralNominalVersionedJournal232.initial context root

theorem full_model : GeneralNominalVersionedJournal232.Models journal model :=
 (GeneralNominalVersionedJournal232.initial_models ..).mpr
   ⟨state_models,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩

def points (i : Fin 2) : GeneralRebaseStructuralOrigin270.Slots journal := i

def window := GeneralRebaseMixedOriginWindow270.window journal points (fun _ _ => none)

theorem coverage : GeneralRebaseMixedOriginWindow270.check journal points = true := by decide +kernel

theorem certificate :
 GeneralRebaseOriginCycles268.Sound journal window ∧
 GeneralRebaseOriginQuotient269.Forward journal window.point :=
 GeneralRebaseMixedOriginWindow270.certified journal points (fun _ _ => none)
   (fun _ _ => True.intro) coverage ⟨model,full_model⟩

def identify (o : GeneralNominalRecursiveInspection.Origin) (i : Fin 2) : Option Bool :=
 if o = window.point i then some true else none

theorem identify_sound (o : GeneralNominalRecursiveInspection.Origin) (i : Fin 2) :
 GeneralRebasePartialBool268.Reflect (GeneralNominalVersionedCycles232.Equal journal o (window.point i))
   (identify o i) := by
 unfold identify
 split
 · rename_i same
   rw [same]
   exact fun m _ => GeneralNominalOriginTerms.source_self m _
 · trivial

def query (o : GeneralNominalRecursiveInspection.Origin) : Option Bool :=
 GeneralRebaseOriginExecutable269.cyclic window identify (fun _ => true) (fun _ => false) o

theorem calculated_forward : window.probe 0 1 = some true := by decide +kernel
theorem calculated_backward : window.probe 1 0 = some true := by decide +kernel
theorem calculated_root : query (.source 0) = some true := by decide +kernel

/-- Rigid structural and actual nominal positions participate in the
same full-model recurrence. The structural literal and nominal interval
edges are computed with every supplied semantic fallback unknown. -/
theorem actual_cycle : GeneralNominalVersionedCycles232.Cyclic journal (.source 0) := by
 have obtained := GeneralRebaseOriginExecutable269.with_semantic_closure window certificate.1 identify
   (identify_sound (.source 0)) certificate.2
 change GeneralRebasePartialBool268.Reflect _ (query (.source 0)) at obtained
 rw [calculated_root] at obtained
 exact obtained

end Yulang.GeneralRebaseVariantNominalFixture270
