import Yulang.GeneralNominalUnaryCaptureFacts
import Yulang.GeneralNominalExamples
import Yulang.CommonNominalFullGuardedClosure

/-! A nonvacuous anonymous record/list cycle. The nominal body is absent;
the return edge is the explicit actual parameter of the list descriptor. -/
namespace Yulang.GeneralNominalMixedExamples

open GeneralDeclarationExamples (roles constructors display display_checked)
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralSourceState (equationAtoms equationAtoms_exact)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier

abbrev shapes : Fin 1 → GeneralSourceState.Shape 2 := fun _ => .required 7
abbrev heads : Fin 2 → GeneralSourceState.Head shapes :=
  fun slot => if slot = 0 then .structural 0 (fun _ => 1) else .unresolved

abbrev base : GeneralSourceState.State where
  slots := 2
  source := Fin.val
  source_injective := fun _ _ h => Fin.ext h
  rowSource := Fin.val
  ordinary := equationAtoms 0 (.required 7 (.var 1))
  kinds := 1
  shapes := shapes
  shapes_injective := by intro i j _; exact Subsingleton.elim _ _
  heads := heads
  intervals := [(0,0),(1,1)]
  heads_sound := by
    intro assignment valid slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have same : (.required 7 (.var 1) : TyTerm (Fin 2)) = term := by
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
  shapes := fun _ => .record [7]
  shapes_injective := by intro i j _; exact Subsingleton.elim _ _
  canonical := by intro i; simp [GeneralNormalizedObservation.Shape.Canonical]
  heads := fun slot => if slot = 0 then .structural 0 (fun _ => 1) else .deferred .unresolved
  checked := by
    intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have same : (.record 7 (.var 1) .emptyRecord : TyTerm (Fin 2)) = term := by
        simpa [GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Shape.term,
          GeneralNormalizedObservation.recordTerm,List.ofFn_succ] using recorded
      subst term
      exact .trans (.head rfl) .required
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
  if index = 0 then .record 7 (.inl 1) .emptyRecord else .nominal 0 [.inl (.inl 0)]

abbrev value := CommonNominalFullGuardedClosure.instantiate body Fin.elim0
abbrev model : GeneralNominalCommonBridge.Assignment := fun identity =>
  (if identity = 0 then value 0 else value 1,Common.rowEmpty)

theorem record_equation : Equivalent (value 0) (required 7 (value 1)) := by
  have equation := CommonNominalFullGuardedClosure.all_parameter_sound body Fin.elim0 (0 : Fin 2)
  simpa [CommonNominalFullGuardedClosure.equation,CommonNominalFullGuardedClosure.valueReference,
    CommonNominalSyntax.Layer.map,body,required,record] using equation

theorem list_equation : Equivalent (value 1) (nominal 0 [.inl (value 0)]) := by
  have equation := CommonNominalFullGuardedClosure.all_parameter_sound body Fin.elim0 (1 : Fin 2)
  simpa [CommonNominalFullGuardedClosure.equation,CommonNominalFullGuardedClosure.valueReference,
    CommonNominalSyntax.Layer.map,body,nominal] using equation

theorem state_models : GeneralNominalState.Models state model := by
  refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
  · intro atom member
    change atom ∈ equationAtoms (0 : Fin 2) (.required 7 (.var 1)) at member
    simp only [equationAtoms,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl
    · exact record_equation.1
    · exact record_equation.2
  · intro slot term recorded
    by_cases zero : slot = 0
    · subst slot
      have same : (.required 7 (.var 1) : TyTerm (Fin 2)) = term := by
        simpa [heads,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term] using recorded
      subst term
      exact record_equation
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

theorem structural_edge : GeneralSourceK2.Child view 0 1 := ⟨0,(fun _ => 1),rfl,⟨0,by decide +kernel⟩,rfl⟩

theorem nominal_edge : GeneralNominalMixedRecurrence.ActualArgument state 1 0 :=
  GeneralNominalMixedRecurrence.point_argument_edge state 1 0 descriptor rfl 0 rfl

theorem anonymous_recursive : GeneralNominalMixedRecurrence.RecursAt state 0 :=
  GeneralNominalMixedRecurrence.mixed_cycle_rejects state 0 1
    ⟨0,(fun _ => 1),rfl⟩ structural_edge nominal_edge model state_models

theorem list_not_recursive : ¬ GeneralNominalMixedRecurrence.RecursAt state 1 :=
  GeneralNominalMixedRecurrence.nominal_not_recursive state 1 descriptor rfl

abbrev context : GeneralNominalRecursiveCandidates.Context := ⟨state,GeneralNominalExamples.interpretation⟩
abbrev showRoot : GeneralSourceDictionaries.Occurrence roles :=
  ⟨100,⟨0,fun _ => (1,1),[],by intro _ member; cases member⟩⟩
abbrev childDemand : GeneralSourceState.Demand roles :=
  ⟨0,fun _ => (0,0),[],by intro _ member; cases member⟩

theorem child_K2 : GeneralNominalMixedRecurrence.RootK2 state childDemand := by
  refine ⟨?_,?_,⟨0,by decide +kernel⟩,0,rfl,anonymous_recursive⟩
  · constructor
    · intro index; constructor <;> simp [GeneralNominalState.sources,List.ofFn_succ]
    · intro output member; cases member
  · rintro ⟨index,unknown⟩
    apply unknown
    refine ⟨0,rfl,Or.inl ?_⟩
    simp [GeneralNormalizedObservation.Snapshot.graph,GeneralNormalizedObservation.Head.node]

theorem list_root_not_K2 : ¬ GeneralNominalMixedRecurrence.RootK2 state showRoot.demand := by
  rintro ⟨_,_,index,slot,equal,cycle⟩
  have one : slot = 1 := Fin.ext equal
  subst slot
  exact list_not_recursive cycle

end Yulang.GeneralNominalMixedExamples
