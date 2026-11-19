import Yulang.GeneralRebaseClosedRecordDriver271
import Yulang.CommonNominalFullGuardedClosure

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRecordRecursiveFixture271
open GeneralDeclarationExamples (roles constructors)
open GeneralSourceState (equationAtoms)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier
open GeneralRebaseClosedRecordDriver271 (covered window totalEdges inspect inspectRoot)

abbrev shapes (k : Fin 2) : GeneralNormalizedObservation.Shape :=
 if k = 0 then .record [2,7] else .exactEmpty

abbrev children (k : Fin 2) : Fin (shapes k).arity → Fin 2 :=
 fun i => if i.val = 0 then 0 else 1

abbrev introduce (k : Fin 2) : TyTerm (Fin 2) := (shapes k).term (children k)

abbrev equations := equationAtoms 0 (introduce 0) ++ equationAtoms 1 (introduce 1)

theorem finite_slots (i : Fin 2) : i = 0 ∨ i = 1 := by decide +revert +kernel

abbrev base : GeneralSourceState.State where
 slots := 2
 source := Fin.val
 source_injective := fun _ _ h => Fin.ext h
 rowSource := Fin.val
 ordinary := equations
 kinds := 0
 shapes := Fin.elim0
 shapes_injective := fun i => Fin.elim0 i
 heads := fun _ => .unresolved
 intervals := []
 heads_sound := by intro model valid slot term recorded; cases recorded
 intervals_sound := by simp

abbrev view : GeneralNormalizedObservation.Snapshot base where
 kinds := 2
 shapes := shapes
 shapes_injective := by change ∀ i j, shapes i = shapes j → i = j; decide +kernel
 canonical := by intro k; rcases finite_slots k with rfl | rfl <;> simp [shapes,GeneralNormalizedObservation.Shape.Canonical]
 heads := fun k => .structural k (children k)
 checked := by
   intro slot term recorded
   have eq : introduce slot = term := Option.some.inj recorded
   subst term
   apply GeneralNormalizedObservation.Rewrites.ordinary
   · rcases finite_slots slot with rfl | rfl <;> decide +kernel
   · rcases finite_slots slot with rfl | rfl <;> decide +kernel

abbrev state : GeneralNominalState.State where
 base := base
 view := view
 constructors := constructors
 nominals := fun _ => none
 catalogue := by simp
 bodies_opaque := by simp

abbrev body : CommonNominalFullGuardedClosure.Body 2 0 := fun i =>
 if i = 0 then .record 2 (.inl 0) (.record 7 (.inl 1) .emptyRecord) else .exactEmpty
abbrev value := CommonNominalFullGuardedClosure.instantiate body Fin.elim0

abbrev model : GeneralNominalCommonBridge.Assignment := fun i =>
  (if i = 0 then value 0 else value 1,Common.rowEmpty)

theorem record_equation : Equivalent (value 0) (record 2 (value 0) (record 7 (value 1) emptyRecord)) := by
 have equation := CommonNominalFullGuardedClosure.all_parameter_sound body Fin.elim0 (0 : Fin 2)
 simpa [CommonNominalFullGuardedClosure.equation,CommonNominalFullGuardedClosure.valueReference,
    CommonNominalSyntax.Layer.map,body,record,emptyRecord] using equation

theorem exact_equation : Equivalent (value 1) exactEmpty := by
 have equation := CommonNominalFullGuardedClosure.all_parameter_sound body Fin.elim0 (1 : Fin 2)
 simpa [CommonNominalFullGuardedClosure.equation,CommonNominalFullGuardedClosure.valueReference,
    CommonNominalSyntax.Layer.map,body,exactEmpty] using equation

theorem raw_model : GeneralNominalState.Models state model := by
 refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
 · intro atom member
   change atom ∈ equations at member
   simp only [equations,equationAtoms,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl
   · exact record_equation.1
   · exact record_equation.2
   · exact exact_equation.1
   · exact exact_equation.2
 · intro slot term recorded; cases recorded
 · simp
 · simp

abbrev context : GeneralNominalCandidates.Context := ⟨state,GeneralNominalExamples.interpretation⟩
abbrev root : GeneralSourceDictionaries.Occurrence roles :=
 ⟨100,⟨0,fun _ => (0,0),[],by intro _ h; cases h⟩⟩
abbrev journal := GeneralNominalVersionedJournal232.initial context root

theorem full_model : GeneralNominalVersionedJournal232.Models journal model :=
 (GeneralNominalVersionedJournal232.initial_models ..).mpr
   ⟨raw_model,fun _ => ⟨subtype_refl _,subtype_refl _⟩⟩

def points (i : Fin 2) : GeneralRebaseStructuralOrigin270.Slots journal := i

theorem checked_window : covered journal = true := by decide +kernel

theorem checked_matrix : totalEdges journal = true := by decide +kernel

theorem computed_root : inspectRoot journal root = some true := by decide +kernel

theorem actual_root : GeneralNominalVersionedCycles232.RootCycle journal root := by
 have proof := GeneralRebaseClosedRecordDriver271.inspectRoot_sound journal ⟨model,full_model⟩ root
 rw [computed_root] at proof
 exact proof

theorem visible_self : inspect journal (.structural (.source 0) (.record [2,7]) 0) = some true := by decide +kernel

theorem distinct_leaf : inspect journal (.structural (.source 0) (.record [2,7]) 1) = some false := by decide +kernel

theorem unknown_noncanonical : inspect journal (.structural (.source 0) (.record [2,2,7]) 1) = none := by decide +kernel

end Yulang.GeneralRebaseRecordRecursiveFixture271
