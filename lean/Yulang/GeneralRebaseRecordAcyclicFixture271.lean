import Yulang.GeneralRebaseClosedRecordDriver271
import Yulang.GeneralRebaseAcyclicNominal270

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseRecordAcyclicFixture271
open GeneralDeclarationExamples (roles constructors)
open GeneralSourceState (equationAtoms)
open Core.PresenceGeneration (TyTerm)
open CommonNominalFullCarrier
open GeneralRebaseClosedRecordDriver271 (covered window totalEdges inspect inspectRoot)

abbrev shapes (k : Fin 3) : GeneralNormalizedObservation.Shape :=
 if k = 0 then .record [2,7] else if k = 1 then .record [3] else .exactEmpty

abbrev children (k : Fin 3) : Fin (shapes k).arity → Fin 3 :=
 fun i => if k = 0 ∧ i.val = 0 then 1 else 2

abbrev introduce (k : Fin 3) : TyTerm (Fin 3) := (shapes k).term (children k)

abbrev equations := equationAtoms 0 (introduce 0) ++ equationAtoms 1 (introduce 1) ++ equationAtoms 2 (introduce 2)

theorem finite_slots (i : Fin 3) : i = 0 ∨ i = 1 ∨ i = 2 := by decide +revert +kernel

abbrev base : GeneralSourceState.State where
 slots := 3
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
 kinds := 3
 shapes := shapes
 shapes_injective := by change ∀ i j, shapes i = shapes j → i = j; decide +kernel
 canonical := by intro k; rcases finite_slots k with rfl | rfl | rfl <;> simp [shapes,GeneralNormalizedObservation.Shape.Canonical]
 heads := fun k => .structural k (children k)
 checked := by
   intro slot term recorded
   have eq : introduce slot = term := Option.some.inj recorded
   subst term
   apply GeneralNormalizedObservation.Rewrites.ordinary
   · rcases finite_slots slot with rfl | rfl | rfl <;> decide +kernel
   · rcases finite_slots slot with rfl | rfl | rfl <;> decide +kernel

abbrev state : GeneralNominalState.State where
 base := base
 view := view
 constructors := constructors
 nominals := fun _ => none
 catalogue := by simp
 bodies_opaque := by simp

abbrev last : Ty := exactEmpty
abbrev middle : Ty := record 3 last emptyRecord
abbrev first : Ty := record 2 middle (record 7 last emptyRecord)

abbrev model : GeneralNominalCommonBridge.Assignment := fun i =>
  (if i = 0 then first else if i = 1 then middle else last,Common.rowEmpty)

theorem raw_model : GeneralNominalState.Models state model := by
 refine ⟨⟨?_,?_,?_⟩,?_,PresenceNormalForm.all_nil _ _⟩
 · intro atom member
   change atom ∈ equations at member
   simp only [equations,equationAtoms,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
   rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> exact subtype_refl _
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

def points (i : Fin 3) : GeneralRebaseStructuralOrigin270.Slots journal := i

theorem checked_window : covered journal = true := by decide +kernel

theorem checked_matrix : totalEdges journal = true := by decide +kernel

theorem computed_root : inspectRoot journal root = some false := by decide +kernel

theorem no_root : ¬ GeneralNominalVersionedCycles232.RootCycle journal root := by
 have proof := GeneralRebaseClosedRecordDriver271.inspectRoot_sound journal ⟨model,full_model⟩ root
 rw [computed_root] at proof
 exact proof

theorem after_projection : inspect journal (.structural (.source 0) (.record [2,7]) 1) = some false := by decide +kernel

end Yulang.GeneralRebaseRecordAcyclicFixture271
