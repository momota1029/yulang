import Yulang.GeneralRebaseTerminalTrustedWidth274

set_option maxRecDepth 12000
set_option maxHeartbeats 3600000
namespace Yulang.GeneralRebaseAllWidthRegistration275
open GeneralSourceState (equationAtoms equationAtoms_exact)
open Core.PresenceGeneration (TyTerm)
open GeneralRebaseTerminalMixedRefresh274 (widthCandidates)

open GeneralDictionaryVersionedSecondRaw233 (oldHi newLo newHi)

abbrev embed (slot : Fin 5) : Fin 8 := ⟨slot.val,by have bound := slot.isLt; omega⟩
abbrev widthSlot (slot : Fin 8) := slot = 2 ∨ slot = 5 ∨ slot = 6 ∨ slot = 7

def source (slot : Fin 8) : Nat :=
 if slot = 5 then oldHi else if slot = 6 then newLo else if slot = 7 then newHi else slot.val

def rows (slot : Fin 8) : Nat := if slot.val < 5 then slot.val else 2

theorem source_embed : ∀ slot : Fin 5, source (embed slot) = slot.val := by decide +kernel
theorem row_embed : ∀ slot : Fin 5, rows (embed slot) = slot.val := by decide +kernel
theorem source_distinct : Function.Injective source := by
 change ∀ u v : Fin 8, source u = source v → u = v
 decide +kernel

abbrev atoms : List (PresenceNormalForm.Atom (Fin 8)) :=
 equationAtoms 0 (.var 1) ++ equationAtoms 2 .emptyRecord ++ equationAtoms 3 .top ++
   [.tyLe (.var 4) (.var 2)] ++ equationAtoms 5 .emptyRecord ++ equationAtoms 6 .emptyRecord ++
   equationAtoms 7 .emptyRecord

abbrev shapes : Fin 1 → GeneralSourceState.Shape 8 := fun _ => .emptyRecord
def heads (slot : Fin 8) : GeneralSourceState.Head shapes :=
 if widthSlot slot then .structural 0 Fin.elim0 else .unresolved

theorem head_at (slot : Fin 8) (term : TyTerm (Fin 8))
 (seen : (heads slot).equation = some term) : widthSlot slot ∧ term = .emptyRecord := by
 by_cases h : widthSlot slot
 · exact ⟨h,by simpa [heads,h,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term] using seen.symm⟩
 · simp [heads,h,GeneralSourceState.Head.equation] at seen

abbrev base : GeneralSourceState.State where
 slots := 8
 source := source
 source_injective := source_distinct
 rowSource := rows
 ordinary := atoms
 kinds := 1
 shapes := shapes
 shapes_injective := fun _ _ _ => Subsingleton.elim _ _
 heads := heads
 intervals := []
 heads_sound := by
  intro assignment valid slot term seen
  obtain ⟨h,rfl⟩ := head_at slot term seen
  rcases h with h|h|h|h <;> subst slot
  · exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp
     ((PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp
       ((PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp
         ((PresenceNormalForm.all_append ..).mp valid).1).1).1).1).1).2
  · exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp
      ((PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp valid).1).1).2
  · exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp
      ((PresenceNormalForm.all_append ..).mp valid).1).2
  · exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp valid).2
 intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev viewShapes : Fin 1 → GeneralNormalizedObservation.Shape := fun _ => .record []
def viewHeads (slot : Fin 8) : GeneralNormalizedObservation.Head viewShapes 8 :=
 if widthSlot slot then .structural 0 Fin.elim0 else .deferred .unresolved

theorem view_at (slot : Fin 8) (term : TyTerm (Fin 8))
 (seen : (viewHeads slot).term = some term) : widthSlot slot ∧ term = .emptyRecord := by
 by_cases h : widthSlot slot
 · exact ⟨h,by simpa [viewHeads,h,GeneralNormalizedObservation.Head.term,
     GeneralNormalizedObservation.Shape.term,GeneralNormalizedObservation.recordTerm] using seen.symm⟩
 · simp [viewHeads,h,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at seen

abbrev view : GeneralNormalizedObservation.Snapshot base where
 kinds := 1
 shapes := viewShapes
 shapes_injective := fun _ _ _ => Subsingleton.elim _ _
 canonical := fun _ => .nil
 heads := viewHeads
 checked := by
  intro slot term recorded
  obtain ⟨width,rfl⟩ := view_at slot term recorded
  exact .head (by simp [heads,width,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term])

end Yulang.GeneralRebaseAllWidthRegistration275
