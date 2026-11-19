import Yulang.GeneralRebaseTerminalTrustedWidth274

set_option maxRecDepth 12000
set_option maxHeartbeats 3600000
namespace Yulang.GeneralRebaseWidthRegistration275
open GeneralSourceState (equationAtoms equationAtoms_exact)
open Core.PresenceGeneration (TyTerm)
open GeneralRebaseTerminalMixedRefresh274 (widthCandidates)

abbrev embed (slot : Fin 5) : Fin 6 := slot.castSucc
abbrev widthSlot (slot : Fin 6) := slot = 2 ∨ slot = 5
def source (id : Nat) (slot : Fin 6) : Nat := if slot = 5 then id else slot.val
def rows (slot : Fin 6) : Nat := if slot = 5 then 2 else slot.val

theorem source_embed (id : Nat) (slot : Fin 5) : source id (embed slot) = slot.val := by
 have small := slot.isLt
 have ne : embed slot ≠ 5 := by intro h; have e := congrArg Fin.val h; change slot.val = 5 at e; omega
 exact ite_eq_right ne

theorem row_embed (slot : Fin 5) : rows (embed slot) = slot.val := by
 have small := slot.isLt
 have ne : embed slot ≠ 5 := by intro h; have e := congrArg Fin.val h; change slot.val = 5 at e; omega
 exact ite_eq_right ne

theorem source_distinct (id : Nat) (large : 4 < id) : Function.Injective (source id) := by
 intro u v equal
 have hu := u.isLt
 have hv := v.isLt
 by_cases a : u = 5
 · by_cases b : v = 5
   · exact a.trans b.symm
   · simp [source,a,b] at equal
     have nz : v.val ≠ 5 := by intro h; exact b (Fin.ext h)
     omega
 · by_cases b : v = 5
   · simp [source,a,b] at equal
     have nz : u.val ≠ 5 := by intro h; exact a (Fin.ext h)
     omega
   · exact Fin.ext (by simpa [source,a,b] using equal)

abbrev atoms : List (PresenceNormalForm.Atom (Fin 6)) :=
 equationAtoms 0 (.var 1) ++ equationAtoms 2 .emptyRecord ++ equationAtoms 3 .top ++
   [.tyLe (.var 4) (.var 2)] ++ equationAtoms 5 .emptyRecord

abbrev shapes : Fin 1 → GeneralSourceState.Shape 6 := fun _ => .emptyRecord
def heads (slot : Fin 6) : GeneralSourceState.Head shapes :=
 if widthSlot slot then .structural 0 Fin.elim0 else .unresolved

theorem head_at (slot : Fin 6) (term : TyTerm (Fin 6))
 (seen : (heads slot).equation = some term) : widthSlot slot ∧ term = .emptyRecord := by
 by_cases h : widthSlot slot
 · exact ⟨h,by simpa [heads,h,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term] using seen.symm⟩
 · simp [heads,h,GeneralSourceState.Head.equation] at seen

abbrev base (id : Nat) (large : 4 < id) : GeneralSourceState.State where
 slots := 6
 source := source id
 source_injective := source_distinct id large
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
  rcases h with h|h <;> subst slot
  · exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp
     ((PresenceNormalForm.all_append ..).mp ((PresenceNormalForm.all_append ..).mp
       ((PresenceNormalForm.all_append ..).mp valid).1).1).1).2
  · exact (equationAtoms_exact ..).mp ((PresenceNormalForm.all_append ..).mp valid).2
 intervals_sound := by intro _ _ _ impossible; cases impossible

abbrev viewShapes : Fin 1 → GeneralNormalizedObservation.Shape := fun _ => .record []
def viewHeads (slot : Fin 6) : GeneralNormalizedObservation.Head viewShapes 6 :=
 if widthSlot slot then .structural 0 Fin.elim0 else .deferred .unresolved

theorem view_at (slot : Fin 6) (term : TyTerm (Fin 6))
 (seen : (viewHeads slot).term = some term) : widthSlot slot ∧ term = .emptyRecord := by
 by_cases h : widthSlot slot
 · exact ⟨h,by simpa [viewHeads,h,GeneralNormalizedObservation.Head.term,
     GeneralNormalizedObservation.Shape.term,GeneralNormalizedObservation.recordTerm] using seen.symm⟩
 · simp [viewHeads,h,GeneralNormalizedObservation.Head.term,GeneralNormalizedObservation.Deferred.term] at seen

abbrev view (id : Nat) (large : 4 < id) : GeneralNormalizedObservation.Snapshot (base id large) where
 kinds := 1
 shapes := viewShapes
 shapes_injective := fun _ _ _ => Subsingleton.elim _ _
 canonical := fun _ => .nil
 heads := viewHeads
 checked := by
  intro slot term recorded
  obtain ⟨width,rfl⟩ := view_at slot term recorded
  exact .head (by simp [heads,width,GeneralSourceState.Head.equation,GeneralSourceState.Shape.term])

end Yulang.GeneralRebaseWidthRegistration275
