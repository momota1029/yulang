import Yulang.GeneralRebaseFiniteReport259
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralVersionReportProjection259
open GeneralDictionaryVersionLoopBook239 (context packet allocations reservations atoms)
open GeneralDictionaryVersionLoopFamilyBase238 (original anchor)
open GeneralNominalRecursiveInspection (Report)

def projection (slot : Fin (n+4)) : Fin 4 := if small : slot.val < 4 then ⟨slot.val,small⟩ else 2

theorem original_projection (n : Nat) (slot : Fin 4) : projection (original n slot) = slot := by
 apply Fin.ext
 simp only [projection,original]
 split
 · rfl
 · rename_i impossible; exact False.elim (impossible slot.isLt)

theorem anchor_projection (n : Nat) : projection (anchor n) = 2 := by
 apply Fin.ext
 cases n with
 | zero => decide
 | succ n => simp only [projection,anchor,Nat.succ_ne_zero,ite_false]; split <;> omega

abbrev bounds (n : Nat) (pair : GeneralNominalInspection.Bounds (context n).state) :
 GeneralNominalInspection.Bounds (context 0).state := (projection pair.1,projection pair.2)

def transport (n : Nat) (report : Report (context n).state) : Report (context 0).state where
 captures := report.captures.map fun capture => ⟨capture.name,bounds n capture.bounds,capture.origin⟩
 inspected := report.inspected.map (bounds n)
 checked := report.checked.map (bounds n)
 blocked := report.blocked.map (bounds n)
 conflicts := report.conflicts.map (bounds n)
 arity := report.arity
 anchors := report.anchors.map fun anchor => (anchor.1,bounds n anchor.2)
 tests := report.tests

theorem actual_report (n : Nat) : transport n (GeneralNominalPacketSupport.report (packet n)) =
 GeneralNominalPacketSupport.report (packet 0) := by
 have exactReport (k : Nat) : GeneralNominalPacketSupport.report (packet k) =
 GeneralDictionaryVersionLoopFamilyPacket238.calculated k (allocations k) (reservations k) (atoms k) :=
 GeneralDictionaryVersionLoopFamilyPacket238.report_exact ..
 rw [exactReport n,exactReport 0]
 unfold transport
 simp only [GeneralDictionaryVersionLoopFamilyPacket238.calculated,List.map_cons,List.map_nil,bounds,
   original_projection,anchor_projection]
 rfl
end Yulang.GeneralVersionReportProjection259
