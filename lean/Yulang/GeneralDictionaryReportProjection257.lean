import Yulang.GeneralDictionaryPointProjection257
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryReportProjection257
open GeneralDictionaryLooseIterationBook240 (context packet atoms allocations reservations)
open GeneralDictionaryLooseFamilyBase240 (anchor original)
open GeneralDictionaryFiveSlot257 (projection)
open GeneralNominalRecursiveInspection (Report Capture)

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

theorem anchor_projected (n : Nat) : projection (anchor n) = (2 : Fin 5) := by
 cases n with
 | zero => rfl
 | succ n =>
   rw [GeneralDictionaryProjectionBoundary257.anchor_collapsed,
     GeneralDictionaryFiveSlot257.original_projection]

theorem actual_report (n : Nat) :
 transport n (GeneralNominalPacketSupport.report (packet n)) =
 GeneralNominalPacketSupport.report (packet 0) := by
 have exactReport (k : Nat) : GeneralNominalPacketSupport.report (packet k) =
   GeneralDictionaryLooseFamilyPacket240.calculated k (allocations k) (reservations k) (atoms k) :=
   GeneralDictionaryLooseFamilyPacket240.report_exact ..
 rw [exactReport n,exactReport 0]
 unfold transport
 simp only [GeneralDictionaryLooseFamilyPacket240.calculated,List.map_cons,List.map_nil,bounds,
   GeneralDictionaryFiveSlot257.original_projection,anchor_projected]
 rfl

theorem origins_unchanged (n : Nat) :
 ((GeneralNominalPacketSupport.report (packet n)).captures.map (fun capture => capture.origin)) =
 ((GeneralNominalPacketSupport.report (packet 0)).captures.map (fun capture => capture.origin)) := by
 have same := congrArg (fun report : Report (context 0).state => report.captures.map (fun capture => capture.origin)) (actual_report n)
 simpa only [transport,List.map_map,Function.comp_def] using same
end Yulang.GeneralDictionaryReportProjection257
