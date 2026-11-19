import Yulang.GeneralRebaseNestedRecordQuery271
import Yulang.GeneralRebaseRecordQueryCases271
import Yulang.GeneralRebaseVariantNominalFixture270

namespace Yulang.GeneralRebaseNestedQueryFixture271
open GeneralNominalRecursiveInspection (Origin)
open GeneralRebaseNestedRecordQuery271 (resolve follow next inspect inspect_sound)
open GeneralNominalVersionedCycles232 (Cyclic)

namespace Record
open GeneralRebaseRecordRecursiveFixture271 (journal points model full_model)
open GeneralRebaseRecordQueryCases271.Recursive (hiddenRepeat)

def read : Origin → Origin := fun o => .structural o (.record [7,2,2]) 1

def chain : Nat → Origin
 | 0 => .source 0
 | n+1 => read (chain n)

theorem one_more : next journal (points 0) (.structural (.record [7,2,2]) 1) = .child (points 0) := by decide +kernel

theorem every_depth_rep (n : Nat) : resolve journal (chain n) = .child (points 0) := by
 induction n with
 | zero => decide +kernel
 | succ n ih =>
   change follow journal (.structural (.record [7,2,2]) 1) (resolve journal (chain n)) = _
   rw [ih]
   exact one_more

theorem every_depth_computed (n : Nat) : inspect journal (chain n) = some true := by
 unfold inspect
 rw [every_depth_rep]
 change GeneralRebaseRecordRouting271.inspect journal (.source 0) = some true
 decide +kernel

theorem every_depth_actual (n : Nat) : Cyclic journal (chain n) := by
 have sound := inspect_sound journal ⟨model,full_model⟩ (chain n)
 rw [every_depth_computed] at sound
 exact sound

def hiddenParent : Origin := .structural hiddenRepeat (.record [2,7]) 0

theorem conservative : resolve journal hiddenParent = .unknown := by decide +kernel

end Record

namespace Mixed
open GeneralRebaseVariantNominalFixture270 (journal points model full_model)

def mixed : Nat → Origin
 | 0 => .source 0
 | n+1 => .nominal (.structural (mixed n) (.variant 7) 0) 0 0

theorem variant_move : next journal (points 0) (.structural (.variant 7) 0) =
 .child (points 1) := by decide +kernel

theorem nominal_move : next journal (points 1) (.nominal 0 0) =
 .child (points 0) := by decide +kernel

theorem every_depth_rep (n : Nat) : resolve journal (mixed n) = .child (points 0) := by
 induction n with
 | zero => decide +kernel
 | succ n ih =>
   change follow journal (.nominal 0 0)
     (follow journal (.structural (.variant 7) 0) (resolve journal (mixed n))) = _
   rw [ih]
   change follow journal (.nominal 0 0) (next journal (points 0) (.structural (.variant 7) 0)) = _
   rw [variant_move]
   exact nominal_move

theorem every_depth_computed (n : Nat) : inspect journal (mixed n) = some true := by
 unfold inspect
 rw [every_depth_rep]
 change GeneralRebaseRecordRouting271.inspect journal (.source 0) = some true
 decide +kernel

theorem every_depth_actual (n : Nat) : Cyclic journal (mixed n) := by
 have sound := inspect_sound journal ⟨model,full_model⟩ (mixed n)
 rw [every_depth_computed] at sound
 exact sound

end Mixed
end Yulang.GeneralRebaseNestedQueryFixture271
