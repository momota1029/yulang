import Yulang.GeneralDeclarativeStoppedDepthExact341
import Yulang.GeneralDeclarativeStoppedPairedDisplay341

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 14500000

namespace Yulang.Cycle341OriginAudit
open GeneralDeclarativeOrigins321 (restriction backed_iff)
open GeneralDeclarativeStoppedDepthView341 (support outRow scalar no_promoted_targets)
open GeneralDeclarativeStoppedDepthWitness341 (current)
open GeneralDeclarativeStoppedDepthProjection341 (extend)
open GeneralNominalCommonBridge (Assignment)

/-- The latest witness on the actual stopped C285 view does not promote
either the generated output RHS or a solver-observed scalar into an
authored source row, even after the actual 4/5 endpoint expansion. -/
theorem keeps_origins (done : Nat → Prop) :
    outRow ∉ (restriction (current done)).equations ∧
      scalar 0 ∉ (restriction (current done)).equations := by
  have old (row) (new : row ∈ (restriction (current done)).equations) :
      row ∈ (restriction (support done)).equations := by
    obtain ⟨origin,used,ready⟩ := (backed_iff (current done) _).mp new
    exact (backed_iff (support done) _).mpr ⟨origin,used,ready⟩
  exact ⟨fun h => (no_promoted_targets done).1 (old _ h),fun h => (no_promoted_targets done).2 (old _ h)⟩

theorem row_coordinates_unchanged (m : Assignment) (name : Nat) :
    (extend m name).2 = (m name).2 := by
  unfold extend
  split <;> rfl

end Yulang.Cycle341OriginAudit

#print axioms Yulang.Cycle341OriginAudit.keeps_origins
#print axioms Yulang.Cycle341OriginAudit.row_coordinates_unchanged
