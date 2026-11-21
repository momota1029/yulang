import Yulang.GeneralWherePhysicalCurrentRead319

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 28000000
namespace Yulang.GeneralWherePhysicalTicket319
open CommonNominalFullCarrier
open GeneralWhereOriginSingleSource318 (registry declaration checked oldPlan)
open GeneralWhereOriginSingleModel318 (previousHi)
open GeneralWhereOriginSingleCells318 (hi)
open GeneralWherePhysicalCurrentRead319 (plan low high address_lo address_hi reads)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWherePhysicalPast319 (point savedHi)
open GeneralWherePhysicalFresh319 (upperSlot)
open GeneralWherePhysicalActive319 (active ctx active_models)
open GeneralWhereOriginInstall318 (RawTicket)
open GeneralWhereVersionInstall317 (Models)
open GeneralNominalVersionedPlans231 (variables)
open GeneralNominalVersionedExpressionFrame236 (variable_value)
open GeneralDictionaryBinderLocations (sourceSlot)
open GeneralNominalCommonBridge (Assignment)
open GeneralVersionedEndpointAddress315 (atCell)
open GeneralWhereVersionCase317 (expr)

theorem raw_ticket : RawTicket updated plan ctx := by
  intro n valid holds
  have lower := holds.rows low.row low.written.1
  change Equivalent (n (atCell plan .lower GeneralLiveCompoundRegistry316.otherChild.id 0 expr)).1
      (variant 0 (variables plan n .lower 0)) at lower
  rw [address_lo,variable_value,reads.1] at lower
  apply (active_models n).mpr
  exact (GeneralWherePhysicalFresh319.raw_models n).mpr ⟨valid.1.1.1,lower⟩

theorem historical_row (n : Assignment) (valid : Models updated n) :
    previousHi.row.Holds (variables oldPlan n) n := by
  exact (valid.2 oldPlan List.mem_cons_self).1.rows _ previousHi.written.1

theorem target_eq : high.row.target = previousHi.row.target :=
  address_hi.trans (by rfl)

/-- The reused row is witnessed by the actual prior installed record after the
real nominal refresh, not inferred from raw slot membership. -/
theorem current_upper_stored (n : Assignment) (valid : Models updated n) :
    high.row.Holds (variables plan n) n := by
  have visible : declaration ∈ registry.declarations := List.mem_cons_self
  exact (GeneralWhereVersionStoredRow317.same_target_iff (p := plan) (q := oldPlan)
    checked rfl rfl rfl visible visible high.written.2 previousHi.written.2 target_eq n).mpr
    (historical_row n valid)

theorem upper_physical :
    sourceSlot point.base hi = some savedHi ∧
    sourceSlot active.base hi = some upperSlot ∧
    upperSlot = GeneralWherePhysicalIndex319.old 1 savedHi :=
  ⟨GeneralWherePhysicalPast319.point_slots.2,GeneralWherePhysicalFresh319.final_slots.1,rfl⟩

end Yulang.GeneralWherePhysicalTicket319
