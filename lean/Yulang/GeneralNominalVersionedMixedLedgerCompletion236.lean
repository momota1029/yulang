import Yulang.GeneralNominalVersionedMixedSelectiveCompletion236
import Yulang.GeneralNominalVersionedAggregateLedger236
/-! Finite historical lookup discharges the protected aggregate equations.
No reachability-wide coverage or complete materialization is asserted. -/
namespace Yulang.GeneralNominalVersionedMixedLedgerCompletion236
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedMixedFreshCompletion236 (pool)
open GeneralNominalVersionedMixedSelectiveCompletion236 (extended Reused)
variable {roles : Roles.RoleDecls}
theorem reused {state : State roles} {plan : Plan roles} {model : Assignment}
    (covered : GeneralNominalVersionedAggregateLedger236.ProtectedCovered (pool state plan) state plan.packet)
    (valid : Models state model) : Reused state plan model :=
  GeneralNominalVersionedAggregateLedger236.protected_equations covered valid

theorem simultaneous (state : State roles) (plan : Plan roles) (model : Assignment)
    (current : plan.packet.context = state.core.erased.current.context)
    (covered : GeneralNominalVersionedAggregateLedger236.ProtectedCovered (pool state plan) state plan.packet) (valid : Models state model)
    (cross : GeneralNominalAllocation.Compatible plan.packet.bindings model)
    (self : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)))
    (projection : GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) model)
    (live : GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan model) :
    Models state (extended state plan model) ∧
      GeneralNominalVersionedPlans231.HeadModels plan.packet (extended state plan model) ∧
      GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan (extended state plan model) :=
  GeneralNominalVersionedMixedSelectiveCompletion236.simultaneous state plan model current
    (reused covered valid) valid cross self projection live
end Yulang.GeneralNominalVersionedMixedLedgerCompletion236
