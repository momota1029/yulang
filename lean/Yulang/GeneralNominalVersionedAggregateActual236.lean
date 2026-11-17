import Yulang.GeneralNominalVersionedSemanticCompletion236
import Yulang.GeneralNominalVersionedEffects231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedAggregateActual236
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters GeneralNominalSaturationState
open GeneralNominalVersionedSemanticCompletion236 (extended Fresh preserves)
variable (packet : Packet roles) (model : Assignment)

theorem legacy_kept (r d purpose owner : Nat) :
    extended packet model (GeneralNominalCenters.fresh packet.context.state.seed r d purpose owner 0) =
      model (GeneralNominalCenters.fresh packet.context.state.seed r d purpose owner 0) := by
  apply GeneralNominalFiniteEquationRealization236.outside
  intro entry member
  obtain ⟨name,_,_,rfl | rfl⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp member
  all_goals
    exact GeneralNominalAggregateVersion231.not_legacy_slot packet.context.state.seed packet.site.occurrence.identity
      packet.declaration.id _ name packet.bindings r d purpose owner

theorem output_kept (name : Nat) :
    extended packet model ((GeneralNominalVersionedFrame231.capture packet).outputs name) =
      model ((GeneralNominalVersionedFrame231.capture packet).outputs name) :=
  legacy_kept packet model packet.site.occurrence.identity packet.declaration.id 2 name

theorem binder_kept (plan : Plan roles) (fresh : Fresh plan.packet) (name : Nat) :
    extended plan.packet model (GeneralNominalVersionedFrame231.binder plan name) =
      model (GeneralNominalVersionedFrame231.binder plan name) := by
  unfold GeneralNominalVersionedFrame231.binder
  by_cases output : name ∈ plan.packet.declaration.outputNames
  · simp only [output,ite_true]
    exact output_kept plan.packet model name
  · simp only [output,ite_false]
    have legacy := legacy_kept plan.packet model plan.packet.site.occurrence.identity plan.packet.declaration.id 8 name
    unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame GeneralNominalVersionedAllocation231.capture
    cases found : GeneralNominalAllocation.occurrences plan.packet.bindings name with
    | nil =>
      have different := GeneralNominalAggregateVersion231.distinct_purpose plan.packet.context.state.seed
        plan.packet.site.occurrence.identity plan.packet.declaration.id 0 1 name plan.packet.bindings plan.packet.bindings (by decide)
      simpa only [found,different,ite_false] using legacy
    | cons bounds rest =>
      cases rest with
      | nil =>
        simp only [found]
        by_cases point : bounds.1 = bounds.2
        · simp only [point,ite_true]
          have linked := GeneralNominalSemanticRawFrame236.report_endpoints plan.packet.context.state
            (GeneralNominalPacketSupport.report plan.packet)
          have supported := GeneralNominalAllocationSupport.occurrences_endpoints linked name bounds
            (by change bounds ∈ GeneralNominalAllocation.occurrences plan.packet.bindings name; rw [found]; exact List.mem_singleton_self _)
          exact preserves plan.packet model fresh _ supported.2
        · simpa only [point,ite_false] using legacy
      | cons next tail =>
        have different := GeneralNominalAggregateVersion231.distinct_purpose plan.packet.context.state.seed
          plan.packet.site.occurrence.identity plan.packet.declaration.id 0 1 name plan.packet.bindings plan.packet.bindings (by decide)
        simpa only [found,different,ite_false] using legacy

theorem actual_variables (plan : Plan roles) (fresh : Fresh plan.packet) (name : Nat) :
    GeneralNominalVersionedPlans231.variables plan (extended plan.packet model) .actual name =
      GeneralNominalVersionedPlans231.variables plan model .actual name := by
  unfold GeneralNominalVersionedPlans231.variables
  split <;> exact congrArg Prod.fst (binder_kept model plan fresh name)

theorem actual_expression (plan : Plan roles) (fresh : Fresh plan.packet)
    (expression : GeneralNominalCenteredHeadMatExpressions.Expr) :
    GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalVersionedPlans231.variables plan (extended plan.packet model)) .actual expression =
      GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalVersionedPlans231.variables plan model) .actual expression :=
  GeneralNominalVersionedEffects231.actual_value _ _ (actual_variables model plan fresh) expression
end Yulang.GeneralNominalVersionedAggregateActual236
