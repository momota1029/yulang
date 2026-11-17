import Yulang.GeneralNominalVersionedSupportedCompletion237
import Yulang.GeneralNominalVersionedEffects231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedSupportedActual237
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters GeneralNominalSaturationState
open GeneralNominalVersionedSupportedCompletion237 (extended raw_preserves)
variable (names : List Nat) (state : GeneralNominalVersionedJournal232.State roles) (plan : Plan roles) (model : Assignment)

theorem legacy_kept (r d purpose owner : Nat) :
    extended names state plan model (GeneralNominalCenters.fresh plan.packet.context.state.seed r d purpose owner 0) =
      model (GeneralNominalCenters.fresh plan.packet.context.state.seed r d purpose owner 0) := by
  apply GeneralNominalSelectiveEquationRealization236.outside
  intro entry member
  obtain ⟨name,_,_,rfl | rfl⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp member
  all_goals
    exact GeneralNominalAggregateVersion231.not_legacy_slot plan.packet.context.state.seed plan.packet.site.occurrence.identity
      plan.packet.declaration.id _ name plan.packet.bindings r d purpose owner

theorem output_kept (name : Nat) :
    extended names state plan model ((GeneralNominalVersionedFrame231.capture plan.packet).outputs name) =
      model ((GeneralNominalVersionedFrame231.capture plan.packet).outputs name) :=
  legacy_kept names state plan model plan.packet.site.occurrence.identity plan.packet.declaration.id 2 name

theorem binder_kept (name : Nat) :
    extended names state plan model (GeneralNominalVersionedFrame231.binder plan name) =
      model (GeneralNominalVersionedFrame231.binder plan name) := by
  unfold GeneralNominalVersionedFrame231.binder
  by_cases output : name ∈ plan.packet.declaration.outputNames
  · simp only [output,ite_true]
    exact output_kept names state plan model name
  · simp only [output,ite_false]
    have legacy := legacy_kept names state plan model plan.packet.site.occurrence.identity plan.packet.declaration.id 8 name
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
          have linked := GeneralNominalReportSupport237.report_endpoints plan.packet.context.state
            (GeneralNominalPacketSupport.report plan.packet)
          have supported := GeneralNominalAllocationSupport.occurrences_endpoints linked name bounds
            (by change bounds ∈ GeneralNominalAllocation.occurrences plan.packet.bindings name; rw [found]; exact List.mem_singleton_self _)
          exact raw_preserves names state plan model _ supported.2
        · simpa only [point,ite_false] using legacy
      | cons next tail =>
        have different := GeneralNominalAggregateVersion231.distinct_purpose plan.packet.context.state.seed
          plan.packet.site.occurrence.identity plan.packet.declaration.id 0 1 name plan.packet.bindings plan.packet.bindings (by decide)
        simpa only [found,different,ite_false] using legacy

theorem actual_variables (name : Nat) :
    GeneralNominalVersionedPlans231.variables plan (extended names state plan model) .actual name =
      GeneralNominalVersionedPlans231.variables plan model .actual name := by
  unfold GeneralNominalVersionedPlans231.variables
  split <;> exact congrArg Prod.fst (binder_kept names state plan model name)

theorem actual_expression
    (expression : GeneralNominalCenteredHeadMatExpressions.Expr) :
    GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalVersionedPlans231.variables plan (extended names state plan model)) .actual expression =
      GeneralNominalCenteredHeadMatExpressions.value (GeneralNominalVersionedPlans231.variables plan model) .actual expression :=
  GeneralNominalVersionedEffects231.actual_value _ _ (actual_variables names state plan model) expression
end Yulang.GeneralNominalVersionedSupportedActual237
