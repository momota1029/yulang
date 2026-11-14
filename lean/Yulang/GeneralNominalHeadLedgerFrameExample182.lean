import Yulang.GeneralNominalHeadLedgerSupport182
import Yulang.GeneralNominalCenteredHeadStepDefaults
import Yulang.GeneralNominalOutputGrowth

set_option backward.isDefEq.respectTransparency false

/-! Two retained requests with the same output name inspect both targets even
when an explicit declaration contributes no output schema. This tests the
class-equation component, not reachability or a successful installation. -/
namespace Yulang.GeneralNominalHeadLedgerFrameExample182
open GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepDefaults (roles)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

def root : Occurrence roles := ⟨100,⟨0,fun _ => (1,1),[⟨0,1⟩,⟨0,2⟩],by
  intro output member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl <;> exact ⟨some (.var 0),rfl⟩⟩⟩

abbrev start := GeneralNominalCenteredSteps.initial (GeneralNominalExamples.context true) root

theorem requests_exact : requests start root = [⟨0,1⟩,⟨0,2⟩] := by
  classical
  unfold requests
  change (([GeneralNominalDemandMerging.pointSite root].filter fun site =>
    GeneralNominalSaturationState.Alias start.erased.current root.identity site.occurrence.identity).flatMap
      fun site => site.occurrence.demand.outputs) = _
  have alias : GeneralNominalSaturationState.Alias start.erased.current root.identity root.identity := .refl _
  simp only [List.filter_cons,List.filter_nil]
  change (if decide (GeneralNominalSaturationState.Alias start.erased.current root.identity root.identity)
    then [GeneralNominalDemandMerging.pointSite root] else []).flatMap
      (fun site => site.occurrence.demand.outputs) = _
  rw [show decide (GeneralNominalSaturationState.Alias start.erased.current root.identity root.identity) = true from
    decide_eq_true alias]
  rfl

def before : Assignment := fun _ => (GeneralNominalOutputGrowth.tower 0,Common.rowEmpty)
def after : Assignment := fun name =>
  (GeneralNominalOutputGrowth.tower (if name = 2 then 1 else 0),Common.rowEmpty)

theorem before_equal : EqualOutputs start root before :=
  fun _ _ _ _ _ => ⟨subtype_refl _,subtype_refl _⟩

theorem after_not_equal : ¬ EqualOutputs start root after := by
  intro equal
  have relation := equal ⟨0,1⟩ (by rw [requests_exact]; simp)
    ⟨0,2⟩ (by rw [requests_exact]; simp) rfl
  have impossible : 0 = 1 := (GeneralNominalOutputGrowth.tower_equivalent 0 1).mp relation
  cases impossible

theorem target_support : (requests start root).map (·.target) = [1,2] := by
  rw [requests_exact]
  rfl

theorem first_unchanged : before 1 = after 1 := rfl

theorem class_support_disagrees : ¬ GeneralNominalCenteredFrame179.Agree
    ((requests start root).map (·.target)) before after := by
  intro same
  exact after_not_equal ((GeneralNominalHeadLedgerFrame182.equal_outputs_iff start root same).mp before_equal)

theorem empty_associated_schema (plan : Plan roles) (empty : plan.packet.declaration.associated = []) :
    outputSchema start root plan = (⟨[],[],false⟩ : GeneralNominalMaterialization.Schema) := by
  simp [outputSchema,requests_exact,empty,Plan.schema,GeneralNominalMaterialization.generated]

theorem empty_schema_support (plan : Plan roles) (empty : plan.packet.declaration.associated = []) :
    GeneralNominalModeFrame181.schemaSources plan (outputSchema start root plan) = [] := by
  rw [empty_associated_schema plan empty]
  rfl

theorem empty_schema_agrees (plan : Plan roles) (empty : plan.packet.declaration.associated = []) :
    GeneralNominalCenteredFrame179.Agree
      (GeneralNominalModeFrame181.schemaSources plan (outputSchema start root plan)) before after := by
  rw [empty_schema_support plan empty]
  intro name member
  cases member

theorem both_targets_present (plan : Plan roles) :
    1 ∈ GeneralNominalHeadLedgerFrame182.outputSources start root plan ∧
    2 ∈ GeneralNominalHeadLedgerFrame182.outputSources start root plan := by
  constructor
  · exact GeneralNominalHeadLedgerSupport182.request_target_mem start root plan
      (show (⟨0,1⟩ : GeneralSourceState.Output) ∈ requests start root by rw [requests_exact]; simp)
  · exact GeneralNominalHeadLedgerSupport182.request_target_mem start root plan
      (show (⟨0,2⟩ : GeneralSourceState.Output) ∈ requests start root by rw [requests_exact]; simp)

end Yulang.GeneralNominalHeadLedgerFrameExample182
