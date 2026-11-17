import Yulang.GeneralDictionaryMixedUpperSemantics234
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4000
namespace Yulang.GeneralDictionaryMixedUpperTransport234
open GeneralDictionaryMixedUpperPlan234
open GeneralDictionaryVersionedUpperSnapshot233
open GeneralNominalVersionedPlans231

theorem capture_eq : GeneralNominalVersionedFrame231.capture packet =
    GeneralNominalVersionedFrame231.capture oldPlan.packet := by
  unfold GeneralNominalVersionedFrame231.capture GeneralNominalVersionedFrame231.frame
  rw [bindings_exact,GeneralDictionaryVersionedPoint233.bindings_exact]
  rfl

theorem binder_eq : GeneralNominalVersionedFrame231.binder plan =
    GeneralNominalVersionedFrame231.binder oldPlan := by
  unfold GeneralNominalVersionedFrame231.binder
  rw [capture_eq]

theorem projection_eq (model : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalRecursiveInspection.ProjectionModels packet.context.state (GeneralNominalPacketSupport.report packet) model =
    GeneralNominalRecursiveInspection.ProjectionModels oldPlan.packet.context.state (GeneralNominalPacketSupport.report oldPlan.packet) model := by
  unfold GeneralNominalPacketSupport.report
  rw [report_exact,GeneralDictionaryOptionalCurrent229.report_exact]
  simp only [GeneralNominalRecursiveInspection.ProjectionModels,List.mem_cons,
    List.not_mem_nil,forall_eq_or_imp,forall_false,implies_true, and_true]
  rfl

theorem schema_eq (model : GeneralNominalCommonBridge.Assignment) :
    SchemaHolds plan plan.headSchema model = SchemaHolds oldPlan oldPlan.headSchema model := by
  unfold SchemaHolds
  rw [capture_eq,binder_eq]
  rfl

theorem inputs (model : GeneralNominalCommonBridge.Assignment) (old : Inputs oldPlan model) : Inputs plan model := by
  refine ⟨(GeneralDictionaryMixedUpperSemantics234.ordinary_eq model).mpr old.1,
    (projection_eq model).mpr old.2.1,old.2.2.1,?_,(schema_eq model).mpr old.2.2.2.2.1,?_,?_⟩
  · intro name needed
    rw [capture_eq,binder_eq]
    exact old.2.2.2.1 name needed
  · intro equation member nonactual
    rw [emitted_schema] at member
    cases List.mem_singleton.mp member
    exact False.elim (nonactual rfl)
  · intro clause member
    change clause ∈ [] at member
    cases member

theorem variables_eq (model : GeneralNominalCommonBridge.Assignment) :
    variables plan model = variables oldPlan model := by
  unfold variables
  rw [binder_eq,capture_eq]

theorem outputs (model : GeneralNominalCommonBridge.Assignment) (old : Outputs oldPlan model) : Outputs plan model := by
  unfold Outputs at old ⊢
  rw [emitted_schema]
  rw [GeneralDictionaryVersionedPoint233.emitted_schema] at old
  rw [variables_eq]
  exact old

theorem holds (raw : GeneralNominalState.Models packet.context.state model)
    (old : Holds oldPlan model) : Holds plan model :=
  ⟨raw,inputs model old.2.1,outputs model old.2.2⟩
end Yulang.GeneralDictionaryMixedUpperTransport234
