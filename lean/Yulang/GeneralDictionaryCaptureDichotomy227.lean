import Yulang.GeneralDictionaryPointCaptureSupport227

namespace Yulang.GeneralDictionaryCaptureDichotomy227
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticTrace227 GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalQueryProvenance183 (headInspection)
variable {roles : Roles.RoleDecls}

theorem top_not_bottom : ¬ CommonNominalFullCarrier.Subtype .top .bottom := by
  intro bad
  have impossible := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp (bad 0)
    0 ⟨fun _ => .bottom,fun _ => []⟩ (.role 0) (by trivial)
  exact impossible

/-- Even for two different endpoints, an observed capture cannot have both
nonzero endpoints outside the semantic footprint. -/
theorem endpoint_mem
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (captured : Capture plan.packet.context.state)
    (member : captured ∈ (headInspection plan).captures)
    (located : captured.origin = some origin)
    (lower : plan.packet.context.state.base.source captured.bounds.1 ≠ 0)
    (upper : plan.packet.context.state.base.source captured.bounds.2 ≠ 0)
    (observed : Observes model origin actual) :
    plan.packet.context.state.base.source captured.bounds.1 ∈ pool ∨
    plan.packet.context.state.base.source captured.bounds.2 ∈ pool := by
  classical
  by_cases one : plan.packet.context.state.base.source captured.bounds.1 ∈ pool
  · exact Or.inl one
  by_cases two : plan.packet.context.state.base.source captured.bounds.2 ∈ pool
  · exact Or.inr two
  exact False.elim (top_not_bottom (CommonNominalFullCarrier.subtype_trans
    (GeneralDictionaryPointCaptureSupport227.absent_lower_top trace plan frame model valid schema captured member located lower one observed)
    (GeneralDictionaryPointCaptureSupport227.absent_upper_bottom trace plan frame model valid schema captured member located upper two observed)))
/-- The schema itself supplies the observation; no independent observation
or packet-satisfiability premise is required. -/
theorem captured_endpoint_mem
    (trace : Footprint registry context root state pool)
    (plan : Plan roles)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (model : Assignment) (valid : Models state model)
    (schema : plan.SchemaHolds plan.headSchema model)
    (captured : Capture plan.packet.context.state)
    (member : captured ∈ (headInspection plan).captures)
    (lower : plan.packet.context.state.base.source captured.bounds.1 ≠ 0)
    (upper : plan.packet.context.state.base.source captured.bounds.2 ≠ 0) :
    plan.packet.context.state.base.source captured.bounds.1 ∈ pool ∨
    plan.packet.context.state.base.source captured.bounds.2 ∈ pool := by
  obtain ⟨origin,located,used⟩ := GeneralNominalCenteredCaptureSchema.many_capture
    plan.packet.context.state _ plan.packet.bounds _ 0 captured member
  obtain ⟨actual,observed⟩ := (schema.2 ⟨captured.name,origin,.actual⟩ used).1
  exact endpoint_mem trace plan frame model valid schema captured member located lower upper observed

end Yulang.GeneralDictionaryCaptureDichotomy227
