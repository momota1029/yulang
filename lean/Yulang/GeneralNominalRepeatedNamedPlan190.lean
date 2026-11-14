import Yulang.GeneralNominalInitialNamedEvidence189
import Yulang.GeneralNominalLinearNamedPlan189
import Yulang.GeneralNominalLeafWitnessInstall190
import Yulang.GeneralNominalRepeatedPointRepair190

/-! Full variable-head leaf plans can use repaired private head models.
Repeated names are allowed. Private head, centered head and named output
judgments must all hold in the same assignment. -/
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalRepeatedNamedPlan190
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalSingleVariableModels189 (leaf_named_schema actual_schema_raw installed_outputs)
variable {roles : Roles.RoleDecls}

private theorem linear_report (state : GeneralNominalState.State)
    (entries : List (Nat × Fin state.base.slots)) (index : Nat) :
    inspectMany state (entries.map fun entry => .variables [entry.1])
      (entries.map fun entry => (entry.2,entry.2)) (fun _ => none) index =
    { captures := entries.map (fun entry => ⟨entry.1,(entry.2,entry.2),none⟩),
      checked := entries.map (fun entry => (entry.2,entry.2)) } := by
  induction entries generalizing index with
  | nil => simp [inspectMany]
  | cons head tail ih =>
      simp [inspectMany,inspect,Report.append,ih]

theorem named_plan (candidate : Plan roles) (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (leaf : candidate.packet.declaration.requirements = [])
    (model : Assignment)
    (branch : GeneralNominalCenteredHeadCandidates.HeadModels candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.bounds model)
    (head : HeadEquations candidate model)
    (outputs : candidate.SchemaHolds (GeneralNominalPacketSupport.namedSchema candidate.packet) model) :
    candidate.Holds model := by
  have actual : GeneralDictionaryActualSchema.ActualOnly (GeneralNominalPacketSupport.namedSchema candidate.packet) := by
    rw [leaf_named_schema candidate leaf]
    exact GeneralDictionaryActualSchema.root_generated_actual candidate.packet.context.state candidate.packet.context.interpretation candidate.packet.declaration candidate.packet.site.occurrence
  have scope : ∀ entry ∈ (GeneralNominalPacketSupport.namedSchema candidate.packet).variables,
      entry.name ∈ candidate.packet.declaration.inputNames ∨ entry.name ∈ candidate.packet.declaration.outputNames := by
    rw [leaf_named_schema candidate leaf]
    exact GeneralDictionaryActualSchemaScope.root_generated_scoped _ _ _ _ candidate.packet.checked.scope
  have origins : ∀ captured ∈ (GeneralNominalPacketSupport.report candidate.packet).captures, captured.origin = none := by
    intro captured member
    have report := linear_report candidate.packet.context.state entries 0
    simp only [GeneralNominalPacketSupport.report,GeneralNominalRecursiveCandidates.report,
      query,bounds,report] at member
    obtain ⟨entry,_,rfl⟩ := List.mem_map.mp member
    rfl
  have raw := actual_schema_raw candidate _ model outputs actual scope head.2.1 origins
  refine ⟨⟨branch.1,branch.2,raw⟩,head.1,?_,head.2.2,?_,outputs,?_⟩
  · intro used member
    rcases member with member | needed
    · exact head.2.1 used member
    · simp [GeneralNominalSharedCaptures.Needed,leaf] at needed
  · rw [GeneralNominalHeadLeafPlan189.input_schema_empty candidate leaf]
    simp [Plan.SchemaHolds]
  · simp [leaf]


/-- A selected named-output witness is repaired only at fresh merge extrema.
Current source values, all actual binders and named outputs are preserved. -/
theorem selected_named_plan
    {registry : Registry} {root : Occurrence roles} {state : State roles}
    (checked : Checked registry)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (selected : GeneralNominalCenteredHeadWFBoundary.Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (names : candidate.packet.declaration.inputNames = entries.map Prod.fst)
    (leaf : candidate.packet.declaration.requirements = [])
    (ready : EffectsReady state.core root candidate) :
    ∃ model, Models state model ∧ candidate.Holds model ∧
      OutputEquations state.core root candidate model := by
  obtain ⟨model,valid,head,outputs⟩ :=
    GeneralNominalInitialFrameUnique189.selected_frame_model checked state source selected candidate frame ready
  let repaired := GeneralNominalRepeatedPointRepair190.repair candidate model
  have current := GeneralNominalRepeatedPointRepair190.repair_models source candidate frame model valid
  have newHead := GeneralNominalRepeatedPointRepair190.repair_head_equations source candidate frame entries query bounds names model valid head
  have branch := GeneralNominalRepeatedPointRepair190.repair_head_models source candidate frame entries query bounds names model valid head
  have newOutputs := GeneralNominalRepeatedPointRepair190.repair_outputs source candidate frame leaf model outputs
  have schemaEq := GeneralNominalInitialNamedEvidence189.initial_schema source candidate frame leaf
  refine ⟨repaired,current,named_plan candidate entries query bounds leaf repaired branch newHead ?_,newOutputs⟩
  rw [schemaEq]
  exact newOutputs.1

theorem selected_named_installable
    {registry : Registry} {root : Occurrence roles} {state : State roles}
    (checked : Checked registry)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (selected : GeneralNominalCenteredHeadWFBoundary.Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (entries : List (Nat × Fin candidate.packet.context.state.base.slots))
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = entries.map fun entry => .variables [entry.1])
    (bounds : candidate.packet.bounds = entries.map fun entry => (entry.2,entry.2))
    (names : candidate.packet.declaration.inputNames = entries.map Prod.fst)
    (leaf : candidate.packet.declaration.requirements = [])
    (ready : EffectsReady state.core root candidate) :
    ∃ support, GeneralNominalCenteredHeadStepKernel.Installable registry state candidate support :=
  GeneralNominalLeafWitnessInstall190.installable_of_named_witness source selected candidate frame leaf ready
    (selected_named_plan checked source selected candidate frame entries query bounds names leaf ready)

end Yulang.GeneralNominalRepeatedNamedPlan190
