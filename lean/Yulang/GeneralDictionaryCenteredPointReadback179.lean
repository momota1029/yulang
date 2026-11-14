import Yulang.GeneralDictionaryCenteredNominalPoint178
import Yulang.GeneralNominalCenteredModelExtension

/-! Exact remaining centered obligation for a finite linear nominal point leaf.
The source shape and actual center identities are explicit. Raw branch validity,
head tests and captured interval bounds are derived, not assumed. This does not
construct a common model or the unrestricted ground-boundary evidence field. -/
namespace Yulang.GeneralDictionaryCenteredPointReadback179
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveInspection GeneralNominalRecursiveCandidates
open GeneralNominalSaturationState GeneralNominalCenteredSteps
open GeneralDictionaryLinearLeaf GeneralNominalLinearMaterializationFacts
open CommonNominalFullCarrier

variable {roles : Roles.RoleDecls} (plan : Plan roles)
  (shape : LinearLeafShape plan.packet.context plan.packet.site.occurrence plan.packet.declaration)

/-- Only finite actual-binder readback remains after a source model is fixed. -/
def Readback (model : GeneralNominalCommonBridge.Assignment) : Prop :=
  ∀ i : Fin shape.arity, GeneralNominalOriginTerms.Same model
    (.nominal (.source (plan.packet.context.state.base.source shape.slot))
      shape.descriptor.declaration.name i.val) (.source (plan.binder (shape.names i)))

theorem head_schema
    (centers : List.ofFn plan.input.center = [plan.packet.context.state.base.source shape.slot]) :
    plan.headSchema = headSchema plan.packet.context.state shape.slot
      shape.descriptor.declaration.name shape.names := by
  unfold Plan.headSchema
  rw [shape.query,centers]
  simp only [GeneralNominalMaterialization.schemas,List.getElem?_cons_zero,Option.getD_some]
  rw [schema_exact]
  simp [GeneralNominalMaterialization.Schema.append,headSchema]

theorem holds_iff_readback
    (located : plan.packet.bounds = [(shape.slot,shape.slot)])
    (centers : List.ofFn plan.input.center = [plan.packet.context.state.base.source shape.slot])
    (model : GeneralNominalCommonBridge.Assignment)
    (source : GeneralNominalState.Models plan.packet.context.state model)
    (input : plan.input.Holds model) : plan.Holds model ↔ Readback plan shape model := by
  have headExact := head_schema plan shape centers
  have noOutputs := no_output_binders plan.packet.declaration plan.packet.checked shape.terminal
  have reportExact := GeneralNominalLinearCaptureFacts.report_exact plan.packet.context
    plan.packet.declaration shape.slot shape.descriptor shape.recorded shape.names shape.bounds
    shape.parameters shape.query
  have captureExact : GeneralNominalPacketSupport.capture plan.packet =
      GeneralNominalAllocation.capture plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration.id
        (bindings plan.packet.context.state (GeneralNominalLinearCaptureFacts.captured
          plan.packet.context.state shape.slot shape.descriptor.declaration.name shape.names shape.bounds)) := by
    unfold GeneralNominalPacketSupport.capture Packet.bindings
    rw [located,reportExact]
  have materialized := schema_models plan.packet.context.state plan.packet.registry
    plan.packet.site.occurrence.identity plan.packet.declaration noOutputs shape.slot shape.descriptor
    shape.recorded shape.names shape.distinct shape.bounds shape.parameters model source
  have raw : plan.packet.Holds model := by
    unfold Packet.Holds
    rw [located]
    exact branch_models _ _ _ _ _ shape model source
  constructor
  · intro valid i
    have one := valid.2.2.2.1.2
    rw [headExact] at one
    exact one _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro readback
    have head : plan.SchemaHolds plan.headSchema model := by
      rw [headExact]
      refine ⟨materialized.1,?_⟩
      intro entry member
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
      exact readback i
    refine ⟨raw,input,?_,head,?_,?_,?_⟩
    · intro name needed
      have member : name ∈ plan.packet.declaration.inputNames := by
        rcases needed with member | ⟨clause,member,_⟩
        · exact member
        · rw [shape.terminal] at member; cases member
      rw [shape.inputs] at member
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
      obtain ⟨actual,seen⟩ := (readback i).1
      have fit := materialized.2.1 _ (List.mem_ofFn.mpr ⟨i,rfl⟩) |>.2 actual seen
      simp only [GeneralNominalMaterialization.VariableHolds,noOutputs,List.not_mem_nil,ite_false] at fit
      rw [← captureExact] at fit
      have same := (readback i).2.2 actual _ seen (.source _)
      exact ⟨subtype_trans fit.1 same.1,subtype_trans same.2 fit.2⟩
    · rw [GeneralNominalSharedPositive.leaf_input_schema _ shape.terminal]
      constructor <;> intro _ member <;> cases member
    · change plan.SchemaHolds (generated _ _ _ _ _ _) model
      rw [generated_empty _ _ _ _ _ shape.terminal shape.outputs]
      constructor <;> intro _ member <;> cases member
    · intro clause member
      rw [shape.terminal] at member; cases member

end Yulang.GeneralDictionaryCenteredPointReadback179
