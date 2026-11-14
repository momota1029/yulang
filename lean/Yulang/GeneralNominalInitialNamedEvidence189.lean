import Yulang.GeneralNominalSingleVariableModels189
import Yulang.GeneralNominalInitialLeafEvidence189

/-! Named-output leaf installation feeds the unchanged model-indexed Evidence
field. This allows nonempty root requests; the single-variable head and actual
output-schema readiness are retained explicitly. -/
namespace Yulang.GeneralNominalInitialNamedEvidence189
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {state : State roles}

theorem initial_schema (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (leaf : candidate.packet.declaration.requirements = []) :
    GeneralNominalPacketSupport.namedSchema candidate.packet = outputSchema state.core root candidate := by
  have requestEq : requests state.core root = root.demand.outputs := by
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    exact GeneralNominalHeadInitialEffects188.initial_requests context
  rw [GeneralNominalSingleVariableModels189.leaf_named_schema candidate leaf]
  simp only [outputSchema,requestEq,Plan.schema,GeneralNominalMaterialization.rootRequests,frame.occurrence_eq]

theorem initial_request_ready (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (leaf : candidate.packet.declaration.requirements = [])
    (ready : EffectsReady state.core root candidate) :
    GeneralNominalRecursiveCandidates.RequestReady candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.checked candidate.packet.bounds := by
  constructor
  · intro output member
    apply ready.1 output
    rw [frame.occurrence_eq] at member
    obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
    subst state
    rw [GeneralNominalHeadInitialEffects188.initial_requests]
    exact member
  · change (GeneralNominalPacketSupport.namedSchema candidate.packet).unknown = false
    rw [initial_schema source candidate frame leaf]
    exact ready.2

theorem committed_instance (source : (boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (leaf : candidate.packet.declaration.requirements = [])
    (ready : EffectsReady state.core root candidate)
    (committed : GeneralNominalFeedbackSteps.Committed state.core.erased.current candidate.packet)
    (model : Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model root key [] := by
  have instanceRule : GeneralDictionaryRecursiveEvidence.Instance candidate.packet.registry candidate.packet.context model
      candidate.packet.site.occurrence candidate.packet.declaration.id candidate.packet.children := by
    refine ⟨candidate.packet.declaration,?_,candidate.packet.checked,rfl,?_,candidate.packet.bounds,?_,?_,
      initial_request_ready source candidate frame leaf ready,rfl,?_,?_⟩
    · simpa only [frame.registry_eq] using frame.visible
    · simpa only [frame.occurrence_eq] using frame.role_eq
    · rw [frame.occurrence_eq]
      exact frame.located
    · have prepared := frame.prepared
      rw [← frame.context_eq] at prepared
      obtain ⟨_,_,_,bounds,found,finished,_⟩ := prepared
      have same := Option.some.inj (frame.located.symm.trans found)
      subst bounds
      exact finished
    · simpa only [frame.registry_eq,frame.context_eq] using frame.prepared.1
    · exact committed.1 model valid.1.1
  simpa only [frame.registry_eq,frame.context_eq,frame.occurrence_eq,frame.key_eq,
    GeneralNominalHeadLeafPlan189.children_empty candidate leaf] using instanceRule

theorem stable_selected_evidence (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (stable : (boundary roles).Stable registry state root)
    (selected : Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (slot : Fin candidate.packet.context.state.base.slots)
    (query : GeneralNominalInspection.queries candidate.packet.context.state
      candidate.packet.context.interpretation candidate.packet.declaration = [.variables [name]])
    (bounds : candidate.packet.bounds = [(slot,slot)])
    (names : candidate.packet.declaration.inputNames = [name])
    (leaf : candidate.packet.declaration.requirements = [])
    (ready : EffectsReady state.core root candidate) :
    ∀ model, Models state model → (boundary roles).Evidence registry state model root (.node key []) := by
  obtain ⟨support,enabled⟩ := GeneralNominalSingleVariableModels189.selected_named_installable
    checked source selected candidate frame slot query bounds names leaf ready
  have committed := GeneralNominalInitialLeafEvidence189.stable_committed stable candidate frame enabled
  intro model valid
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry state.core.erased.current.context model
    root key [] [] (committed_instance source candidate frame leaf ready committed model valid) .nil

end Yulang.GeneralNominalInitialNamedEvidence189
