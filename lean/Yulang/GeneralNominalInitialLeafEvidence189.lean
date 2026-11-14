import Yulang.GeneralNominalInitialLeafStep189
import Yulang.GeneralDictionaryCommittedEvidence

/-! Initial stable leaf selection yields the existing model-indexed source
Evidence judgment. The theorem is local to initial states and empty requests;
it does not close the general reachable-state EvidenceNode obligation. -/
namespace Yulang.GeneralNominalInitialLeafEvidence189
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {state : State roles}

theorem stable_committed
    (stable : (boundary roles).Stable registry state root)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (enabled : Installable registry state candidate support) :
    GeneralNominalFeedbackSteps.Committed state.core.erased.current candidate.packet := by
  classical
  apply Classical.byContradiction
  intro novel
  exact stable candidate.packet.site.occurrence
    (frame.occurrence_eq ▸ GeneralNominalSaturationState.Generated.root) _
    (.install candidate support enabled novel)

theorem committed_instance (candidate : Plan roles)
    (frame : Frame registry state.core root key candidate)
    (leaf : candidate.packet.declaration.requirements = []) (empty : root.demand.outputs = [])
    (committed : GeneralNominalFeedbackSteps.Committed state.core.erased.current candidate.packet)
    (model : Assignment) (valid : Models state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.core.erased.current.context model
      root key [] := by
  have ready : GeneralNominalRecursiveCandidates.RequestReady candidate.packet.registry candidate.packet.context
      candidate.packet.site.occurrence candidate.packet.declaration candidate.packet.checked candidate.packet.bounds := by
    constructor
    · simp [GeneralNominalMaterialization.RootDefined,frame.occurrence_eq,empty]
    · change (GeneralNominalPacketSupport.namedSchema candidate.packet).unknown = false
      rw [GeneralNominalHeadLeafPlan189.named_schema_empty candidate leaf (frame.occurrence_eq ▸ empty)]
  have instanceRule : GeneralDictionaryRecursiveEvidence.Instance candidate.packet.registry candidate.packet.context model
      candidate.packet.site.occurrence candidate.packet.declaration.id candidate.packet.children := by
    refine ⟨candidate.packet.declaration,?_,candidate.packet.checked,rfl,?_,candidate.packet.bounds,?_,?_,ready,rfl,?_,?_⟩
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
    (leaf : ∀ declaration ∈ registry.declarations, declaration.id = key → declaration.requirements = [])
    (empty : root.demand.outputs = []) :
    children = [] ∧ ∀ model, Models state model →
      (boundary roles).Evidence registry state model root (.node key []) := by
  obtain ⟨candidate,support,frame,kids,enabled⟩ :=
    GeneralNominalInitialLeafStep189.selected_candidate checked source selected leaf empty
  have leafPlan := leaf candidate.packet.declaration frame.visible frame.key_eq
  have committed := stable_committed stable candidate frame enabled
  refine ⟨kids.symm.trans (GeneralNominalHeadLeafPlan189.children_empty candidate leafPlan),?_⟩
  intro model valid
  exact GeneralDictionaryRecursiveEvidence.evidence_node registry state.core.erased.current.context model
    root key [] [] (committed_instance candidate frame leafPlan empty committed model valid) .nil

end Yulang.GeneralNominalInitialLeafEvidence189
