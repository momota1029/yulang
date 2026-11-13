import Yulang.GeneralNominalReportSourceTransport
import Yulang.GeneralNominalPacketSupport
import Yulang.GeneralDictionaryRecursiveEvidence

/-! Source-preserving relocation permits the source carrier and observations to
change. Target state models are checked separately; old cached state models are
never identified with them. Only computed reports and generated schema are
compared, not the desired target branch or evidence judgment. -/
namespace Yulang.GeneralDictionarySource168Transport
open GeneralDeclarations GeneralNominalRecursiveCandidates
open GeneralNominalReportSourceTransport GeneralNominalRecursiveInspection
open GeneralNominalCommonBridge (Assignment)
open GeneralSourceDictionaries (Occurrence)

variable {roles : Roles.RoleDecls}

 theorem capture_seed (before after : GeneralNominalState.State)
    (seed : after.seed = before.seed) (registry : Registry) (root key : Nat)
    (bs : GeneralNominalAllocation.Bindings) :
    GeneralNominalAllocation.capture after registry root key bs =
      GeneralNominalAllocation.capture before registry root key bs := by
  simp only [GeneralNominalAllocation.capture,GeneralNominalAllocation.source,seed]

 theorem branch_relocated (registry : Registry) (before after : Context)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (oldBounds : List (GeneralNominalInspection.Bounds before.state))
    (newBounds : List (GeneralNominalInspection.Bounds after.state))
    (slots : Fin before.state.base.slots → Fin after.state.base.slots)
    (sources : ∀ slot, after.state.base.source (slots slot) = before.state.base.source slot)
    (seed : after.state.seed = before.state.seed)
    (reports : report after declaration newBounds = moveReport slots (report before declaration oldBounds))
    (schemas : generated registry after root declaration checked newBounds =
      generated registry before root declaration checked oldBounds)
    (model : Assignment) (current : GeneralNominalState.Models after.state model)
    (old : BranchModels registry before root declaration checked oldBounds model) :
    BranchModels registry after root declaration checked newBounds model := by
  have bs : bindings after.state (report after declaration newBounds) =
      bindings before.state (report before declaration oldBounds) := by
    rw [reports]; exact bindings_preserved slots sources _
  have checks : selfChecks after.state (report after declaration newBounds) =
      selfChecks before.state (report before declaration oldBounds) := by
    rw [reports]; exact selfChecks_preserved slots sources _
  have cap := capture_seed before.state after.state seed registry root.identity declaration.id
    (bindings before.state (report before declaration oldBounds))
  have ordinary := old.1
  unfold privateState at ordinary
  unfold BranchModels
  unfold privateState
  rw [GeneralNominalState.extend_models,GeneralNominalAllocation.propagate_models] at ordinary
  refine ⟨?_,?_,?_⟩
  · rw [GeneralNominalState.extend_models,GeneralNominalAllocation.propagate_models,bs,checks]
    refine ⟨⟨current,ordinary.1.2.1,?_⟩,ordinary.2⟩
    simpa only [GeneralNominalAllocation.merges,cap] using ordinary.1.2.2
  · rw [reports]
    exact (projections_iff slots sources _ model).mpr old.2.1
  · change GeneralNominalMaterialization.Models after.state declaration
      (GeneralNominalAllocation.capture after.state registry root.identity declaration.id
        (bindings after.state (report after declaration newBounds)))
      (report after declaration newBounds) (generated registry after root declaration checked newBounds) model
    rw [bs,cap,reports,schemas]
    exact (materialization_iff slots _ declaration _ _ model).mpr old.2.2

 theorem node_relocated (registry : Registry) (before after : Context)
    (root : Occurrence roles) (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (visible : declaration ∈ registry.declarations) (role : declaration.role = root.demand.role)
    (oldBounds : List (GeneralNominalInspection.Bounds before.state))
    (newBounds : List (GeneralNominalInspection.Bounds after.state))
    (slots : Fin before.state.base.slots → Fin after.state.base.slots)
    (sources : ∀ slot, after.state.base.source (slots slot) = before.state.base.source slot)
    (seed : after.state.seed = before.state.seed)
    (reports : report after declaration newBounds = moveReport slots (report before declaration oldBounds))
    (schemas : generated registry after root declaration checked newBounds =
      generated registry before root declaration checked oldBounds)
    (located : arguments after root = some newBounds)
    (finished : Finished (report before declaration oldBounds))
    (ready : RequestReady registry before root declaration checked oldBounds)
    (metadata : Metadata registry after)
    (children : List (Occurrence roles))
    (emitted : children = GeneralNominalAllocation.children after.state registry root declaration checked
      (bindings after.state (report after declaration newBounds)))
    (model : Assignment) (current : GeneralNominalState.Models after.state model)
    (old : BranchModels registry before root declaration checked oldBounds model)
    (payloads : List GeneralDictionaryReadback.Payload)
    (childEvidence : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry after model) children payloads) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after model root (.node declaration.id payloads) := by
  apply GeneralDictionaryRecursiveEvidence.evidence_node registry after model root declaration.id children payloads
  · refine ⟨declaration,visible,checked,rfl,role,newBounds,located,?_,?_,emitted,metadata,?_⟩
    · rw [reports]; exact (finished_iff slots _).mpr finished
    · exact ⟨ready.1,by rw [schemas]; exact ready.2⟩
    · exact branch_relocated registry before after root declaration checked oldBounds newBounds
        slots sources seed reports schemas model current old
  · exact childEvidence
end Yulang.GeneralDictionarySource168Transport
