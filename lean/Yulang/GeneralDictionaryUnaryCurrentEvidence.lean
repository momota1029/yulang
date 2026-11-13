import Yulang.GeneralDictionaryUnaryRefinementCapture
import Yulang.GeneralDictionaryRecordedScalarIntervalEvidence

/-! Current source evidence for a genuine historical unary nominal packet.
BranchModels and binding/origin transport are derived. Current lookup and
syntax metadata remain explicit; this is not unrestricted evidenceNode. -/
namespace Yulang.GeneralDictionaryUnaryCurrentEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalInspection GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls}

structure Shape (packet : Packet roles) (current : Context) where
  refinement : GeneralNominalRefinements.Refines packet.context.state current.state
  interpretation : current.interpretation = packet.context.interpretation
  slot : Fin packet.context.state.base.slots
  descriptor : GeneralNominalState.Descriptor packet.context.state.base.slots
  nominal : packet.context.state.nominals slot = some descriptor
  binder : Nat
  bounds : Bounds packet.context.state
  parameters : descriptor.arguments = [.type bounds]
  query : queries packet.context.state packet.context.interpretation packet.declaration =
    [.nominal descriptor.declaration.name [.variables [binder]]]
  packetBounds : packet.bounds = [(slot,slot)]
  names : packet.declaration.inputNames = [binder]
  located : arguments current packet.site.occurrence =
    some [(refinement.base.embed slot,refinement.base.embed slot)]
  role : packet.declaration.role = packet.site.occurrence.demand.role
  defined : GeneralNominalMaterialization.RootDefined packet.declaration packet.site.occurrence

abbrev Shape.currentBounds {packet : Packet roles} {current : Context} (shape : Shape packet current) :=
  [(shape.refinement.base.embed shape.slot,shape.refinement.base.embed shape.slot)]

theorem current_bindings (packet : Packet roles) (current : Context) (shape : Shape packet current) :
    bindings current.state (report current packet.declaration shape.currentBounds) = packet.bindings := by
  unfold Packet.bindings
  rw [shape.packetBounds]
  exact GeneralDictionaryUnaryRefinementCapture.bindings_preserved packet.context current shape.refinement
    shape.interpretation packet.declaration shape.slot shape.descriptor shape.nominal shape.binder shape.bounds
    shape.parameters shape.query

theorem current_finished (packet : Packet roles) (current : Context) (shape : Shape packet current) :
    Finished (report current packet.declaration shape.currentBounds) := by
  rw [GeneralDictionaryUnaryRefinementCapture.report_refined packet.context current shape.refinement
    shape.interpretation packet.declaration shape.slot shape.descriptor shape.nominal shape.binder shape.bounds
    shape.parameters shape.query]
  exact ⟨rfl,rfl,rfl⟩

theorem current_branch (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) (shape : Shape packet state.current.context)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    BranchModels packet.registry state.current.context packet.site.occurrence packet.declaration packet.checked
      shape.currentBounds model :=
  GeneralDictionaryUnaryRefinementCapture.recorded_branch root state packet reachable recorded
    shape.refinement shape.interpretation shape.slot shape.descriptor shape.nominal shape.binder
    shape.bounds shape.parameters shape.query shape.packetBounds shape.names model valid

theorem current_instance (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) (shape : Shape packet state.current.context)
    (metadata : Metadata packet.registry state.current.context)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance packet.registry state.current.context model packet.site.occurrence packet.declaration.id
      (GeneralNominalAllocation.children state.current.context.state packet.registry packet.site.occurrence
        packet.declaration packet.checked (bindings state.current.context.state
          (report state.current.context packet.declaration shape.currentBounds))) := by
  refine ⟨packet.declaration,GeneralDictionaryVariableClauseCatalog.recorded_visible packet root state reachable recorded,
    packet.checked,rfl,shape.role,shape.currentBounds,shape.located,current_finished packet _ shape,
    ⟨shape.defined,?_⟩,rfl,metadata,current_branch packet root state reachable recorded shape model valid⟩
  exact GeneralDictionaryRecordedScalarIntervalEvidence.generated_known packet root state reachable recorded
    shape.currentBounds (current_bindings packet _ shape)

theorem selected_instance (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) (shape : Shape packet state.current.context)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local packet.registry state packet.site.occurrence (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance packet.registry state.current.context model packet.site.occurrence key children := by
  have old := GeneralNominalValueBoundary.selected_old selected
  have metadata : Metadata packet.registry state.current.context := by
    cases old with
    | selected _ unique =>
      obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := unique.1
      exact prepared.1
  have current := current_instance packet root state reachable recorded shape metadata model valid
  have same := GeneralDictionarySelectedInstanceCoherence.instance_selected packet.registry state.current
    packet.site.occurrence model packet.declaration.id key _ children current old
  simpa only [same.1,same.2] using current

theorem selected_evidence (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) (shape : Shape packet state.current.context)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local packet.registry state packet.site.occurrence (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂ (Evidence packet.registry state.current.context model) children dictionaries) :
    Evidence packet.registry state.current.context model packet.site.occurrence (.node key dictionaries) :=
  evidence_node packet.registry state.current.context model packet.site.occurrence key children dictionaries
    (selected_instance packet root state reachable recorded shape key children selected model valid) given
end Yulang.GeneralDictionaryUnaryCurrentEvidence
