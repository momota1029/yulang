import Yulang.GeneralDictionaryBindingSchemaReplay
import Yulang.GeneralDictionaryVariableRegistryIntervals
import Yulang.GeneralDictionaryVariableClauseCatalog

/-! Current scalar interval evidence with unrestricted variable-bearing named
materialization. Actual recorded history supplies known requests and provenance;
global VariableRegistry, source-ID binding equality and current scalar Shape
remain explicit. Scalar Shape has no captures, so binding equality restricts this
bridge to packets with empty bindings. This
is not unrestricted evidenceNode or general preservation of inspection shape. -/
namespace Yulang.GeneralDictionaryRecordedScalarIntervalEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState GeneralNominalSupport
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence GeneralDictionaryScalarIntervalInspection
variable {roles : Roles.RoleDecls}

theorem recorded_generated (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) : Generated state.current root packet.site.occurrence :=
  GeneralDictionaryInstallationOrigin.packet_generated packet.registry root state
    (GeneralNominalDownstreamSteps.formed_old (GeneralNominalValueSteps.formed_old
      (GeneralNominalValueBoundary.reachable_formed packet.registry state root reachable))) packet recorded

theorem origins (packet : Packet roles) (current : Context)
    (shape : Shape current packet.site.occurrence packet.declaration) :
    GeneralDictionaryBindingSchemaReplay.Origins packet
      (report current packet.declaration (intervals shape.entries)) := by
  intro entry member captured present
  rw [report_exact current packet.site.occurrence packet.declaration shape] at present
  cases present

theorem generated_known (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) (bounds : List (GeneralNominalInspection.Bounds state.current.context.state))
    (captures : bindings state.current.context.state (report state.current.context packet.declaration bounds) = packet.bindings) :
    (generated packet.registry state.current.context packet.site.occurrence packet.declaration packet.checked bounds).unknown = false := by
  unfold generated
  rw [captures,GeneralDictionaryBindingSchemaReplay.requests_seed packet.context.state state.current.context.state
    (GeneralDictionaryBindingSchemaReplay.packet_seed packet.registry root state reachable packet recorded)]
  exact GeneralDictionaryRecordedRequestModels.reachable_subset_known packet.registry root state reachable
    packet recorded _ (fun _ member => member)

theorem branch_models (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (fragment : GeneralDictionaryVariableRegistryIntervals.VariableRegistry packet.registry)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets)
    (shape : Shape state.current.context packet.site.occurrence packet.declaration)
    (captures : bindings state.current.context.state
      (report state.current.context packet.declaration (intervals shape.entries)) = packet.bindings)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    BranchModels packet.registry state.current.context packet.site.occurrence packet.declaration packet.checked
      (intervals shape.entries) model := by
  have ordered := GeneralDictionaryGeneratedIntervals.located_intervals reachable
    (GeneralDictionaryVariableRegistryIntervals.journal fragment reachable)
    (recorded_generated packet root state reachable recorded) _ shape.located model valid
  have current := private_models packet.registry state.current.context packet.site.occurrence
    packet.declaration shape model valid.1 ordered
  exact ⟨current.1,current.2,GeneralDictionaryBindingSchemaReplay.replay packet.registry root state reachable
    packet recorded _ captures (origins packet state.current.context shape) model valid⟩

theorem instance_of_recorded (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (fragment : GeneralDictionaryVariableRegistryIntervals.VariableRegistry packet.registry)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets)
    (shape : Shape state.current.context packet.site.occurrence packet.declaration)
    (captures : bindings state.current.context.state
      (report state.current.context packet.declaration (intervals shape.entries)) = packet.bindings)
    (metadata : Metadata packet.registry state.current.context)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance packet.registry state.current.context model packet.site.occurrence packet.declaration.id
      (GeneralNominalAllocation.children state.current.context.state packet.registry packet.site.occurrence
        packet.declaration packet.checked (bindings state.current.context.state
          (report state.current.context packet.declaration (intervals shape.entries)))) := by
  refine ⟨packet.declaration,GeneralDictionaryVariableClauseCatalog.recorded_visible packet root state reachable recorded,
    packet.checked,rfl,shape.role,intervals shape.entries,shape.located,?_,?_,rfl,metadata,
    branch_models packet root state fragment reachable recorded shape captures model valid⟩
  · rw [report_exact state.current.context packet.site.occurrence packet.declaration shape]
    exact ⟨rfl,rfl,rfl⟩
  · exact ⟨shape.defined,generated_known packet root state reachable recorded _ captures⟩

theorem selected_instance (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (fragment : GeneralDictionaryVariableRegistryIntervals.VariableRegistry packet.registry)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets)
    (shape : Shape state.current.context packet.site.occurrence packet.declaration)
    (captures : bindings state.current.context.state
      (report state.current.context packet.declaration (intervals shape.entries)) = packet.bindings)
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
  have current := instance_of_recorded packet root state fragment reachable recorded shape captures metadata model valid
  have same := GeneralDictionarySelectedInstanceCoherence.instance_selected packet.registry state.current
    packet.site.occurrence model packet.declaration.id key _ children current old
  simpa only [same.1,same.2] using current
end Yulang.GeneralDictionaryRecordedScalarIntervalEvidence
