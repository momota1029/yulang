import Yulang.GeneralDictionaryCatalogMultiArgumentEvidence
import Yulang.GeneralDictionaryCatalogScalarIntervalRoot
import Yulang.GeneralDictionaryObservedScalarRequests

/-! A recorded packet with variable-only where clauses emits only the named
root requests. Those requests are independent of carrier growth, current
inspection and allocation. Consequently its recorded requests cover a current
re-inspection without assuming any request inclusion or same-context equality.
This does not infer journal membership from stability. -/
namespace Yulang.GeneralDictionaryVariableClauseCatalog
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalMaterialization GeneralNominalRecursiveInspection
open GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls}

/-- The complete materialization request list is unchanged under arbitrary
replacement of the observation state and capture bindings in this syntax class.
The statement concerns requests, not emitted children or their allocation. -/
theorem requests_independent (packet : Packet roles)
    (variables : GeneralDictionaryVariableRequirements.VariableClauses packet.declaration)
    (current : GeneralNominalState.State) (captures : GeneralNominalAllocation.Bindings) :
    requests current packet.registry packet.site.occurrence packet.declaration packet.checked captures =
      GeneralDictionaryReachableRequestHistory.emitted packet := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ variables]
  unfold GeneralDictionaryReachableRequestHistory.emitted
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ variables]

/-- A single actual historical packet suffices to establish every current
request's catalog membership, without equal historical/current contexts. -/
theorem current_covered (state : Tracked roles) (packet : Packet roles)
    (recorded : packet ∈ state.current.packets)
    (variables : GeneralDictionaryVariableRequirements.VariableClauses packet.declaration)
    (closed : (GeneralNominalPacketSupport.namedSchema packet).variables = [])
    (captures : GeneralNominalAllocation.Bindings) :
    ∀ request ∈ requests state.current.context.state packet.registry packet.site.occurrence
      packet.declaration packet.checked captures,
      request ∈ GeneralDictionaryReachableRequestHistory.safeCatalog state := by
  rw [requests_independent packet variables]
  exact fun request member => GeneralDictionaryReachableRequestHistory.safe_member state packet recorded closed request member

/-- Current scalar heads of any finite arity consume historical named-root
requests directly, even after carrier/observation refresh. Current scalar shape
and metadata remain explicit, but request-by-request coverage is derived. -/
theorem scalar_instance (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets)
    (variables : GeneralDictionaryVariableRequirements.VariableClauses packet.declaration)
    (closed : (GeneralNominalPacketSupport.namedSchema packet).variables = [])
    (visible : packet.declaration ∈ packet.registry.declarations)
    (shape : GeneralDictionaryMultiScalarInspection.Shape state.current.context packet.site.occurrence packet.declaration)
    (metadata : GeneralNominalRecursiveCandidates.Metadata packet.registry state.current.context)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance packet.registry state.current.context model packet.site.occurrence packet.declaration.id
      (GeneralNominalAllocation.children state.current.context.state packet.registry packet.site.occurrence
        packet.declaration packet.checked (bindings state.current.context.state
          (GeneralNominalRecursiveCandidates.report state.current.context packet.declaration
            (GeneralDictionaryMultiScalarInspection.points shape.entries)))) := by
  exact GeneralDictionaryCatalogMultiArgumentEvidence.instance_of_catalog packet.registry root
    packet.site.occurrence state reachable packet.declaration visible packet.checked shape
    (current_covered state packet recorded variables closed _) metadata model valid

/-- Declaration visibility comes from the actual installation history. -/
theorem recorded_visible (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets) : packet.declaration ∈ packet.registry.declarations := by
  have formed := GeneralNominalDownstreamSteps.formed_old
    (GeneralNominalValueSteps.formed_old
      (GeneralNominalValueBoundary.reachable_formed packet.registry state root reachable))
  obtain ⟨before,support,_,_,enabled,_,_,_⟩ :=
    GeneralDictionaryInstallationOrigin.packet_origin packet.registry root state formed packet recorded
  exact enabled.1.2.2.2.1

/-- Selection coherence supplies the current key and complete child list. No
current-context equality with the stored packet and no Stable premise occurs. -/
theorem selected_scalar_instance (packet : Packet roles) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) packet.registry root state)
    (recorded : packet ∈ state.current.packets)
    (variables : GeneralDictionaryVariableRequirements.VariableClauses packet.declaration)
    (closed : (GeneralNominalPacketSupport.namedSchema packet).variables = [])
    (shape : GeneralDictionaryMultiScalarInspection.Shape state.current.context packet.site.occurrence packet.declaration)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local packet.registry state packet.site.occurrence (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance packet.registry state.current.context model packet.site.occurrence key children := by
  have old := GeneralNominalValueBoundary.selected_old selected
  have metadata : GeneralNominalRecursiveCandidates.Metadata packet.registry state.current.context := by
    cases old with
    | selected _ unique =>
      obtain ⟨_,_,_,_,_,_,_,_,prepared,_⟩ := unique.1
      exact prepared.1
  have instanceRule := scalar_instance packet root state reachable recorded variables closed
    (recorded_visible packet root state reachable recorded) shape metadata model valid
  have same := GeneralDictionarySelectedInstanceCoherence.instance_selected packet.registry state.current
    packet.site.occurrence model packet.declaration.id key _ children instanceRule old
  simpa only [same.1,same.2] using instanceRule

/-- The original root may have genuine scalar intervals rather than points.
The root formation invariant supplies endpoint order; historical requests supply
materialization, so no manually supplied request coverage remains. -/
theorem selected_root_interval_instance (packet : Packet roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles)
      packet.registry packet.site.occurrence state)
    (recorded : packet ∈ state.current.packets)
    (variables : GeneralDictionaryVariableRequirements.VariableClauses packet.declaration)
    (closed : (GeneralNominalPacketSupport.namedSchema packet).variables = [])
    (shape : GeneralDictionaryScalarIntervalInspection.Shape state.current.context packet.site.occurrence packet.declaration)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalValueBoundary.Local packet.registry state packet.site.occurrence (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance packet.registry state.current.context model packet.site.occurrence key children :=
  GeneralDictionaryCatalogScalarIntervalRoot.selected_instance packet.registry packet.site.occurrence state
    reachable packet.declaration (recorded_visible packet packet.site.occurrence state reachable recorded)
    packet.checked shape (current_covered state packet recorded variables closed _) key children selected model valid
end Yulang.GeneralDictionaryVariableClauseCatalog
