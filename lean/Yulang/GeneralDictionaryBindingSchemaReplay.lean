import Yulang.GeneralDictionaryCapturedSchemaTransport
import Yulang.GeneralDictionarySupportBindingGeneration

/-! Actual Value-history replay of variable-bearing named schemas, across
carrier-changing contexts. Computed source-ID bindings and nominal-origin reads
are compared syntactically; no final model-validity certificate is assumed. -/
namespace Yulang.GeneralDictionaryBindingSchemaReplay
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalMaterialization GeneralNominalRecursiveInspection
variable {roles : Roles.RoleDecls}

theorem packet_seed (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (packet : Packet roles) (recorded : packet ∈ state.current.packets) :
    state.current.context.state.seed = packet.context.state.seed :=
  GeneralDictionarySupportBindingGeneration.packet_seed registry root state
    (GeneralNominalDownstreamSteps.formed_old
      (GeneralNominalValueSteps.formed_old
        (GeneralNominalValueBoundary.reachable_formed registry state root reachable))) packet recorded

theorem capture_seed (before after : GeneralNominalState.State)
    (seed : after.seed = before.seed) (registry : Registry) (root key : Nat)
    (captures : GeneralNominalAllocation.Bindings) :
    GeneralNominalAllocation.capture after registry root key captures =
      GeneralNominalAllocation.capture before registry root key captures := by
  unfold GeneralNominalAllocation.capture GeneralNominalAllocation.source
  rw [seed]

theorem requests_seed (before after : GeneralNominalState.State)
    (seed : after.seed = before.seed) (registry : Registry) (root : Occurrence roles)
    (declaration : Declaration) (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings) :
    requests after registry root declaration checked captures =
      requests before registry root declaration checked captures := by
  unfold requests GeneralNominalAllocation.capture GeneralNominalAllocation.allocation GeneralNominalAllocation.source
  rw [seed]

/-- Every current origin read relevant to a variable request was already read
under the same name in the installed packet. Bounds/slots may differ. -/
def Origins (packet : Packet roles) (current : Report state) : Prop :=
  ∀ entry ∈ (GeneralNominalPacketSupport.namedSchema packet).variables,
    ∀ captured ∈ current.captures, entry.name = captured.name → entry.mode = .actual →
    ∀ origin, captured.origin = some origin →
    ∃ old ∈ (GeneralNominalPacketSupport.report packet).captures,
      old.name = captured.name ∧ old.origin = some origin

theorem replay (registry : Registry) (root : Occurrence roles) (state : Tracked roles)
    (reachable : B4TargetV5.Reachable (GeneralNominalValueBoundary.boundary roles) registry root state)
    (packet : Packet roles) (recorded : packet ∈ state.current.packets)
    (bounds : List (GeneralNominalInspection.Bounds state.current.context.state))
    (captures : bindings state.current.context.state
      (GeneralNominalRecursiveCandidates.report state.current.context packet.declaration bounds) = packet.bindings)
    (origins : Origins packet (GeneralNominalRecursiveCandidates.report state.current.context packet.declaration bounds))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralNominalMaterialization.Models state.current.context.state packet.declaration
      (GeneralNominalAllocation.capture state.current.context.state packet.registry packet.site.occurrence.identity
        packet.declaration.id (bindings state.current.context.state
          (GeneralNominalRecursiveCandidates.report state.current.context packet.declaration bounds)))
      (GeneralNominalRecursiveCandidates.report state.current.context packet.declaration bounds)
      (GeneralNominalRecursiveCandidates.generated packet.registry state.current.context packet.site.occurrence
        packet.declaration packet.checked bounds) model := by
  have seed := packet_seed registry root state reachable packet recorded
  have cap : GeneralNominalAllocation.capture state.current.context.state packet.registry packet.site.occurrence.identity
      packet.declaration.id (bindings state.current.context.state
        (GeneralNominalRecursiveCandidates.report state.current.context packet.declaration bounds)) =
      GeneralNominalPacketSupport.capture packet := by
    rw [captures]
    exact capture_seed packet.context.state state.current.context.state seed packet.registry _ _ _
  have footprint : GeneralDictionaryCapturedSchemaTransport.Footprint packet.declaration
      (GeneralNominalPacketSupport.capture packet)
      (GeneralNominalAllocation.capture state.current.context.state packet.registry packet.site.occurrence.identity
        packet.declaration.id (bindings state.current.context.state
          (GeneralNominalRecursiveCandidates.report state.current.context packet.declaration bounds)))
      (GeneralNominalPacketSupport.report packet)
      (GeneralNominalRecursiveCandidates.report state.current.context packet.declaration bounds)
      (GeneralNominalPacketSupport.namedSchema packet) := by
    refine ⟨?_,?_,origins⟩
    · intro entry member output; rw [cap]
    · intro entry member input; rw [cap]
  have result := GeneralDictionaryCapturedSchemaTransport.recorded_replay registry root state reachable packet
    recorded _ _ footprint model valid
  unfold GeneralNominalRecursiveCandidates.generated
  rw [captures,requests_seed packet.context.state state.current.context.state seed]
  rw [capture_seed packet.context.state state.current.context.state seed]
  simpa only [cap] using result
end Yulang.GeneralDictionaryBindingSchemaReplay
