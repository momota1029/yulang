import Yulang.GeneralDictionaryRecursive168Transport
import Yulang.GeneralDictionarySharedRecordedTree
import Yulang.GeneralDictionarySharedMetadata

/-! Shared journal replay through source-preserving descriptor relocation.
Witnesses compare computed reports and schemas, not the desired Instance or
Evidence. A finite witnessed tree only constrains packets it actually uses;
unrelated journal packets need not relocate. Tree existence is not inferred. -/
namespace Yulang.GeneralDictionaryRecorded168Relocation
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralDictionarySharedRecordedTree (RecordedTree)
variable {roles : Roles.RoleDecls}

/-- Structural current-context agreement for one historical packet. -/
def Relocates (registry : Registry) (state : Tracked roles) (packet : Packet roles) : Prop :=
  ∃ slots : Fin packet.context.state.base.slots → Fin state.current.context.state.base.slots,
    (∀ slot, state.current.context.state.base.source (slots slot) = packet.context.state.base.source slot) ∧
    state.current.context.state.seed = packet.context.state.seed ∧
    GeneralDictionaryRecursive168Transport.RelocatesAt registry packet.context state.current.context slots
      packet.site.occurrence packet.declaration.id

theorem current_instance {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (relocation : Relocates registry state packet)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.current.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  obtain ⟨slots,sources,seed,agreement⟩ := relocation
  exact GeneralDictionaryRecursive168Transport.instance_relocated registry packet.context state.current.context
    slots sources seed (GeneralDictionarySharedMetadata.formed_metadata formed)
    packet.site.occurrence packet.declaration.id packet.children agreement model valid.1
    (GeneralDictionarySharedRecordedEvidence.stored_instance formed packet member model valid)

/-- Only the packets used at nodes carry relocation obligations. -/
inductive RelocatedTree (registry : Registry) (state : Tracked roles) : Occurrence roles → Payload → Prop
  | node (packet : Packet roles) (member : packet ∈ state.current.packets)
      (relocation : Relocates registry state packet) (payloads : List Payload)
      (children : All₂ (RelocatedTree registry state) packet.children payloads) :
      RelocatedTree registry state packet.site.occurrence (.node packet.declaration.id payloads)

theorem recorded_tree (tree : RelocatedTree registry state occurrence payload) :
    RecordedTree state.current occurrence payload := by
  induction tree using RelocatedTree.rec
    (motive_2 := fun sites payloads _ => All₂ (RecordedTree state.current) sites payloads) with
  | node packet member relocation payloads children ih => exact .node packet member payloads ih
  | nil => exact .nil
  | cons one rest ihOne ihRest => exact .cons ihOne ihRest

theorem current_evidence {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (tree : RelocatedTree registry state occurrence payload)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model occurrence payload := by
  induction tree using RelocatedTree.rec
    (motive_2 := fun sites payloads _ => All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model) sites payloads) with
  | node packet member relocation payloads children ih =>
    exact GeneralDictionaryRecursiveEvidence.evidence_node _ _ _ _ _ _ _
      (current_instance formed packet member relocation model valid) ih
  | nil => exact .nil
  | cons one rest ihOne ihRest => exact .cons ihOne ihRest

/-- A convenient stronger premise recovers replay of an existing RecordedTree.
The node-local variant above does not require every journal packet to agree. -/
theorem of_recorded_tree {registry : Registry} {state : Tracked roles}
    (relocations : ∀ packet ∈ state.current.packets, Relocates registry state packet)
    (tree : RecordedTree state.current occurrence payload) :
    RelocatedTree registry state occurrence payload := by
  induction tree using RecordedTree.rec
    (motive_2 := fun sites payloads _ => All₂ (RelocatedTree registry state) sites payloads) with
  | node packet member payloads children ih => exact .node packet member (relocations packet member) payloads ih
  | nil => exact .nil
  | cons one rest ihOne ihRest => exact .cons ihOne ihRest

theorem recorded_current_evidence {registry : Registry} {root : Occurrence roles} {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (relocations : ∀ packet ∈ state.current.packets, Relocates registry state packet)
    (tree : RecordedTree state.current occurrence payload)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.current.context model occurrence payload :=
  current_evidence formed (of_recorded_tree relocations tree) model valid

theorem discharged (tree : RelocatedTree registry state occurrence payload) :
    Discharged state.current occurrence :=
  GeneralDictionarySharedRecordedTree.discharged (recorded_tree tree)
end Yulang.GeneralDictionaryRecorded168Relocation
