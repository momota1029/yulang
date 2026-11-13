import Yulang.GeneralNominalSharedSteps
import Yulang.GeneralDictionaryCommittedEvidence
import Yulang.GeneralDictionaryOrdinaryTrace

/-! Recorded-packet evidence by induction on the actual Shared history.
Stored inspection contexts are retained; current-context transport requires
an explicit ordinary extension and is not asserted for arbitrary refresh. -/
namespace Yulang.GeneralDictionarySharedRecordedEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

def Metadata (registry : Registry) (packet : Packet roles) : Prop :=
  packet.registry = registry ∧
  packet.declaration ∈ packet.registry.declarations ∧
  packet.declaration.role = packet.site.occurrence.demand.role ∧
  GeneralNominalRecursiveCandidates.arguments packet.context packet.site.occurrence = some packet.bounds ∧
  GeneralNominalRecursiveCandidates.Prepared packet.registry packet.context packet.site.occurrence packet.declaration packet.checked

theorem formed_recorded {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state) :
    ∀ packet ∈ state.current.packets, Metadata registry packet ∧
      ∀ child ∈ packet.children, (packet.site.occurrence,child) ∈ state.current.edges := by
  induction formed with
  | initial context source => intro packet member; cases member
  | @update before after formed step ih =>
    obtain ⟨focus,generated,action⟩ := step
    cases action with
    | administrative focus after action =>
      have packets : after.packets = before.current.packets := by cases action <;> rfl
      have edges : after.edges = before.current.edges := by cases action <;> rfl
      intro packet member
      simpa only [packets,edges] using ih packet (packets ▸ member)
    | install added support enabled novel guard =>
      intro packet member
      change packet ∈ added :: before.current.packets at member
      rcases List.mem_cons.mp member with same | old
      · subst packet
        refine ⟨⟨enabled.1.1,?_,enabled.1.2.2.2.2.1,enabled.1.2.2.2.2.2.1,enabled.1.2.2.2.2.2.2.1⟩,?_⟩
        · simpa only [enabled.1.1] using enabled.1.2.2.2.1
        · intro child present
          exact List.mem_append_right _ (List.mem_map.mpr ⟨child,present,rfl⟩)
      · obtain ⟨metadata,edges⟩ := ih packet old
        exact ⟨metadata,fun child present => List.mem_append_left _ (edges child present)⟩
    | merge first last support one two same novel guard => exact ih

theorem recorded_committed {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets) :
    GeneralNominalFeedbackSteps.Committed state.current packet :=
  ⟨fun _model valid => valid.2.1 packet member,(formed_recorded formed packet member).2⟩

theorem stored_instance {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (model : Assignment) (valid : Models state.current model) :
    Instance registry packet.context model packet.site.occurrence packet.declaration.id packet.children := by
  obtain ⟨same,visible,role,located,prepared⟩ := (formed_recorded formed packet member).1
  have result := GeneralDictionaryCommittedEvidence.committed_instance state.current packet
    visible role located prepared (recorded_committed formed packet member) model valid
  simpa only [same] using result

theorem recorded_children {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets) :
    ∀ child ∈ packet.children, Generated state.current packet.site.occurrence child :=
  GeneralDictionaryCommittedEvidence.committed_children _ packet (recorded_committed formed packet member)

theorem current_instance {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (extension : GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (model : Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model packet.site.occurrence packet.declaration.id packet.children :=
  GeneralDictionaryOrdinaryTrace.instance_extension registry _ _ extension model valid.1 _ _ _
    (stored_instance formed packet member model valid)

theorem current_evidence {state : Tracked roles}
    (formed : GeneralNominalSharedSteps.SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (extension : GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (children : All₂ (Evidence registry state.current.context model) packet.children dictionaries) :
    Evidence registry state.current.context model packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  evidence_node _ _ _ _ _ _ _ (current_instance formed packet member extension model valid) children

end Yulang.GeneralDictionarySharedRecordedEvidence
