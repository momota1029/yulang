import Yulang.GeneralDictionarySameContextSelection
import Yulang.GeneralDictionaryOrdinaryTrace

/-! Same-model evidence and actual generated children for an arbitrary recorded
key under ordinary context growth. Current uniqueness identifies that key;
key agreement, Joint and BranchModels are not extra inputs. -/
namespace Yulang.GeneralDictionaryOrdinarySelectedReplay
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralDictionaryRecursiveEvidence GeneralNominalRecursiveCandidates
variable {roles : Roles.RoleDecls}

/-- A current survivor supplies only the common structural readiness fields.
A separately established source Instance at the SAME model then forms a
survivor for its own key, so current uniqueness may compare the two keys. -/
theorem survivor_of_instance (registry : Registry) (context : Context)
    (focus : Occurrence roles) (selectedKey : Nat) (selectedChildren : List (Occurrence roles))
    (selected : Survivor registry context focus selectedKey selectedChildren)
    (model : GeneralNominalCommonBridge.Assignment) (key : Nat) (children : List (Occurrence roles))
    (instanceRule : Instance registry context model focus key children) :
    Survivor registry context focus key children := by
  obtain ⟨ready,chosen,visible,check,id,role,bounds,located,prepared,emitted⟩ := selected
  obtain ⟨decl,present,checked,identity,declRole,intervals,found,finished,requests,kids,metadata,branch⟩ := instanceRule
  exact ⟨ready,decl,present,checked,identity,declRole,intervals,found,
    ⟨metadata,prepared.2.1,prepared.2.2.1,intervals,found,finished,requests,model,branch⟩,kids⟩

/-- No selected-key equality premise. The one current model is used both to
replay the historic packet and compare its survivor against current Unique. -/
theorem selected_replay (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    packet.declaration.id = key ∧ packet.children = children ∧
      Instance registry state.current.context model focus key children := by
  have old := (GeneralDictionarySupportJournal.recorded_instances registry root state formed packet member).1 model valid
  rw [GeneralDictionarySupportJournal.packet_registry registry root state formed packet member,same] at old
  have current := GeneralDictionaryOrdinaryTrace.instance_extension registry packet.context state.current.context
    growth model valid.1 focus packet.declaration.id packet.children old
  have identities : packet.declaration.id = key ∧ packet.children = children := by
    cases selected with
    | selected safe unique =>
      exact unique.2 _ _ (survivor_of_instance registry state.current.context focus key children unique.1
        model packet.declaration.id packet.children current)
  exact ⟨identities.1,identities.2,identities.1 ▸ identities.2 ▸ current⟩

theorem selected_generated (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Generated state.current root focus ∧ ∀ child ∈ children, Generated state.current root child := by
  have replay := selected_replay registry root focus state formed packet member growth same key children selected model valid
  have reached := GeneralDictionaryInstallationOrigin.packet_generated registry root state formed packet member
  rw [same] at reached
  refine ⟨reached,?_⟩
  intro child present
  have edge := (GeneralDictionarySupportJournal.recorded_instances registry root state formed packet member).2 child
    (replay.2.1 ▸ present)
  rw [same] at edge
  exact generated_trans reached edge

theorem selected_evidence (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂ (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries) :=
  evidence_node registry state.current.context model focus key children dictionaries
    (selected_replay registry root focus state formed packet member growth same key children selected model valid).2.2 given

end Yulang.GeneralDictionaryOrdinarySelectedReplay
