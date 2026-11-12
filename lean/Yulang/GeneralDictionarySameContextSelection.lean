import Yulang.GeneralDictionaryInstallationOrigin

/-! Identify current selections from actual same-context historical packets,
without assuming the historical key equals the selected key. This structural
coverage subclass is not all reachable stable selected focuses. -/
namespace Yulang.GeneralDictionarySameContextSelection
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportSteps
open GeneralDictionaryRecursiveEvidence
variable {roles : Roles.RoleDecls}

/-- Actual installation supplies a historical Survivor. Identical observation
context and occurrence let the CURRENT Unique judgment identify its key and
complete child list, with no model, stability, Joint or key-agreement premise. -/
theorem selected_identity (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (context : packet.context = state.current.context)
    (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children)) :
    packet.declaration.id = key ∧ packet.children = children := by
  obtain ⟨start,before,support,source,prior,generated,oldContext,oldSelected,enabled,fresh,guard,later⟩ :=
    GeneralDictionaryInstallationOrigin.packet_history registry root state formed packet member
  have old : GeneralNominalRecursiveCandidates.Survivor registry packet.context
      packet.site.occurrence packet.declaration.id packet.children := by
    rw [oldContext]
    cases oldSelected with | selected _ unique => exact unique.1
  rw [context,same] at old
  cases selected with | selected _ unique => exact unique.2 _ _ old

/-- A current-context source instance in every final model, including arbitrary
nonterminal requirements and associated outputs of the recorded declaration. -/
theorem selected_instance (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (context : packet.context = state.current.context)
    (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model) :
    Instance registry state.current.context model focus key children := by
  have identities := selected_identity registry root focus state formed packet member context same key children selected
  have old := (GeneralDictionarySupportJournal.recorded_instances registry root state formed packet member).1 model valid
  rw [GeneralDictionarySupportJournal.packet_registry registry root state formed packet member,
    context,same,identities.1,identities.2] at old
  exact old

theorem selected_generated (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (context : packet.context = state.current.context)
    (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children)) :
    Generated state.current root focus ∧ ∀ child ∈ children, Generated state.current root child := by
  have reached := GeneralDictionaryInstallationOrigin.packet_generated registry root state formed packet member
  rw [same] at reached
  refine ⟨reached,?_⟩
  intro child present
  have identities := selected_identity registry root focus state formed packet member context same key children selected
  have edge := (GeneralDictionarySupportJournal.recorded_instances registry root state formed packet member).2 child
    (identities.2 ▸ present)
  rw [same] at edge
  exact generated_trans reached edge

theorem selected_evidence (registry : Registry) (root focus : Occurrence roles)
    (state : Tracked roles) (formed : SourceFormed registry root state)
    (packet : Packet roles) (member : packet ∈ state.current.packets)
    (context : packet.context = state.current.context)
    (same : packet.site.occurrence = focus)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalSupportBoundary.Local registry state focus (.selected key children))
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models state.current model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (given : CommonRoleOutermostResolver.All₂ (Evidence registry state.current.context model) children dictionaries) :
    Evidence registry state.current.context model focus (.node key dictionaries) :=
  evidence_node registry state.current.context model focus key children dictionaries
    (selected_instance registry root focus state formed packet member context same key children selected model valid) given

end Yulang.GeneralDictionarySameContextSelection
