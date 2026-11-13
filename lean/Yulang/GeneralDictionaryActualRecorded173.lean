import Yulang.GeneralNominalActualInspectionSteps
import Yulang.GeneralDictionarySharedRecordedEvidence

/-! I-28: recorded evidence for actual-inspection histories. Stored/current
contexts remain distinct. Ordinary Extension is explicit, not proved for all
administrative refreshes. These are soundness helpers, not full V5 fields. -/
namespace Yulang.GeneralDictionaryActualRecorded173
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps
open GeneralDictionaryRecursiveEvidence
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem recorded_metadata {state : Tracked roles}
    (formed : SourceFormed registry root state) (packet : Packet roles)
    (member : packet ∈ state.current.packets) :
    GeneralDictionarySharedRecordedEvidence.Metadata registry packet :=
  (GeneralDictionarySharedRecordedEvidence.formed_recorded (formed_shared formed) packet member).1

theorem recorded_committed {state : Tracked roles}
    (formed : SourceFormed registry root state) (packet : Packet roles)
    (member : packet ∈ state.current.packets) :
    GeneralNominalFeedbackSteps.Committed state.current packet :=
  GeneralDictionarySharedRecordedEvidence.recorded_committed (formed_shared formed) packet member

theorem stored_instance {state : Tracked roles}
    (formed : SourceFormed registry root state) (packet : Packet roles)
    (member : packet ∈ state.current.packets) (model : Assignment)
    (valid : Models state.current model) :
    Instance registry packet.context model packet.site.occurrence packet.declaration.id packet.children :=
  GeneralDictionarySharedRecordedEvidence.stored_instance (formed_shared formed) packet member model valid

theorem recorded_children {state : Tracked roles}
    (formed : SourceFormed registry root state) (packet : Packet roles)
    (member : packet ∈ state.current.packets) :
    ∀ child ∈ packet.children, Generated state.current packet.site.occurrence child :=
  GeneralDictionarySharedRecordedEvidence.recorded_children (formed_shared formed) packet member

theorem current_evidence {state : Tracked roles}
    (formed : SourceFormed registry root state) (packet : Packet roles)
    (member : packet ∈ state.current.packets)
    (extension : GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context)
    (model : Assignment) (valid : Models state.current model) (dictionaries : List Payload)
    (children : All₂ (Evidence registry state.current.context model) packet.children dictionaries) :
    Evidence registry state.current.context model packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  GeneralDictionarySharedRecordedEvidence.current_evidence (formed_shared formed) packet member extension model valid dictionaries children

end Yulang.GeneralDictionaryActualRecorded173
