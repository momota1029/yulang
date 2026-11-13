import Yulang.GeneralDictionaryRecorded168Relocation
import Yulang.GeneralDictionaryOrdinaryTrace

/-! Ordinary replay is a special case of the source-relocation interpreter.
Ordinary extension preserves the allocation seed and entire computed report;
no branch/evidence preservation is used as a premise. -/
namespace Yulang.GeneralDictionaryOrdinary168Relocation
open GeneralDeclarations GeneralNominalRecursiveCandidates
open GeneralDictionaryOrdinaryTransport
open GeneralDictionaryRecursive168Transport
open GeneralSourceDictionaries
variable {roles : Roles.RoleDecls}

theorem report_is_move (context : Context) (reserved : List Nat)
    (atoms : List (PresenceNormalForm.Atom Nat)) (allocated : List GeneralNominalIdentities.Origin)
    (value : GeneralNominalRecursiveInspection.Report context.state) :
    GeneralDictionaryOrdinaryTransport.report allocated reserved atoms value =
      GeneralNominalReportSourceTransport.moveReport
        (before := context.state) (after := (extend context reserved atoms allocated).state)
        (fun slot => slot) value := by
  have bounds : GeneralNominalReportSourceTransport.moveBounds
      (before := context.state) (after := (extend context reserved atoms allocated).state)
      (fun slot => slot) = fun bounds => bounds := by
    funext bounds; rfl
  have captures : GeneralNominalReportSourceTransport.moveCapture
      (before := context.state) (after := (extend context reserved atoms allocated).state)
      (fun slot => slot) = capture allocated reserved atoms := by
    funext captured; rfl
  cases value
  simp [GeneralDictionaryOrdinaryTransport.report,GeneralNominalReportSourceTransport.moveReport,
    bounds,captures]

theorem extension_at (registry : Registry) (context : Context) (reserved : List Nat)
    (atoms : List (PresenceNormalForm.Atom Nat)) (allocated : List GeneralNominalIdentities.Origin)
    (root : Occurrence roles) (key : Nat) :
    RelocatesAt registry context (extend context reserved atoms allocated) (fun slot => slot) root key := by
  intro declaration checked bounds _visible _key located _finished
  refine ⟨bounds,located,?_,?_⟩
  · rw [candidate_report_extended]
    exact report_is_move context reserved atoms allocated _
  · exact generated_extended allocated reserved atoms context registry root declaration checked bounds

theorem packet_relocates (registry : Registry) (state : GeneralNominalSupport.Tracked roles)
    (packet : GeneralNominalSaturationState.Packet roles)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context state.current.context) :
    GeneralDictionaryRecorded168Relocation.Relocates registry state packet := by
  obtain ⟨reserved,atoms,allocated,equal⟩ := growth
  unfold GeneralDictionaryRecorded168Relocation.Relocates
  rw [equal]
  exact ⟨fun slot => slot,fun _ => rfl,rfl,
    extension_at registry packet.context reserved atoms allocated packet.site.occurrence packet.declaration.id⟩

end Yulang.GeneralDictionaryOrdinary168Relocation
