import Yulang.GeneralDictionaryOrdinary168Relocation

/-! Computed-report relocation is compositional. These are structural witness
lemmas, not assumptions of semantic Evidence or a new execution relation. -/
namespace Yulang.GeneralDictionary169RelocationComposition
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalRecursiveCandidates
open GeneralNominalReportSourceTransport GeneralDictionaryRecursive168Transport
variable {roles : Roles.RoleDecls}

theorem report_comp (first middle last : GeneralNominalState.State)
    (f : Fin first.base.slots → Fin middle.base.slots)
    (g : Fin middle.base.slots → Fin last.base.slots)
    (value : GeneralNominalRecursiveInspection.Report first) :
    moveReport g (moveReport f value) = moveReport (fun x => g (f x)) value := by
  cases value
  simp [moveReport,moveCapture,moveBounds,List.map_map,Function.comp_def]

theorem at_trans (registry : Registry) (first middle last : Context)
    (f : Fin first.state.base.slots → Fin middle.state.base.slots)
    (g : Fin middle.state.base.slots → Fin last.state.base.slots)
    (occurrence : Occurrence roles) (key : Nat)
    (left : RelocatesAt registry first middle f occurrence key)
    (right : RelocatesAt registry middle last g occurrence key) :
    RelocatesAt registry first last (fun x => g (f x)) occurrence key := by
  intro declaration checked bounds visible identity located finished
  obtain ⟨next,found,reports,schemas⟩ := left declaration checked bounds visible identity located finished
  have finishedNext : GeneralNominalRecursiveInspection.Finished (report middle declaration next) := by
    rw [reports]
    exact (finished_iff f _).mpr finished
  obtain ⟨final,foundFinal,reportsFinal,schemasFinal⟩ :=
    right declaration checked next visible identity found finishedNext
  refine ⟨final,foundFinal,?_,schemasFinal.trans schemas⟩
  rw [reportsFinal,reports]
  exact report_comp first.state middle.state last.state f g _

theorem packet_extension (registry : Registry)
    (before after : GeneralNominalSupport.Tracked roles)
    (packet : GeneralNominalSaturationState.Packet roles)
    (old : GeneralDictionaryRecorded168Relocation.Relocates registry before packet)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before.current.context after.current.context) :
    GeneralDictionaryRecorded168Relocation.Relocates registry after packet := by
  obtain ⟨f,sources,seed,agreement⟩ := old
  obtain ⟨reserved,atoms,allocated,equal⟩ := growth
  unfold GeneralDictionaryRecorded168Relocation.Relocates
  rw [equal]
  refine ⟨f,sources,seed,?_⟩
  exact at_trans registry packet.context before.current.context
    (GeneralDictionaryOrdinaryTransport.extend before.current.context reserved atoms allocated) f (fun x => x)
    packet.site.occurrence packet.declaration.id agreement
    (GeneralDictionaryOrdinary168Relocation.extension_at registry before.current.context reserved atoms allocated _ _)
end Yulang.GeneralDictionary169RelocationComposition
