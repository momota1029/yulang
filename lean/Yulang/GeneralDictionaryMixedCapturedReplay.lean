import Yulang.GeneralDictionaryBindingSchemaReplay
import Yulang.GeneralDictionaryMixedCatalogReachable

/-! Replay the full mixed variable-bearing schema under actual post-install reinspection.
The operational state has changed; captured source identities and origin witnesses
are explicitly checked, and the current emission list is derived equal to history. -/
namespace Yulang.GeneralDictionaryMixedCapturedReplay
open GeneralDictionaryMixedCatalogExample
open GeneralDictionaryMixedCatalogReachable (installed reachable recorded installed_model)
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open GeneralNominalExamples (displayRoot model)
open GeneralDictionaryCapturedSchemaTransport
noncomputable abbrev currentReport := report installed.current.context declaration (show List (GeneralNominalInspection.Bounds installed.current.context.state) from [((0 : Fin 2),(0 : Fin 2))])
noncomputable abbrev currentCapture := GeneralNominalAllocation.capture installed.current.context.state registry
  displayRoot.identity declaration.id (bindings installed.current.context.state currentReport)

theorem report_current : currentReport = GeneralNominalUnaryCaptureFacts.captured
    installed.current.context.state (show Fin installed.current.context.state.base.slots from (0 : Fin 2)) 0 0
    (show GeneralNominalInspection.Bounds installed.current.context.state from ((1 : Fin 2),(1 : Fin 2))) := by
  exact GeneralNominalUnaryCaptureFacts.report_exact installed.current.context declaration
    (0 : Fin 2) GeneralNominalExamples.listDescriptor rfl 0 ((1 : Fin 2),(1 : Fin 2)) rfl GeneralDictionaryMixedCatalogInhabited.query

theorem report_old : GeneralNominalPacketSupport.report packet = GeneralNominalUnaryCaptureFacts.captured
    packet.context.state 0 0 0 (1,1) :=
  GeneralNominalUnaryCaptureFacts.report_exact (GeneralNominalExamples.context true) declaration 0 GeneralNominalExamples.listDescriptor rfl 0 (1,1) rfl GeneralDictionaryMixedCatalogInhabited.query

theorem footprint : Footprint declaration (GeneralNominalPacketSupport.capture packet) currentCapture
    (GeneralNominalPacketSupport.report packet) currentReport (GeneralNominalPacketSupport.namedSchema packet) := by
  rw [generated_exact]
  refine ⟨?_,?_,?_⟩
  · intro entry member output
    have eq := List.mem_singleton.mp member
    subst entry
    cases output
  · intro entry member _
    have eq := List.mem_singleton.mp member
    subst entry
    simp [currentCapture,GeneralNominalPacketSupport.capture,GeneralNominalSaturationState.Packet.bindings,
      report_current,GeneralNominalUnaryCaptureFacts.report_exact (GeneralNominalExamples.context true) declaration 0 GeneralNominalExamples.listDescriptor rfl 0 (1,1) rfl GeneralDictionaryMixedCatalogInhabited.query,GeneralNominalAllocation.capture,bindings,GeneralNominalUnaryCaptureFacts.captured,
      GeneralNominalAllocation.occurrences]
    rfl
  · intro entry member captured present same actual origin known
    rw [report_current] at present
    have eq := List.mem_singleton.mp present
    subst captured
    rw [report_old]
    exact ⟨_,List.mem_cons_self,rfl,known⟩

theorem replay_current (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models installed.current m) :
    GeneralNominalMaterialization.Models installed.current.context.state declaration currentCapture currentReport
      (GeneralNominalMaterialization.generated installed.current.context.state installed.current.context.interpretation
        (GeneralNominalMaterialization.requests packet.context.state packet.registry packet.site.occurrence
          packet.declaration packet.checked packet.bindings)) m :=
  recorded_replay registry displayRoot installed reachable packet recorded currentCapture currentReport footprint m valid
noncomputable abbrev currentRequests := GeneralNominalMaterialization.requests
  installed.current.context.state registry displayRoot declaration checked
  (bindings installed.current.context.state currentReport)

theorem requests_exact : currentRequests = GeneralDictionaryReachableRequestHistory.emitted packet := by
  unfold currentRequests GeneralDictionaryReachableRequestHistory.emitted
  unfold GeneralNominalMaterialization.requests
  simp only [report_current,GeneralNominalSaturationState.Packet.bindings,
    GeneralNominalUnaryCaptureFacts.report_exact (GeneralNominalExamples.context true) declaration 0
      GeneralNominalExamples.listDescriptor rfl 0 (1,1) rfl GeneralDictionaryMixedCatalogInhabited.query]
  rfl

theorem current_schema (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models installed.current m) :
    GeneralNominalMaterialization.Models installed.current.context.state declaration currentCapture currentReport
      (GeneralNominalMaterialization.generated installed.current.context.state installed.current.context.interpretation
        currentRequests) m := by
  rw [requests_exact]
  exact replay_current m valid

theorem bindings_exact : bindings installed.current.context.state currentReport = packet.bindings := by
  unfold GeneralNominalSaturationState.Packet.bindings
  rw [report_current]
  rw [GeneralNominalUnaryCaptureFacts.report_exact (GeneralNominalExamples.context true) declaration 0
    GeneralNominalExamples.listDescriptor rfl 0 (1,1) rfl GeneralDictionaryMixedCatalogInhabited.query]
  rfl

theorem computed_reinspection (m : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalSaturationState.Models installed.current m) :
    GeneralNominalMaterialization.Models installed.current.context.state declaration currentCapture currentReport
      (generated registry installed.current.context displayRoot declaration checked
        (show List (GeneralNominalInspection.Bounds installed.current.context.state) from [((0 : Fin 2),(0 : Fin 2))])) m :=
  GeneralDictionaryBindingSchemaReplay.replay registry displayRoot installed reachable packet recorded
    _ bindings_exact footprint.origins m valid

theorem context_changed : installed.current.context ≠ packet.context := by
  intro same
  have allocated := congrArg (fun c : GeneralNominalCandidates.Context => c.state.allocated) same
  have count := congrArg List.length allocated
  have different : installed.current.context.state.allocated.length ≠ packet.context.state.allocated.length := by
    decide +kernel
  exact different count

theorem nonvacuous : GeneralNominalSaturationState.Models installed.current model ∧
    (GeneralNominalPacketSupport.namedSchema packet).variables ≠ [] ∧
    GeneralNominalMaterialization.Models installed.current.context.state declaration currentCapture currentReport
      (GeneralNominalMaterialization.generated installed.current.context.state installed.current.context.interpretation
        currentRequests) model :=
  ⟨installed_model,mixed,current_schema model installed_model⟩

end Yulang.GeneralDictionaryMixedCapturedReplay
