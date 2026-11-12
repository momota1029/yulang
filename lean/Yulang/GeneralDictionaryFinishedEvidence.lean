import Yulang.GeneralDictionaryFinishedInspection
import Yulang.GeneralDictionaryRefreshTrace

/-! Actual fixed-carrier, fixed-view refinement preserves already finished
source Instances and complete dictionary witnesses. Unlike the earlier finite
footprint adapters, no report/descriptor-equality or occupancy guard is needed.
This does not cover changing normalized views or source carriers, and does not
assert every stable selected node has already been recorded. -/
namespace Yulang.GeneralDictionaryFinishedEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalRecursiveCandidates (Context arguments report RequestReady)
open GeneralNominalRecursiveInspection (Finished)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryInspectionTransport GeneralDictionaryFinishedInspection

theorem report_finished (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (declaration : Declaration) (bounds : List (GeneralNominalInspection.Bounds context.state))
    (finished : Finished (report context declaration bounds)) :
    report (reobserve context next) declaration bounds = transferReport context next (report context declaration bounds) := by
  unfold report at finished ⊢
  have queries : GeneralNominalInspection.queries (reobserve context next).state
      (reobserve context next).interpretation declaration =
      GeneralNominalInspection.queries context.state context.interpretation declaration := rfl
  rw [queries]
  rw [inspectMany_finished context next view refinement _ bounds (fun _ => none) 0 finished]
  rfl

theorem instance_refinement (registry : Registry) (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (model : Assignment) (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children := by
  obtain ⟨declaration,visible,checked,identity,role,bounds,located,finished,ready,emitted,metadata,branch⟩ := old
  have reports := report_finished context next view refinement declaration bounds finished
  refine ⟨declaration,visible,checked,identity,role,bounds,located,?_,?_,?_,metadata,
    branch_of_report registry context next root declaration checked bounds model reports valid branch⟩
  · rw [reports,transferred_finished]
    exact finished
  · unfold RequestReady at ready ⊢
    rw [generated_eq registry context next root declaration checked bounds reports]
    exact ready
  · rw [reports,transferred_bindings]
    exact emitted

theorem evidence_refinement (registry : Registry) (context : Context) (next : Observation context.state)
    (view : next.view = context.state.view)
    (refinement : GeneralNominalRefinements.Refines context.state (reobserve context next).state)
    (model : Assignment) (valid : GeneralNominalState.Models (reobserve context next).state model)
    (root : Occurrence roles) (payload : GeneralDictionaryReadback.Payload)
    (old : GeneralDictionaryRecursiveEvidence.Evidence registry context model root payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry (reobserve context next) model root payload := by
  obtain ⟨tree,readback,given⟩ := old
  refine ⟨tree,readback,?_⟩
  exact GeneralSourceDictionaries.evidence_mono _ _
    (fun occurrence key children rule => instance_refinement registry context next view refinement model valid
      occurrence key children rule) given

/-- Actual journal certification provides the old model. There is no explicit
Finished premise because source Instance already includes finished inspection. -/
theorem recorded_refresh (registry : Registry) (root : Occurrence roles)
    (before : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (next : Observation before.context.state) (view : next.view = before.context.state.view)
    (refresh : GeneralNominalCycleSteps.Refresh before (reobserve before.context next))
    (model : Assignment) (valid : Models (regenerate before (reobserve before.context next)) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve before.context next) model
      packet.site.occurrence packet.declaration.id packet.children := by
  have earlier := (GeneralNominalCycleSteps.refresh_models refresh model).mp valid
  have old := (GeneralDictionaryFeedbackEvidence.sourceFormed_recorded_instances registry root before
    formed packet recorded).1 model earlier
  rw [GeneralDictionaryFeedbackEvidence.sourceFormed_packet_registry registry root before formed packet recorded] at old
  apply instance_refinement registry before.context next view refresh.refines model valid.1
  exact GeneralDictionaryOrdinaryTrace.instance_extension registry packet.context before.context growth
    model earlier.1 _ _ _ old

end Yulang.GeneralDictionaryFinishedEvidence
