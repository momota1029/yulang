import Yulang.GeneralDictionaryFinishedEvidence
import Yulang.GeneralDictionaryInspectionTransportExamples

/-! Actual finite feedback traces whose refreshes preserve the normalized view
and source carrier. No per-node report, footprint or occupancy premise occurs.
This restricted trace is not a constructed general terminating execution. -/
namespace Yulang.GeneralDictionaryFinishedTrace
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryInspectionTransport GeneralDictionaryFinishedEvidence

inductive Step (registry : Registry) (root : Occurrence roles) : State roles → State roles → Prop where
  | ordinary {before after} : GeneralDictionaryOrdinaryTrace.OrdinaryStep registry root before after →
      Step registry root before after
  | refresh (before : State roles) (next : Observation before.context.state)
      (view : next.view = before.context.state.view)
      (certificate : GeneralNominalCycleSteps.Refresh before (reobserve before.context next))
      (actual : GeneralNominalFeedbackSteps.Step registry root before
        (regenerate before (reobserve before.context next))) :
      Step registry root before (regenerate before (reobserve before.context next))

theorem step_feedback (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (step : Step registry root before after) :
    GeneralNominalFeedbackSteps.Step registry root before after := by
  cases step with
  | ordinary actual => exact actual.1
  | refresh _ _ _ actual => exact actual

theorem trace_feedback (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (step_feedback registry root _ _ step)

theorem step_instance (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (step : Step registry root before after)
    (model : Assignment) (valid : Models after model) (key : Nat) (children : List (Occurrence roles))
    (old : GeneralDictionaryRecursiveEvidence.Instance registry before.context model site key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model site key children := by
  cases step with
  | ordinary actual =>
    exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ _ actual.2 model valid.1 _ _ _ old
  | refresh next view certificate _ =>
    exact instance_refinement registry _ next view certificate.refines model valid.1 site key children old

theorem trace_instance (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root) before after)
    (model : Assignment) (valid : Models after model) (key : Nat) (children : List (Occurrence roles))
    (old : GeneralDictionaryRecursiveEvidence.Instance registry before.context model site key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model site key children := by
  induction path with
  | refl => exact old
  | tail _ step ih =>
    have earlier := GeneralNominalFeedbackSteps.step_models (step_feedback registry root _ _ step) model valid
    exact step_instance registry root site _ _ step model valid key children (ih earlier)

theorem trace_evidence (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root) before after)
    (model : Assignment) (valid : Models after model) (payload : GeneralDictionaryReadback.Payload)
    (old : GeneralDictionaryRecursiveEvidence.Evidence registry before.context model site payload) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.context model site payload := by
  obtain ⟨tree,readback,given⟩ := old
  refine ⟨tree,readback,?_⟩
  exact GeneralSourceDictionaries.evidence_mono _ _
    (fun occurrence key children rule => trace_instance registry root occurrence before after path model valid
      key children rule) given

theorem recorded_trace_instance (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (path : B4Target.Steps (Step registry root) before after)
    (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  have earlier := GeneralNominalFeedbackSteps.steps_models (trace_feedback registry root before after path) model valid
  have old := (GeneralDictionaryFeedbackEvidence.sourceFormed_recorded_instances registry root before
    formed packet recorded).1 model earlier
  rw [GeneralDictionaryFeedbackEvidence.sourceFormed_packet_registry registry root before formed packet recorded] at old
  apply trace_instance registry root packet.site.occurrence before after path model valid
  exact GeneralDictionaryOrdinaryTrace.instance_extension registry packet.context before.context growth
    model earlier.1 _ _ _ old

namespace Actual
open GeneralNominalFeedbackObstruction GeneralNominalFeedbackRefresh
open GeneralDictionaryInspectionTransportExamples (observation reobserve_eq)

theorem descriptor_changing_step : Step registry root installed refreshed :=
  .refresh installed observation rfl refresh_certificate refresh_step

theorem current_parent_without_guard (m : Assignment) (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext m root 2 [child] := by
  have result := recorded_trace_instance registry root installed refreshed GeneralNominalFeedbackRegressions.formed
    packet (by simp [installed,GeneralNominalFeedbackSites.install])
    (GeneralDictionaryOrdinaryTrace.packet_extension packet)
    (.tail .refl descriptor_changing_step) m valid
  simpa only [GeneralNominalFeedbackObstruction.children_exact,GeneralNominalDemandMerging.pointSite,refreshed,regenerate] using result

end Actual
end Yulang.GeneralDictionaryFinishedTrace
