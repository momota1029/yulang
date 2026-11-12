import Yulang.GeneralDictionaryRecordedRefresh

/-! Finite interleavings of actual ordinary feedback and certified descriptor
refreshes preserve a recorded parent in the current context. The inspection
certificate is local to that parent; this is not a general executor or a claim
that every stable selection occurs in the packet journal. -/
namespace Yulang.GeneralDictionaryRefreshTrace
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryInspectionTransport

inductive Step (registry : Registry) (root site : Occurrence roles) : State roles → State roles → Prop where
  | ordinary {before after} : GeneralDictionaryOrdinaryTrace.OrdinaryStep registry root before after →
      Step registry root site before after
  | refresh (before : State roles) (next : Observation before.context.state)
      (actual : GeneralNominalFeedbackSteps.Step registry root before
        (regenerate before (reobserve before.context next)))
      (same : PreservesAt registry before.context next site) :
      Step registry root site before (regenerate before (reobserve before.context next))

theorem step_feedback (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (step : Step registry root site before after) :
    GeneralNominalFeedbackSteps.Step registry root before after := by
  cases step with
  | ordinary actual => exact actual.1
  | refresh _ actual _ => exact actual

theorem trace_feedback (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root site) before after) :
    B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (step_feedback registry root site _ _ step)

theorem step_instance (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (step : Step registry root site before after)
    (model : Assignment) (valid : Models after model) (key : Nat) (children : List (Occurrence roles))
    (old : GeneralDictionaryRecursiveEvidence.Instance registry before.context model site key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model site key children := by
  cases step with
  | ordinary actual =>
    exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ _ actual.2 model valid.1 _ _ _ old
  | refresh next _ same =>
    exact instance_of_reports registry _ next model site key children same valid.1 old

theorem trace_instance (registry : Registry) (root site : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root site) before after)
    (model : Assignment) (valid : Models after model) (key : Nat) (children : List (Occurrence roles))
    (old : GeneralDictionaryRecursiveEvidence.Instance registry before.context model site key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model site key children := by
  induction path with
  | refl => exact old
  | tail _ step ih =>
    have earlier := GeneralNominalFeedbackSteps.step_models
      (step_feedback registry root site _ _ step) model valid
    exact step_instance registry root site _ _ step model valid key children (ih earlier)

/-- SourceFormed supplies the old recorded branch for the final model; neither
Joint nor the desired final Instance is an extra premise. -/
theorem recorded_trace_instance (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (path : B4Target.Steps (Step registry root packet.site.occurrence) before after)
    (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  have earlier := GeneralNominalFeedbackSteps.steps_models
    (trace_feedback registry root packet.site.occurrence before after path) model valid
  have old := (GeneralDictionaryFeedbackEvidence.sourceFormed_recorded_instances registry root before
    formed packet recorded).1 model earlier
  rw [GeneralDictionaryFeedbackEvidence.sourceFormed_packet_registry registry root before formed packet recorded] at old
  apply trace_instance registry root packet.site.occurrence before after path model valid
  exact GeneralDictionaryOrdinaryTrace.instance_extension registry packet.context before.context growth
    model earlier.1 _ _ _ old

end Yulang.GeneralDictionaryRefreshTrace
