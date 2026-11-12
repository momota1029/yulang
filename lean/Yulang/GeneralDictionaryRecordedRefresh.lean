import Yulang.GeneralDictionaryCurrentContextReplay

/-! Actual journal-certified descriptor refresh supplies the middle-model
premise in current-context replay. The source-formed stored packet is used
without a new Joint assumption. This does not assert all stable selections are
recorded, nor claim that every certified regenerate is an enabled Step. -/
namespace Yulang.GeneralDictionaryRecordedRefresh
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDictionaryInspectionTransport

/-- All old packets in a source-formed state retain current-context meaning
through a certified reobservation, when their own inspection reports survive. -/
theorem recorded_refresh_instance (registry : Registry) (root : Occurrence roles)
    (before : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (next : Observation before.context.state)
    (refresh : GeneralNominalCycleSteps.Refresh before (reobserve before.context next))
    (same : PreservesAt registry before.context next packet.site.occurrence)
    (model : Assignment) (valid : Models (regenerate before (reobserve before.context next)) model) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve before.context next) model
      packet.site.occurrence packet.declaration.id packet.children := by
  have earlier := (GeneralNominalCycleSteps.refresh_models refresh model).mp valid
  have old := (GeneralDictionaryFeedbackEvidence.sourceFormed_recorded_instances registry root before
    formed packet recorded).1 model earlier
  rw [GeneralDictionaryFeedbackEvidence.sourceFormed_packet_registry registry root before formed packet recorded] at old
  exact GeneralDictionaryCurrentContextReplay.instance_replay registry packet.context before.context
    next growth packet.site.occurrence packet.declaration.id packet.children same model earlier.1 valid.1 old

/-- The recorded parent survives any actual ordinary-feedback tail after the
certified descriptor refresh, in every model of the final journal. -/
theorem recorded_refresh_tail_instance (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (next : Observation before.context.state)
    (refresh : GeneralNominalCycleSteps.Refresh before (reobserve before.context next))
    (same : PreservesAt registry before.context next packet.site.occurrence)
    (path : B4Target.Steps (GeneralDictionaryOrdinaryTrace.OrdinaryStep registry root)
      (regenerate before (reobserve before.context next)) after)
    (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Instance registry after.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  have realPath := GeneralDictionaryOrdinaryTrace.ordinary_trace_feedback _ _ _ _ path
  have earlier := GeneralNominalFeedbackSteps.steps_models realPath model valid
  exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ after.context
    (GeneralDictionaryOrdinaryTrace.ordinary_trace_extension _ _ _ _ path) model valid.1 _ _ _
    (recorded_refresh_instance registry root before formed packet recorded growth next refresh same model earlier)

/-- Parent and all child witnesses use the same final model and context. -/
theorem recorded_refresh_tail_evidence (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root before)
    (packet : Packet roles) (recorded : packet ∈ before.packets)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context before.context)
    (next : Observation before.context.state)
    (refresh : GeneralNominalCycleSteps.Refresh before (reobserve before.context next))
    (same : PreservesAt registry before.context next packet.site.occurrence)
    (path : B4Target.Steps (GeneralDictionaryOrdinaryTrace.OrdinaryStep registry root)
      (regenerate before (reobserve before.context next)) after)
    (model : Assignment) (valid : Models after model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry after.context model) packet.children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.context model packet.site.occurrence
      (.node packet.declaration.id dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry after.context model packet.site.occurrence
    packet.declaration.id packet.children dictionaries
    (recorded_refresh_tail_instance registry root before after formed packet recorded growth next refresh same path model valid) given

end Yulang.GeneralDictionaryRecordedRefresh
