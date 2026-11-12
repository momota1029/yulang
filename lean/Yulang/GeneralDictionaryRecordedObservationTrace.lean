import Yulang.GeneralDictionaryCurrentJournal
import Yulang.GeneralDictionarySelectedInstanceCoherence

/-! Current-context packet semantics across actual view-changing reobservations.
The finite guard concerns only computed reports for recorded occurrences. It
never assumes Instance or Evidence, and does not require fixed normalized views.
The source carrier remains fixed on a reobservation; arbitrary feedback is not
claimed. Ordinary steps and new installations retain the existing OrdinaryStep
Extension constraint (including no normalized-view change); no further
recorded-report guard is imposed on those ordinary steps. -/
namespace Yulang.GeneralDictionaryRecordedObservationTrace
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryInspectionTransport
open GeneralDictionaryCurrentJournal (Current)

variable {roles : Roles.RoleDecls}

/-- Only occurrences of already recorded packets need inspection preservation.
No condition is imposed at unrecorded occurrences or on child Evidence. -/
def RecordedReports (registry : Registry) (before : State roles)
    (next : Observation before.context.state) : Prop :=
  ∀ packet ∈ before.packets,
    PreservesAt registry before.context next packet.site.occurrence

inductive Step (registry : Registry) (root : Occurrence roles) : State roles → State roles → Prop where
  | ordinary {before after} : GeneralDictionaryOrdinaryTrace.OrdinaryStep registry root before after →
      Step registry root before after
  | refresh (before : State roles) (next : Observation before.context.state)
      (reports : RecordedReports registry before next)
      (actual : GeneralNominalFeedbackSteps.Step registry root before
        (regenerate before (reobserve before.context next))) :
      Step registry root before (regenerate before (reobserve before.context next))

theorem step_feedback (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (step : Step registry root before after) :
    GeneralNominalFeedbackSteps.Step registry root before after := by
  cases step with
  | ordinary actual => exact actual.1
  | refresh _ _ actual => exact actual

theorem trace_feedback (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (step_feedback registry root _ _ step)

/-- View-changing refresh transports all current packet instances under only
recorded-report equality. The actual Step supplies backwards model preservation. -/
theorem refresh_current (registry : Registry) (root : Occurrence roles)
    (before : State roles) (next : Observation before.context.state)
    (reports : RecordedReports registry before next)
    (actual : GeneralNominalFeedbackSteps.Step registry root before
      (regenerate before (reobserve before.context next)))
    (current : Current registry before) :
    Current registry (regenerate before (reobserve before.context next)) := by
  intro packet member model valid
  have earlier := GeneralNominalFeedbackSteps.step_models actual model valid
  exact instance_of_reports registry before.context next model packet.site.occurrence
    packet.declaration.id packet.children (reports packet member) valid.1
    (current packet member model earlier)

theorem step_current (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (step : Step registry root before after)
    (current : Current registry before) : Current registry after := by
  cases step with
  | ordinary actual =>
    exact GeneralDictionaryCurrentJournal.step_current registry root before after (.ordinary actual) current
  | refresh next reports actual => exact refresh_current registry root before next reports actual current

theorem trace_current (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root) before after)
    (current : Current registry before) : Current registry after := by
  induction path with
  | refl => exact current
  | tail _ step ih => exact step_current registry root _ _ step ih

/-- Initial empty journals need neither a model assumption nor per-packet
old-context extensions. Freshly installed packets enter the invariant. -/
theorem initial_trace_current (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (after : State roles)
    (path : B4Target.Steps (Step registry root) (initial context root) after) :
    Current registry after :=
  trace_current registry root _ after path
    (GeneralDictionaryCurrentJournal.initial_current registry context root)

/-- A selected recorded occurrence has exactly the stored key and ordered
children. The theorem applies to nonempty journals after report-local refreshes. -/
theorem recorded_selected (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (after : State roles)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (packet : Packet roles) (recorded : packet ∈ after.packets)
    (model : Assignment) (valid : Models after model)
    (key : Nat) (children : List (Occurrence roles))
    (selected : GeneralNominalFeedbackK2.Local registry after packet.site.occurrence (.selected key children)) :
    packet.declaration.id = key ∧ packet.children = children := by
  exact GeneralDictionarySelectedInstanceCoherence.instance_selected registry after packet.site.occurrence
    model packet.declaration.id key packet.children children
    (initial_trace_current registry root context after path packet recorded model valid) selected

/-- All child payloads and the parent use one arbitrary final journal model.
Selection, Stability and report preservation at the children are not assumed. -/
theorem recorded_node (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (after : State roles)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (packet : Packet roles) (recorded : packet ∈ after.packets)
    (model : Assignment) (valid : Models after model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (children : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry after.context model)
      packet.children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.context model
      packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry after.context model
    packet.site.occurrence packet.declaration.id packet.children dictionaries
    (initial_trace_current registry root context after path packet recorded model valid) children

end Yulang.GeneralDictionaryRecordedObservationTrace
