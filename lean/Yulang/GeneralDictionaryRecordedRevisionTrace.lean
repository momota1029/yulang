import Yulang.GeneralDictionaryRecordedObservationTrace
import Yulang.GeneralNominalReobservationSteps

/-! Report-local transport on Astra's additive point-reobservation relation.
Certified point revisions may replace existing descriptors and are not ordinary
monotone refreshes. We require computed report equality at recorded occurrences,
not a semantic Instance/Evidence premise. No claim that every revision meets
this guard, or that every selected occurrence has a journal packet, is made. -/
namespace Yulang.GeneralDictionaryRecordedRevisionTrace
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryInspectionTransport
open GeneralDictionaryCurrentJournal (Current)
open GeneralNominalReobservationSteps (Revision Certified)

variable {roles : Roles.RoleDecls}

/-- View and source carrier are fixed by a point revision, but its existing
nominal descriptors may be replaced, rather than merely extended. -/
def observation (before : State roles) (revision : Revision before) : Observation before.context.state where
  view := before.context.state.view
  nominals := revision.entries
  catalogue := revision.catalogue
  bodiesOpaque := revision.opaqueHeads

theorem result_eq (before : State roles) (revision : Revision before) :
    revision.result = regenerate before (reobserve before.context (observation before revision)) := rfl

def Reports (registry : Registry) (before : State roles) (revision : Revision before) : Prop :=
  GeneralDictionaryRecordedObservationTrace.RecordedReports registry before (observation before revision)

/-- Exact journal certification transports the common model; report equality
transports the exact declaration key and ordered child list. -/
theorem revision_current (registry : Registry) (before : State roles)
    (revision : Revision before) (certificate : Certified revision)
    (reports : Reports registry before revision) (current : Current registry before) :
    Current registry revision.result := by
  intro packet member model valid
  have earlier := (certificate.exact model).mp valid
  exact instance_of_reports registry before.context (observation before revision) model
    packet.site.occurrence packet.declaration.id packet.children (reports packet member)
    valid.1 (current packet member model earlier)

inductive Step (registry : Registry) (root : Occurrence roles) : State roles → State roles → Prop where
  | feedback {before after} : GeneralDictionaryRecordedObservationTrace.Step registry root before after →
      Step registry root before after
  | revision (before : State roles) (revision : Revision before)
      (reports : Reports registry before revision) (certificate : Certified revision)
      (actual : GeneralNominalReobservationSteps.Step registry root before revision.result) :
      Step registry root before revision.result

theorem step_reobservation (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (step : Step registry root before after) :
    GeneralNominalReobservationSteps.Step registry root before after := by
  cases step with
  | feedback old =>
    exact GeneralNominalReobservationSteps.old_step
      (GeneralDictionaryRecordedObservationTrace.step_feedback registry root before after old)
  | revision _ _ _ actual => exact actual

theorem trace_reobservation (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (step_reobservation registry root _ _ step)

theorem step_current (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (step : Step registry root before after)
    (current : Current registry before) : Current registry after := by
  cases step with
  | feedback old => exact GeneralDictionaryRecordedObservationTrace.step_current registry root before after old current
  | revision revision reports certificate _ => exact revision_current registry before revision certificate reports current

theorem trace_current (registry : Registry) (root : Occurrence roles)
    (before after : State roles) (path : B4Target.Steps (Step registry root) before after)
    (current : Current registry before) : Current registry after := by
  induction path with
  | refl => exact current
  | tail _ step ih => exact step_current registry root _ _ step ih

theorem initial_trace_current (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (after : State roles)
    (path : B4Target.Steps (Step registry root) (initial context root) after) :
    Current registry after :=
  trace_current registry root _ after path
    (GeneralDictionaryCurrentJournal.initial_current registry context root)

/-- Same-final-model evidence for every actually recorded parent, including
nonempty journals after actual report-preserving descriptor replacements. -/
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

end Yulang.GeneralDictionaryRecordedRevisionTrace
