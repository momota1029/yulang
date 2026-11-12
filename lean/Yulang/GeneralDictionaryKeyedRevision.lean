import Yulang.GeneralDictionaryRecordedRevisionTrace
import Yulang.GeneralDictionaryInspectionLocality

/-! Key-local computed guards for current journal semantics. Competitors with a
 different declaration key are not constrained. This is a sufficient restricted
 trace, not an unconditional theorem about all actual revisions. -/
namespace Yulang.GeneralDictionaryKeyedRevision
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalRecursiveCandidates (Context arguments report RequestReady)
open GeneralDictionaryInspectionTransport
open GeneralDictionaryInspectionLocality
open GeneralDictionaryCurrentJournal (Current)
open GeneralNominalReobservationSteps (Revision Certified)
variable {roles : Roles.RoleDecls}

def KeyReports (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (key : Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.id = key → declaration.role = root.demand.role →
    ∀ bounds, arguments context root = some bounds →
      report (reobserve context next) declaration bounds = transferReport context next (report context declaration bounds)

def KeyFootprint (registry : Registry) (context : Context) (next : Observation context.state)
    (root : Occurrence roles) (key : Nat) : Prop :=
  ∀ declaration ∈ registry.declarations, declaration.id = key → declaration.role = root.demand.role →
    ∀ bounds, arguments context root = some bounds →
      ∀ slot ∈ footprints context.state
        (GeneralNominalInspection.queries context.state context.interpretation declaration) bounds,
        next.nominals slot = context.state.nominals slot

theorem reports_of_footprint (registry : Registry) (context : Context)
    (next : Observation context.state) (view : next.view = context.state.view)
    (root : Occurrence roles) (key : Nat) (same : KeyFootprint registry context next root key) :
    KeyReports registry context next root key := by
  intro declaration visible identity role bounds located
  exact report_local context next view declaration bounds (same declaration visible identity role bounds located)

theorem reports_of_preservesAt (registry : Registry) (context : Context)
    (next : Observation context.state) (root : Occurrence roles) (key : Nat)
    (same : PreservesAt registry context next root) : KeyReports registry context next root key := by
  intro declaration visible _ role bounds located
  exact same declaration visible role bounds located

theorem instance_of_key_reports (registry : Registry) (context : Context)
    (next : Observation context.state) (model : Assignment) (root : Occurrence roles)
    (key : Nat) (children : List (Occurrence roles))
    (same : KeyReports registry context next root key)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children := by
  obtain ⟨declaration,visible,checked,identity,role,bounds,located,finished,ready,emitted,metadata,branch⟩ := old
  have reports := same declaration visible identity role bounds located
  refine ⟨declaration,visible,checked,identity,role,bounds,located,?_,?_,?_,metadata,
    branch_of_report registry context next root declaration checked bounds model reports valid branch⟩
  · rw [reports,transferred_finished]; exact finished
  · unfold RequestReady at ready ⊢
    rw [generated_eq registry context next root declaration checked bounds reports]; exact ready
  · rw [reports,transferred_bindings]; exact emitted

theorem instance_of_key_footprint (registry : Registry) (context : Context)
    (next : Observation context.state) (view : next.view = context.state.view)
    (model : Assignment) (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (same : KeyFootprint registry context next root key)
    (valid : GeneralNominalState.Models (reobserve context next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry context model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve context next) model root key children :=
  instance_of_key_reports registry context next model root key children
    (reports_of_footprint registry context next view root key same) valid old

def RecordedKeys (registry : Registry) (before : State roles)
    (next : Observation before.context.state) : Prop :=
  ∀ packet ∈ before.packets,
    KeyReports registry before.context next packet.site.occurrence packet.declaration.id

def RecordedFootprint (registry : Registry) (before : State roles) (revision : Revision before) : Prop :=
  ∀ packet ∈ before.packets, KeyFootprint registry before.context
    (GeneralDictionaryRecordedRevisionTrace.observation before revision)
    packet.site.occurrence packet.declaration.id

theorem recorded_keys_of_reports (registry : Registry) (before : State roles)
    (next : Observation before.context.state)
    (same : GeneralDictionaryRecordedObservationTrace.RecordedReports registry before next) :
    RecordedKeys registry before next := by
  intro packet member
  exact reports_of_preservesAt registry before.context next packet.site.occurrence packet.declaration.id (same packet member)

theorem recorded_keys_of_footprint (registry : Registry) (before : State roles)
    (revision : Revision before) (same : RecordedFootprint registry before revision) :
    RecordedKeys registry before (GeneralDictionaryRecordedRevisionTrace.observation before revision) := by
  intro packet member
  exact reports_of_footprint registry before.context _ rfl packet.site.occurrence packet.declaration.id (same packet member)

theorem refresh_current (registry : Registry) (root : Occurrence roles)
    (before : State roles) (next : Observation before.context.state)
    (same : RecordedKeys registry before next)
    (actual : GeneralNominalFeedbackSteps.Step registry root before
      (regenerate before (reobserve before.context next))) (current : Current registry before) :
    Current registry (regenerate before (reobserve before.context next)) := by
  intro packet member model valid
  exact instance_of_key_reports registry before.context next model packet.site.occurrence
    packet.declaration.id packet.children (same packet member) valid.1
    (current packet member model (GeneralNominalFeedbackSteps.step_models actual model valid))

theorem revision_current (registry : Registry) (before : State roles)
    (revision : Revision before) (certificate : Certified revision)
    (same : RecordedFootprint registry before revision) (current : Current registry before) :
    Current registry revision.result := by
  intro packet member model valid
  exact instance_of_key_reports registry before.context
    (GeneralDictionaryRecordedRevisionTrace.observation before revision) model packet.site.occurrence
    packet.declaration.id packet.children (recorded_keys_of_footprint registry before revision same packet member)
    valid.1 (current packet member model ((certificate.exact model).mp valid))

inductive Step (registry : Registry) (root : Occurrence roles) : State roles → State roles → Prop where
  | ordinary {before after} : GeneralDictionaryOrdinaryTrace.OrdinaryStep registry root before after → Step registry root before after
  | refresh (before : State roles) (next : Observation before.context.state)
      (same : RecordedKeys registry before next)
      (actual : GeneralNominalFeedbackSteps.Step registry root before (regenerate before (reobserve before.context next))) :
      Step registry root before (regenerate before (reobserve before.context next))
  | revision (before : State roles) (revision : Revision before)
      (same : RecordedFootprint registry before revision) (certificate : Certified revision)
      (actual : GeneralNominalReobservationSteps.Step registry root before revision.result) :
      Step registry root before revision.result

theorem step_actual (registry : Registry) (root : Occurrence roles) (before after : State roles)
    (step : Step registry root before after) : GeneralNominalReobservationSteps.Step registry root before after := by
  cases step with
  | ordinary old => exact GeneralNominalReobservationSteps.old_step old.1
  | refresh _ _ actual => exact GeneralNominalReobservationSteps.old_step actual
  | revision _ _ _ actual => exact actual

theorem step_current (registry : Registry) (root : Occurrence roles) (before after : State roles)
    (step : Step registry root before after) (current : Current registry before) : Current registry after := by
  cases step with
  | ordinary old => exact GeneralDictionaryRecordedObservationTrace.step_current registry root before after (.ordinary old) current
  | refresh next same actual => exact refresh_current registry root before next same actual current
  | revision revision same certificate _ => exact revision_current registry before revision certificate same current

theorem trace_actual (registry : Registry) (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (step_actual registry root _ _ step)

theorem trace_current (registry : Registry) (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (Step registry root) before after) (current : Current registry before) : Current registry after := by
  induction path with
  | refl => exact current
  | tail _ step ih => exact step_current registry root _ _ step ih

theorem initial_trace_current (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (after : State roles)
    (path : B4Target.Steps (Step registry root) (initial context root) after) : Current registry after :=
  trace_current registry root _ after path (GeneralDictionaryCurrentJournal.initial_current registry context root)

theorem recorded_node (registry : Registry) (root : Occurrence roles)
    (context : GeneralNominalCandidates.Context) (after : State roles)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (packet : Packet roles) (recorded : packet ∈ after.packets)
    (model : Assignment) (valid : Models after model)
    (dictionaries : List GeneralDictionaryReadback.Payload)
    (children : CommonRoleOutermostResolver.All₂ (GeneralDictionaryRecursiveEvidence.Evidence registry after.context model)
      packet.children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry after.context model packet.site.occurrence
      (.node packet.declaration.id dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry after.context model _ _ _ _
    (initial_trace_current registry root context after path packet recorded model valid) children
end Yulang.GeneralDictionaryKeyedRevision
