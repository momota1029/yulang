import Yulang.GeneralDictionaryCenteredFootprint176
import Yulang.GeneralDictionaryRecordedRevisionTrace

/-! Actual centered administrative point-reobservation, without a Refines
assumption. Existing descriptor-footprint locality transports recorded parents.
The existing Revision, Certified, Improves and observation adapter are reused.
No report equality or semantic Instance/Evidence is a transition guard. -/
namespace Yulang.GeneralDictionaryCenteredRevision176
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralDictionaryRecursiveEvidence GeneralDictionaryInspectionTransport
open GeneralDictionaryInspectionLocality (FootprintAt instance_of_footprint)
open GeneralDictionaryRecordedRevisionTrace (observation)
open GeneralDictionaryCenteredFlexible176 (RecordedCurrent)
open GeneralDictionarySharedRecordedTree (RecordedTree)
open GeneralNominalReobservationSteps (Revision Certified Improves)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Packet Generated)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}

/-- Finite descriptor-read equality at current recorded parents. It does not
forbid changes to descriptor slots outside their queried footprints. -/
def RecordedFootprints (registry : Registry) (before : State roles)
    (revision : Revision before.erased.current) : Prop :=
  ∀ packet ∈ before.erased.current.packets,
    FootprintAt registry before.erased.current.context
      (observation before.erased.current revision) packet.site.occurrence

inductive At (registry : Registry) (before : State roles) : Occurrence roles → State roles → Prop where
  | footprint {focus after} : GeneralDictionaryCenteredFootprint176.At registry before focus after →
      At registry before focus after
  | reobserve (focus : Occurrence roles) (revision : Revision before.erased.current)
      (footprints : RecordedFootprints registry before revision)
      (certificate : Certified revision) (improved : Improves revision) :
      At registry before focus (administrative before revision.result)

def Step (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ focus, Generated before.erased.current root focus ∧ At registry before focus after

theorem at_actual (action : At registry before focus after) :
    GeneralNominalCenteredSteps.At registry before focus after := by
  cases action with
  | footprint action => exact GeneralDictionaryCenteredFootprint176.at_actual action
  | reobserve revision footprints certificate improved =>
    exact .administrative focus revision.result (.reobserve focus revision certificate improved)

theorem step_actual (step : Step registry root before after) :
    GeneralNominalCenteredSteps.Step registry root before after :=
  ⟨step.choose,step.choose_spec.1,at_actual step.choose_spec.2⟩

theorem steps_actual (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalCenteredSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact .tail ih (step_actual step)

theorem footprint_step (step : GeneralDictionaryCenteredFootprint176.Step registry root before after) :
    Step registry root before after := ⟨step.choose,step.choose_spec.1,.footprint step.choose_spec.2⟩

theorem footprint_steps
    (path : B4Target.Steps (GeneralDictionaryCenteredFootprint176.Step registry root) before after) :
    B4Target.Steps (Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact .tail ih (footprint_step step)

/-- Certification supplies the same final model before the revision; the
syntactic footprint supplies source inspection equality. Refines is absent. -/
theorem revision_instance (old : RecordedCurrent registry before)
    (revision : Revision before.erased.current)
    (footprints : RecordedFootprints registry before revision)
    (certificate : Certified revision)
    (packet : Packet roles) (member : packet ∈ before.erased.current.packets)
    (model : Assignment) (valid : Models (administrative before revision.result) model) :
    Instance registry revision.result.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  have earlier : Models before model := ⟨(certificate.exact model).mp valid.1,valid.2⟩
  exact instance_of_footprint registry before.erased.current.context
    (observation before.erased.current revision) rfl model
    packet.site.occurrence packet.declaration.id packet.children (footprints packet member)
    valid.1.1 (old packet member model earlier)

theorem step_recorded (metadata : GeneralDictionaryCenteredRecorded176.Recorded registry before)
    (old : RecordedCurrent registry before) (step : Step registry root before after) :
    RecordedCurrent registry after := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | footprint action =>
    exact GeneralDictionaryCenteredFootprint176.step_recorded metadata old ⟨focus,generated,action⟩
  | reobserve revision footprints certificate improved =>
    intro packet recorded model valid
    exact revision_instance old revision footprints certificate packet recorded model valid

theorem trace_recorded (metadata : GeneralDictionaryCenteredRecorded176.Recorded registry before)
    (old : RecordedCurrent registry before)
    (path : B4Target.Steps (Step registry root) before after) :
    GeneralDictionaryCenteredRecorded176.Recorded registry after ∧ RecordedCurrent registry after := by
  induction path with
  | refl => exact ⟨metadata,old⟩
  | tail path step ih => exact
      ⟨GeneralDictionaryCenteredRecorded176.recorded_at ih.1 (at_actual step.choose_spec.2),step_recorded ih.1 ih.2 step⟩

theorem initial_trace_recorded (context : GeneralNominalCandidates.Context)
    (path : B4Target.Steps (Step registry root) (initial context root) after) :
    RecordedCurrent registry after :=
  (trace_recorded (GeneralDictionaryCenteredRecorded176.initial_recorded context)
    (GeneralDictionaryCenteredFlexible176.initial_recorded context) path).2

/-- Whole finite recorded dictionaries, not just a parent conditioned on child
Evidence. The syntactic tree is still required; no selection completeness claim. -/
theorem initial_trace_evidence (context : GeneralNominalCandidates.Context)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (tree : RecordedTree after.erased.current occurrence payload)
    (model : Assignment) (valid : Models after model) :
    Evidence registry after.erased.current.context model occurrence payload :=
  GeneralDictionaryCenteredTree176.current_evidence (initial_trace_recorded context path) tree model valid

end Yulang.GeneralDictionaryCenteredRevision176
