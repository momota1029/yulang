import Yulang.GeneralDictionaryViewFootprint176
import Yulang.GeneralDictionaryCenteredTree176

/-! Additive actual centered histories with a local head-footprint refresh.
The fixed shape catalogue is explicit. Only currently recorded packet parents
are checked, against the finite declaration list and their determined argument
bounds. No semantic Instance/Evidence predicate occurs in a transition guard. -/
namespace Yulang.GeneralDictionaryCenteredFootprint176
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralDictionaryRecursiveEvidence GeneralDictionaryInspectionTransport
open GeneralDictionaryViewFootprint176 (HeadObservation AgreeMany)
open GeneralDictionaryCenteredFlexible176 (RecordedCurrent)
open GeneralDictionarySharedRecordedTree (RecordedTree)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralNominalSaturationState (Packet Generated)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}

/-- A finite recursive syntactic observation check. Argument lookup determines
the bound list, so the quantifier does not range over arbitrary successful bounds. -/
def RecordedFootprints (registry : Registry) (before : State roles)
    (next : HeadObservation before.erased.current.context.state) : Prop :=
  ∀ packet ∈ before.erased.current.packets, ∀ declaration ∈ registry.declarations,
    ∀ bounds, GeneralNominalRecursiveCandidates.arguments before.erased.current.context packet.site.occurrence = some bounds →
      AgreeMany before.erased.current.context next
        (GeneralNominalInspection.queries before.erased.current.context.state
          before.erased.current.context.interpretation declaration) bounds

inductive At (registry : Registry) (before : State roles) : Occurrence roles → State roles → Prop where
  | flexible {focus after} : GeneralDictionaryCenteredFlexible176.At registry before focus after →
      At registry before focus after
  | refresh (focus : Occurrence roles) (next : HeadObservation before.erased.current.context.state)
      (footprints : RecordedFootprints registry before next)
      (certificate : Refresh before (reobserve before.erased.current.context next))
      (identity : Nat) (member : identity ∈ GeneralNominalState.sources before.erased.current.context.state)
      (unknown : ¬ GeneralNominalState.Known before.erased.current.context.state identity)
      (known : GeneralNominalState.Known (reobserve before.erased.current.context next).state identity) :
      At registry before focus (refresh before (reobserve before.erased.current.context next))

def Step (registry : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ focus, Generated before.erased.current root focus ∧ At registry before focus after

theorem at_actual (action : At registry before focus after) :
    GeneralNominalCenteredSteps.At registry before focus after := by
  cases action with
  | flexible action => exact GeneralDictionaryCenteredFlexible176.at_actual action
  | refresh next footprints certificate identity member unknown known =>
    exact .refresh focus _ certificate identity member unknown known

theorem step_actual (step : Step registry root before after) :
    GeneralNominalCenteredSteps.Step registry root before after :=
  ⟨step.choose,step.choose_spec.1,at_actual step.choose_spec.2⟩

theorem steps_actual (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalCenteredSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact .tail ih (step_actual step)

theorem flexible_step (step : GeneralDictionaryCenteredFlexible176.Step registry root before after) :
    Step registry root before after := ⟨step.choose,step.choose_spec.1,.flexible step.choose_spec.2⟩

theorem flexible_steps
    (path : B4Target.Steps (GeneralDictionaryCenteredFlexible176.Step registry root) before after) :
    B4Target.Steps (Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact .tail ih (flexible_step step)

/-- A recorded parent is transported through the local head-footprint refresh
in the specified final CENTERED model. -/
theorem refresh_instance (old : RecordedCurrent registry before)
    (next : HeadObservation before.erased.current.context.state)
    (footprints : RecordedFootprints registry before next)
    (certificate : Refresh before (reobserve before.erased.current.context next))
    (packet : Packet roles) (member : packet ∈ before.erased.current.packets)
    (model : Assignment) (valid : Models (refresh before (reobserve before.erased.current.context next)) model) :
    Instance registry (reobserve before.erased.current.context next) model
      packet.site.occurrence packet.declaration.id packet.children := by
  apply GeneralDictionaryViewFootprint176.instance_refinement registry _ next certificate.refines model valid.1.1
    packet.site.occurrence packet.declaration.id packet.children
  · intro declaration visible role bounds located
    exact footprints packet member declaration visible bounds located
  · exact old packet member model ((refresh_models certificate model).mp valid)

theorem step_recorded (metadata : GeneralDictionaryCenteredRecorded176.Recorded registry before)
    (old : RecordedCurrent registry before) (step : Step registry root before after) :
    RecordedCurrent registry after := by
  obtain ⟨focus,generated,action⟩ := step
  cases action with
  | flexible action =>
    exact GeneralDictionaryCenteredFlexible176.step_recorded metadata old ⟨focus,generated,action⟩
  | refresh next footprints certificate identity member unknown known =>
    intro packet recorded model valid
    exact refresh_instance old next footprints certificate packet recorded model valid

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

/-- Complete finite dictionary evidence without assumed child Evidence.
Tree existence remains an explicit syntactic premise, not a stability claim. -/
theorem initial_trace_evidence (context : GeneralNominalCandidates.Context)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (tree : RecordedTree after.erased.current occurrence payload)
    (model : Assignment) (valid : Models after model) :
    Evidence registry after.erased.current.context model occurrence payload :=
  GeneralDictionaryCenteredTree176.current_evidence (initial_trace_recorded context path) tree model valid

end Yulang.GeneralDictionaryCenteredFootprint176
