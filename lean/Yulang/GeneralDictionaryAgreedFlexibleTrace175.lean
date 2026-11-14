import Yulang.GeneralDictionaryAgreedRefiningTrace174
import Yulang.GeneralDictionaryNominalOnlyRefresh175

/-! Current recorded-parent instances along finite actual ordinary histories
with fixed-carrier refreshes. Each refresh either fixes the normalized view,
or its current translated registry queries lie in the nominal-only fragment.
The latter allows view changes, while Refines retains old nominal descriptors.
No Instance/Evidence is an edge guard. Arbitrary descriptor revisions and
carrier-changing steps remain outside this actual subrelation. -/
namespace Yulang.GeneralDictionaryAgreedFlexibleTrace175
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralDictionaryRecursiveEvidence
open GeneralDictionaryInspectionTransport
open GeneralDictionaryAgreedEvidence174 (OrdinaryAt ordinary_at_actual ordinary_at_extension)
open GeneralDictionaryAgreedRefresh174 (refreshed)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}

inductive At (registry : Registry) (before : Tracked roles) : Occurrence roles → Tracked roles → Prop where
  | ordinary {focus after} : OrdinaryAt registry before focus after → At registry before focus after
  | refresh (focus : Occurrence roles) (next : Observation before.current.context.state)
      (scope : next.view = before.current.context.state.view ∨
        ∀ declaration ∈ registry.declarations,
          GeneralDictionaryNominalOnlyRefresh175.DeclarationFragment before.current.context declaration)
      (certificate : GeneralNominalCycleSteps.Refresh before.current (reobserve before.current.context next))
      (identity : Nat) (member : identity ∈ GeneralNominalState.sources before.current.context.state)
      (unknown : ¬ GeneralNominalState.Known before.current.context.state identity)
      (known : GeneralNominalState.Known (reobserve before.current.context next).state identity) :
      At registry before focus (refreshed before next)

def Step (registry : Registry) (root : Occurrence roles) (before after : Tracked roles) : Prop :=
  ∃ focus, Generated before.current root focus ∧ At registry before focus after

theorem at_actual (action : At registry before focus after) :
    GeneralNominalActualInspectionSteps.At registry before focus after := by
  cases action with
  | ordinary action => exact ordinary_at_actual action
  | refresh next scope certificate identity member unknown known =>
    exact .administrative focus _ (.refresh focus _ certificate identity member unknown known)

theorem step_actual (step : Step registry root before after) :
    GeneralNominalActualInspectionSteps.Step registry root before after :=
  ⟨step.choose,step.choose_spec.1,at_actual step.choose_spec.2⟩

theorem steps_actual (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalActualInspectionSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail prior step ih => exact .tail ih (step_actual step)

theorem step_models (step : Step registry root before after) (model : Assignment)
    (valid : Models after.current model) : Models before.current model :=
  GeneralNominalSharedSteps.step_models
    (GeneralNominalActualInspectionSteps.step_shared (step_actual step)) model valid

theorem step_formed
    (formed : GeneralNominalActualInspectionSteps.SourceFormed registry root before)
    (step : Step registry root before after) :
    GeneralNominalActualInspectionSteps.SourceFormed registry root after :=
  .update formed (step_actual step)

/-- Transport a previously established instance in the SAME final assignment. -/
theorem at_instance (action : At registry before focus after)
    (model : Assignment) (valid : Models after.current model)
    (occurrence : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (old : Instance registry before.current.context model occurrence key children) :
    Instance registry after.current.context model occurrence key children := by
  cases action with
  | ordinary action =>
    exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ _ (ordinary_at_extension action)
      model valid.1 occurrence key children old
  | refresh next scope certificate identity member unknown known =>
    rcases scope with view | nominal
    · exact GeneralDictionaryFinishedEvidence.instance_refinement registry _ next view certificate.refines
        model valid.1 occurrence key children old
    · exact GeneralDictionaryNominalOnlyRefresh175.instance_refinement registry _ next certificate.refines nominal
        model valid.1 occurrence key children old

/-- Semantic invariant to be DERIVED; it is not an action premise. -/
def RecordedCurrent (registry : Registry) (state : Tracked roles) : Prop :=
  ∀ packet ∈ state.current.packets, ∀ model, Models state.current model →
    Instance registry state.current.context model packet.site.occurrence packet.declaration.id packet.children

theorem step_recorded
    (formed : GeneralNominalActualInspectionSteps.SourceFormed registry root before)
    (old : RecordedCurrent registry before) (step : Step registry root before after) :
    RecordedCurrent registry after := by
  have formedAfter := step_formed formed step
  have retained : ∀ packet ∈ before.current.packets, ∀ model, Models after.current model →
      Instance registry after.current.context model packet.site.occurrence packet.declaration.id packet.children := by
    intro packet member model valid
    exact at_instance step.choose_spec.2 model valid _ _ _ (old packet member model (step_models step model valid))
  obtain ⟨focus,generated,action⟩ := step
  intro packet member model valid
  cases action with
  | refresh => exact retained packet member model valid
  | ordinary action =>
    cases action with
    | enqueue => exact retained packet member model valid
    | equate => exact retained packet member model valid
    | merge => exact retained packet member model valid
    | install installed support enabled novel guard =>
      rcases List.mem_cons.mp member with rfl | oldMember
      · exact GeneralDictionarySharedRecordedEvidence.current_instance
          (GeneralNominalActualInspectionSteps.formed_shared formedAfter) packet (List.mem_cons_self ..)
          (GeneralDictionaryOrdinaryTrace.packet_extension packet) model valid
      · exact retained packet oldMember model valid

theorem initial_recorded (context : GeneralNominalCandidates.Context) :
    RecordedCurrent registry (initial context root) := by
  intro packet member
  cases member

theorem trace_formed_recorded
    (formed : GeneralNominalActualInspectionSteps.SourceFormed registry root before)
    (old : RecordedCurrent registry before)
    (path : B4Target.Steps (Step registry root) before after) :
    GeneralNominalActualInspectionSteps.SourceFormed registry root after ∧ RecordedCurrent registry after := by
  induction path with
  | refl => exact ⟨formed,old⟩
  | tail prior step ih => exact ⟨step_formed ih.1 step,step_recorded ih.1 ih.2 step⟩

/-- Empty journal initialization removes any supplied semantic invariant. -/
theorem initial_trace_recorded (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) after) :
    RecordedCurrent registry after :=
  (trace_formed_recorded (.initial context source) (initial_recorded context) path).2

theorem initial_trace_instance (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (packet : Packet roles) (member : packet ∈ after.current.packets)
    (model : Assignment) (valid : Models after.current model) :
    Instance registry after.current.context model packet.site.occurrence packet.declaration.id packet.children :=
  initial_trace_recorded context source path packet member model valid

theorem initial_trace_evidence (context : GeneralNominalCandidates.Context)
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (packet : Packet roles) (member : packet ∈ after.current.packets)
    (model : Assignment) (valid : Models after.current model) (dictionaries : List Payload)
    (given : All₂ (Evidence registry after.current.context model) packet.children dictionaries) :
    Evidence registry after.current.context model packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  evidence_node _ _ _ _ _ _ _ (initial_trace_instance context source path packet member model valid) given

/-- The previous fixed-view relation is contained in this larger actual
subrelation. The guard for its refresh uses the left disjunct. -/
theorem old_at (action : GeneralDictionaryAgreedRefiningTrace174.At registry before focus after) :
    At registry before focus after := by
  cases action with
  | ordinary action => exact .ordinary action
  | refresh next view certificate identity member unknown known =>
    exact .refresh focus next (Or.inl view) certificate identity member unknown known

theorem old_step (step : GeneralDictionaryAgreedRefiningTrace174.Step registry root before after) :
    Step registry root before after :=
  ⟨step.choose, step.choose_spec.1, old_at step.choose_spec.2⟩

theorem old_steps (path : B4Target.Steps (GeneralDictionaryAgreedRefiningTrace174.Step registry root) before after) :
    B4Target.Steps (Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail prior step ih => exact .tail ih (old_step step)

end Yulang.GeneralDictionaryAgreedFlexibleTrace175
