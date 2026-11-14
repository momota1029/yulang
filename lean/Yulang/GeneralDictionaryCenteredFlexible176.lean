import Yulang.GeneralDictionaryCenteredRecorded176
import Yulang.GeneralDictionaryNominalOnlyRefresh175

/-! A genuine centered subrelation. Refresh certificates quantify over CENTERED
models, not raw journal models. Only fixed-carrier observations with fixed view
or nominal-only declaration queries are admitted. No Instance/Evidence edge
premises, raw erasure compatibility or old SourceFormed assumptions are used. -/
namespace Yulang.GeneralDictionaryCenteredFlexible176
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenteredSteps
open GeneralDictionaryRecursiveEvidence GeneralDictionaryInspectionTransport
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open CommonRoleOutermostResolver (All₂)
open GeneralNominalSaturationState (Packet Generated)
open GeneralNominalCenters (Site Plan SameInputs)
variable {roles : Roles.RoleDecls} {registry : Registry} {root focus : Occurrence roles}

inductive At (registry : Registry) (before : State roles) : Occurrence roles → State roles → Prop where
  | enqueue (focus : Occurrence roles)
      (linked : GeneralNominalState.Linked before.erased.current.context.state focus.demand)
      (absent : ∀ site ∈ before.erased.current.sites, site.occurrence ≠ focus) :
      At registry before focus (administrative before (GeneralNominalSaturationState.enqueue before.erased.current focus))
  | equate (focus : Occurrence roles) (first last : Nat)
      (one : first ∈ GeneralNominalState.sources before.erased.current.context.state)
      (two : last ∈ GeneralNominalState.sources before.erased.current.context.state)
      (equal : GeneralNominalFeedbackK2.Equal before.erased.current first last)
      (novel : ¬ GeneralNominalFeedbackSteps.RawEqual before.erased.current first last) :
      At registry before focus (administrative before (GeneralNominalFeedbackSteps.equate before.erased.current first last))
  | install (plan : Plan roles) (support : List (Occurrence roles))
      (enabled : GeneralNominalFeedbackSteps.Installable registry before.erased.current plan.packet)
      (novel : ¬ GeneralNominalFeedbackSteps.Committed before.erased.current plan.packet)
      (guard : PacketGuard before plan support) :
      At registry before plan.packet.site.occurrence (install before plan support)
  | merge (first last : Site roles) (support : List (Occurrence roles))
      (one : first ∈ before.sites) (two : last ∈ before.sites)
      (same : SameInputs (Models before) first last)
      (novel : ¬ GeneralNominalSaturationState.Alias before.erased.current first.occurrence.identity last.occurrence.identity)
      (guard : GeneralNominalSupportChoices.MergeGuard before.erased first.observed last.observed support) :
      At registry before first.occurrence (merge before first last support)
  | refresh (focus : Occurrence roles) (next : Observation before.erased.current.context.state)
      (scope : next.view = before.erased.current.context.state.view ∨
        ∀ declaration ∈ registry.declarations,
          GeneralDictionaryNominalOnlyRefresh175.DeclarationFragment before.erased.current.context declaration)
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
  | enqueue focus linked absent => exact .administrative _ _ (.enqueue _ linked absent)
  | equate focus first last one two equal novel => exact .administrative _ _ (.equate _ _ _ one two equal novel)
  | install plan support enabled novel guard => exact .install plan support enabled novel guard
  | merge first last support one two same novel guard => exact .merge first last support one two same novel guard
  | refresh focus next scope certificate identity member unknown known =>
    exact .refresh focus _ certificate identity member unknown known

theorem step_actual (step : Step registry root before after) :
    GeneralNominalCenteredSteps.Step registry root before after :=
  ⟨step.choose,step.choose_spec.1,at_actual step.choose_spec.2⟩

theorem steps_actual (path : B4Target.Steps (Step registry root) before after) :
    B4Target.Steps (GeneralNominalCenteredSteps.Step registry root) before after := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact .tail ih (step_actual step)

theorem step_models (step : Step registry root before after) (model : Assignment)
    (valid : Models after model) : Models before model :=
  GeneralNominalCenteredSteps.step_models (step_actual step) model valid

theorem at_instance (action : At registry before focus after)
    (model : Assignment) (valid : Models after model)
    (occurrence : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (old : Instance registry before.erased.current.context model occurrence key children) :
    Instance registry after.erased.current.context model occurrence key children := by
  cases action with
  | enqueue =>
    exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ _
      (GeneralDictionaryOrdinaryTrace.enqueue_extension ..) model valid.1.1 _ _ _ old
  | equate =>
    exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ _
      (GeneralDictionaryOrdinaryTrace.equate_extension ..) model valid.1.1 _ _ _ old
  | install plan support enabled novel guard =>
    exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ _
      (GeneralDictionaryOrdinaryTrace.install_extension _ _ enabled.1.2.1) model valid.1.1 _ _ _ old
  | merge =>
    exact GeneralDictionaryOrdinaryTrace.instance_extension registry _ _
      (GeneralDictionaryOrdinaryTrace.merge_extension ..) model valid.1.1 _ _ _ old
  | refresh focus next scope certificate identity member unknown known =>
    rcases scope with view | nominal
    · exact GeneralDictionaryFinishedEvidence.instance_refinement registry _ next view certificate.refines
        model valid.1.1 occurrence key children old
    · exact GeneralDictionaryNominalOnlyRefresh175.instance_refinement registry _ next certificate.refines nominal
        model valid.1.1 occurrence key children old

/-- A derived semantic invariant, never a transition guard. -/
def RecordedCurrent (registry : Registry) (state : State roles) : Prop :=
  ∀ packet ∈ state.erased.current.packets, ∀ model, Models state model →
    Instance registry state.erased.current.context model packet.site.occurrence packet.declaration.id packet.children

theorem step_recorded
    (metadata : GeneralDictionaryCenteredRecorded176.Recorded registry before)
    (old : RecordedCurrent registry before) (step : Step registry root before after) :
    RecordedCurrent registry after := by
  have recordedAfter := GeneralDictionaryCenteredRecorded176.recorded_at metadata (at_actual step.choose_spec.2)
  have retained : ∀ packet ∈ before.erased.current.packets, ∀ model, Models after model →
      Instance registry after.erased.current.context model packet.site.occurrence packet.declaration.id packet.children := by
    intro packet member model valid
    exact at_instance step.choose_spec.2 model valid _ _ _ (old packet member model (step_models step model valid))
  obtain ⟨focus,generated,action⟩ := step
  intro packet member model valid
  cases action with
  | enqueue => exact retained packet member model valid
  | equate => exact retained packet member model valid
  | merge => exact retained packet member model valid
  | refresh => exact retained packet member model valid
  | install plan support enabled novel guard =>
    rcases List.mem_cons.mp member with rfl | oldMember
    · exact GeneralDictionaryCenteredRecorded176.current_instance recordedAfter plan.packet (List.mem_cons_self ..)
        (GeneralDictionaryOrdinaryTrace.packet_extension plan.packet) model valid
    · exact retained packet oldMember model valid

theorem initial_recorded (context : GeneralNominalCandidates.Context) :
    RecordedCurrent registry (initial context root) := by
  intro packet member
  cases member

theorem trace_recorded
    (metadata : GeneralDictionaryCenteredRecorded176.Recorded registry before)
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
  (trace_recorded (GeneralDictionaryCenteredRecorded176.initial_recorded context) (initial_recorded context) path).2

theorem initial_trace_instance (context : GeneralNominalCandidates.Context)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (packet : Packet roles) (member : packet ∈ after.erased.current.packets)
    (model : Assignment) (valid : Models after model) :
    Instance registry after.erased.current.context model packet.site.occurrence packet.declaration.id packet.children :=
  initial_trace_recorded context path packet member model valid

theorem initial_trace_evidence (context : GeneralNominalCandidates.Context)
    (path : B4Target.Steps (Step registry root) (initial context root) after)
    (packet : Packet roles) (member : packet ∈ after.erased.current.packets)
    (model : Assignment) (valid : Models after model) (dictionaries : List Payload)
    (given : All₂ (Evidence registry after.erased.current.context model) packet.children dictionaries) :
    Evidence registry after.erased.current.context model packet.site.occurrence (.node packet.declaration.id dictionaries) :=
  evidence_node _ _ _ _ _ _ _ (initial_trace_instance context path packet member model valid) given

end Yulang.GeneralDictionaryCenteredFlexible176
