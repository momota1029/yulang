import Yulang.GeneralDictionaryInspectionTransport
import Yulang.GeneralDictionaryOrdinaryTrace
import Yulang.GeneralDictionaryRefreshCurrentEvidence

/-! Replay stored packet evidence through ordinary extension and node-local
inspection-preserving reobservation. These are current-context, same-model
results, not a proof that every stable selection has been recorded. -/
namespace Yulang.GeneralDictionaryCurrentContextReplay
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryReadback (Payload)
open GeneralDictionaryInspectionTransport

/-- The final model must also satisfy the intermediate snapshot. Actual refresh
refinement supplies that fact; it is not inferred from report equality. -/
theorem instance_replay (registry : Registry)
    (before middle : GeneralNominalCandidates.Context) (next : Observation middle.state)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before middle)
    (root : Occurrence roles) (key : Nat) (children : List (Occurrence roles))
    (same : PreservesAt registry middle next root) (model : Assignment)
    (middleValid : GeneralNominalState.Models middle.state model)
    (finalValid : GeneralNominalState.Models (reobserve middle next).state model)
    (old : GeneralDictionaryRecursiveEvidence.Instance registry before model root key children) :
    GeneralDictionaryRecursiveEvidence.Instance registry (reobserve middle next) model root key children :=
  instance_of_reports registry middle next model root key children same finalValid
    (GeneralDictionaryOrdinaryTrace.instance_extension registry before middle growth model
      middleValid root key children old)

/-- At a source-formed final state, a recorded packet can be interpreted in the
current context under a node-local computed-report certificate. -/
theorem sourceFormed_recorded_current_instance (registry : Registry) (root : Occurrence roles)
    (state : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root state)
    (packet : Packet roles) (recorded : packet ∈ state.packets)
    (middle : GeneralNominalCandidates.Context) (next : Observation middle.state)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context middle)
    (current : state.context = reobserve middle next)
    (same : PreservesAt registry middle next packet.site.occurrence)
    (model : Assignment) (valid : Models state model)
    (middleValid : GeneralNominalState.Models middle.state model) :
    GeneralDictionaryRecursiveEvidence.Instance registry state.context model
      packet.site.occurrence packet.declaration.id packet.children := by
  have old := (GeneralDictionaryFeedbackEvidence.sourceFormed_recorded_instances registry root state
    formed packet recorded).1 model valid
  rw [GeneralDictionaryFeedbackEvidence.sourceFormed_packet_registry registry root state formed packet recorded] at old
  rw [current]
  exact instance_replay registry packet.context middle next growth packet.site.occurrence
    packet.declaration.id packet.children same model middleValid (current ▸ valid.1) old

/-- Child evidence is at the final context, not each child's historical context. -/
theorem sourceFormed_recorded_current_evidence (registry : Registry) (root : Occurrence roles)
    (state : State roles) (formed : GeneralNominalFeedbackSteps.SourceFormed registry root state)
    (packet : Packet roles) (recorded : packet ∈ state.packets)
    (middle : GeneralNominalCandidates.Context) (next : Observation middle.state)
    (growth : GeneralDictionaryOrdinaryTrace.Extension packet.context middle)
    (current : state.context = reobserve middle next)
    (same : PreservesAt registry middle next packet.site.occurrence)
    (model : Assignment) (valid : Models state model)
    (middleValid : GeneralNominalState.Models middle.state model) (dictionaries : List Payload)
    (given : CommonRoleOutermostResolver.All₂
      (GeneralDictionaryRecursiveEvidence.Evidence registry state.context model) packet.children dictionaries) :
    GeneralDictionaryRecursiveEvidence.Evidence registry state.context model packet.site.occurrence
      (.node packet.declaration.id dictionaries) :=
  GeneralDictionaryRecursiveEvidence.evidence_node registry state.context model packet.site.occurrence
    packet.declaration.id packet.children dictionaries
    (sourceFormed_recorded_current_instance registry root state formed packet recorded middle next
      growth current same model valid middleValid) given

/-- The existing actual descriptor refresh followed by any ordinary feedback
trace retains the parent in the final context. Its child remains a separate
obligation; this theorem does not construct a recursive dictionary. -/
theorem refreshed_parent_after_ordinary_trace (after : State GeneralDeclarationExamples.roles)
    (path : B4Target.Steps
      (GeneralDictionaryOrdinaryTrace.OrdinaryStep GeneralNominalFeedbackObstruction.registry
        GeneralNominalFeedbackObstruction.root) GeneralNominalFeedbackRefresh.refreshed after)
    (model : Assignment) (valid : Models after model) :
    GeneralDictionaryRecursiveEvidence.Instance GeneralNominalFeedbackObstruction.registry
      after.context model GeneralNominalFeedbackObstruction.root 2 [GeneralNominalFeedbackObstruction.child] := by
  have realPath := GeneralDictionaryOrdinaryTrace.ordinary_trace_feedback _ _ _ _ path
  have earlier := GeneralNominalFeedbackSteps.steps_models realPath model valid
  exact GeneralDictionaryOrdinaryTrace.instance_extension _ _ _
    (GeneralDictionaryOrdinaryTrace.ordinary_trace_extension _ _ _ _ path) model valid.1 _ _ _
    (GeneralDictionaryRefreshCurrentEvidence.refreshed_current_parent_instance model earlier)

/-- Both the installation and descriptor refresh are actual feedback Steps.
The tail is not substituted for an invented execution relation. -/
theorem refreshed_tail_execution (after : State GeneralDeclarationExamples.roles)
    (path : B4Target.Steps
      (GeneralDictionaryOrdinaryTrace.OrdinaryStep GeneralNominalFeedbackObstruction.registry
        GeneralNominalFeedbackObstruction.root) GeneralNominalFeedbackRefresh.refreshed after) :
    B4Target.Steps (GeneralNominalFeedbackSteps.Step GeneralNominalFeedbackObstruction.registry
      GeneralNominalFeedbackObstruction.root) GeneralNominalFeedbackObstruction.initialState after := by
  induction path with
  | refl =>
      exact .tail (.tail .refl GeneralNominalFeedbackRegressions.install_step)
        GeneralNominalFeedbackRefresh.refresh_step
  | tail _ step ih => exact .tail ih step.1

/-- A nonempty final model and current-context parent instance coexist with
rejection of the generated child. No child dictionary is asserted. -/
theorem refreshed_parent_nonvacuous :
    Models GeneralNominalFeedbackRefresh.refreshed GeneralNominalFeedbackObstruction.model ∧
    GeneralDictionaryRecursiveEvidence.Instance GeneralNominalFeedbackObstruction.registry
      GeneralNominalFeedbackRefresh.refreshed.context GeneralNominalFeedbackObstruction.model
      GeneralNominalFeedbackObstruction.root 2 [GeneralNominalFeedbackObstruction.child] ∧
    GeneralNominalFeedbackK2.Local GeneralNominalFeedbackObstruction.registry
      GeneralNominalFeedbackRefresh.refreshed GeneralNominalFeedbackObstruction.child .rejected := by
  have valid := (GeneralNominalFeedbackRefresh.refresh_models GeneralNominalFeedbackObstruction.model).mpr
    GeneralNominalFeedbackObstruction.installed_models
  exact ⟨valid,refreshed_parent_after_ordinary_trace _ .refl _ valid,
    GeneralNominalFeedbackRefresh.child_rejected⟩

end Yulang.GeneralDictionaryCurrentContextReplay
