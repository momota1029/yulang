import Yulang.GeneralNominalInitialNamedLocal189
import Yulang.GeneralNominalSourceVariableEvidence189
import Yulang.GeneralNominalCenteredHeadWFJoinCounterexample

set_option backward.isDefEq.respectTransparency false

/-! The local Evidence theorem has inhabited, genuinely stable assumptions.
The concrete scalar source has a variable-head identity-output declaration. -/
namespace Yulang.GeneralNominalInitialNamedNonvacuity189
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadOutputs GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
open GeneralNominalInitialNamedFixture189 GeneralNominalInitialNamedLocal189

theorem universal_head (assignment : GeneralNominalCommonBridge.Assignment) : HeadEquations plan assignment := by
  refine ⟨point_root_holds _ root (fun _ => rfl) assignment,?_,?_⟩
  · intro name member
    have equal : name = 0 := List.mem_singleton.mp member
    subst name
    rw [binder_zero]
    have cap : (GeneralNominalPacketSupport.capture plan.packet).inputs 0 = (1,1) := by
      unfold GeneralNominalPacketSupport.capture
      have b : packet.bindings = [(0,1,1)] := by
        change bindings snapshot (report context declaration [(1,1)]) = _
        rw [report_exact]; rfl
      change (GeneralNominalAllocation.capture _ _ _ _ packet.bindings).inputs 0 = _
      rw [b]
      rfl
    rw [cap]
    exact ⟨subtype_refl _,subtype_refl _⟩
  · rw [head_schema]
    exact self_schema assignment

theorem packet_models (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot assignment) : packet.Holds assignment := by
  have named : plan.SchemaHolds (GeneralNominalPacketSupport.namedSchema plan.packet) assignment := by
    rw [GeneralNominalInitialNamedEvidence189.initial_schema initial_source plan frame rfl,output_schema]
    exact self_schema assignment
  exact (GeneralNominalSingleVariableModels189.named_plan plan (1 : Fin 3) query rfl rfl rfl
    assignment valid (universal_head assignment) named).1

theorem candidate_packet (candidate : Plan roles)
    (framed : Frame registry start.core root key candidate) : candidate.packet = packet := by
  have reg := framed.registry_eq
  have ctx : candidate.packet.context = context := framed.context_eq
  have site : candidate.packet.site = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp framed.raw_recorded
  have decl : candidate.packet.declaration = declaration := List.mem_singleton.mp framed.visible
  cases candidate with
  | mk p input eq =>
    cases p with
    | mk pr pc ps pd checked pb =>
      simp only at reg ctx site decl
      subst pr; subst pc; subst ps; subst pd
      have bounds : pb = [((1 : Fin 3),(1 : Fin 3))] := Option.some.inj framed.located.symm
      subst pb
      rfl

theorem candidate_committed (candidate : Plan roles)
    (framed : Frame registry start.core root key candidate) :
    GeneralNominalFeedbackSteps.Committed start.core.erased.current candidate.packet := by
  rw [candidate_packet candidate framed]
  constructor
  · intro assignment valid
    exact packet_models assignment valid.1
  · intro child member
    have empty := GeneralNominalHeadLeafPlan189.children_empty plan rfl
    change child ∈ plan.packet.children at member
    rw [empty] at member
    cases member

theorem stable : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Stable registry start root := by
  intro focus generated after action
  have onlyRoot : ∀ focus, GeneralNominalSaturationState.Generated start.core.erased.current root focus → focus = root := by
    intro focus generated
    induction generated with
    | root => rfl
    | child prior member ih => cases member
    | alias prior one two same ih => exact congrArg GeneralNominalDemandMerging.Site.occurrence (List.mem_singleton.mp two)
  have same := onlyRoot focus generated
  cases action with
  | administrative focus after action =>
    cases action with
    | enqueue linked absent => exact absent _ (List.mem_singleton_self _) same.symm
    | refresh context certificate source member unknown known =>
        exact unknown (GeneralNominalCenteredTerminalForkSource.all_known _ source member)
    | equate first last one two equal novel =>
        exact novel (GeneralDictionaryReachableEvidenceInitial.initial_equal_is_raw context root first last equal)
    | reobserve revision certificate improved =>
        exact GeneralNominalReobservationSteps.pointClosed_no_revision
          (GeneralNominalCenteredTerminalForkSource.point_closed false) revision improved
  | refresh focus context certificate source member unknown known =>
      exact unknown (GeneralNominalCenteredTerminalForkSource.all_known _ source member)
  | install candidate support enabled novel =>
      exact novel (candidate_committed candidate (same ▸ enabled.frame))
  | merge first last support one two inputs novel guard =>
    have a := List.mem_singleton.mp one
    have b := List.mem_singleton.mp two
    subst first; subst last
    exact novel (.refl _)

theorem evidence : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence
    registry start model root (.node 3 []) := by
  apply (GeneralNominalSourceVariableEvidence189.stable_selected_evidence checked initial_source stable selected ?_).2 model inhabited
  intro d member _
  cases List.mem_singleton.mp member
  refine ⟨⟨0,rfl⟩,rfl,?_,?_⟩
  · intro output member
    cases List.mem_singleton.mp member
    exact ⟨⟨0,0,.var 0⟩,List.mem_singleton_self _,rfl⟩
  · intro equation member
    cases List.mem_singleton.mp member
    simp [GeneralNominalInspection.translate,GeneralDeclarationPatterns.normalize,
      GeneralNominalHeadMatchMass.Complete]

theorem inhabited_stable_selected :
    Checked registry ∧ (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root start ∧
      (GeneralNominalCenteredHeadWFBoundary.boundary roles).Stable registry start root ∧
      GeneralNominalCenteredHeadWFBoundary.Local registry start root (.selected 3 []) ∧
      Models start model ∧ root.demand.outputs ≠ [] ∧
      (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence registry start model root (.node 3 []) := by
  refine ⟨checked,initial_source,stable,?_,inhabited,by decide +kernel,evidence⟩
  simpa only [GeneralNominalHeadLeafPlan189.children_empty plan rfl] using selected

end Yulang.GeneralNominalInitialNamedNonvacuity189
