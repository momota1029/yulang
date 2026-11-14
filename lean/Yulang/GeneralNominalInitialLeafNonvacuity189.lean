import Yulang.GeneralNominalInitialLeafLocal189
import Yulang.GeneralNominalInitialLeafEvidence189
import Yulang.GeneralNominalCenteredHeadWFJoinCounterexample

set_option backward.isDefEq.respectTransparency false

/-! The local Evidence theorem has inhabited, genuinely stable assumptions.
The fixture reuses the existing int Display declaration and concrete source. -/
namespace Yulang.GeneralNominalInitialLeafNonvacuity189
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadOutputs GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
open GeneralNominalInitialLeafFixture189 GeneralNominalInitialLeafLocal189

theorem packet_models (assignment : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models snapshot assignment) : packet.Holds assignment := by
  change _ ∧ _ ∧ _
  refine ⟨?_,?_,?_⟩
  · unfold privateState
    rw [report_exact]
    apply (GeneralNominalState.extend_models ..).mpr
    refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨valid,?_,?_⟩,?_⟩
    · simp [bindings,GeneralNominalAllocation.Compatible]
    · simp [bindings,GeneralNominalAllocation.merges,Declaration.inputNames,
        GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
        GeneralDeclarationPatterns.variablesArgs,GeneralDeclarationPatterns.Pattern.variables]
    · simp [selfChecks,PresenceNormalForm.All]
      exact subtype_refl _
  · rw [report_exact]; simp [ProjectionModels]
  · change GeneralNominalMaterialization.Models _ _ _ _ (GeneralNominalPacketSupport.namedSchema plan.packet) assignment
    rw [GeneralNominalHeadLeafPlan189.named_schema_empty plan rfl rfl]
    exact GeneralNominalMaterialization.empty_models ..

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
  have same := GeneralNominalCenteredHeadWFJoinCounterexample.generated_only_root focus generated
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
  apply (GeneralNominalInitialLeafEvidence189.stable_selected_evidence checked initial_source stable selected ?_ rfl).2 model inhabited
  intro d member _
  cases List.mem_singleton.mp member
  rfl

theorem inhabited_stable_selected :
    Checked registry ∧ (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root start ∧
      (GeneralNominalCenteredHeadWFBoundary.boundary roles).Stable registry start root ∧
      GeneralNominalCenteredHeadWFBoundary.Local registry start root (.selected 3 []) ∧
      Models start model ∧ (GeneralNominalCenteredHeadWFBoundary.boundary roles).Evidence
        registry start model root (.node 3 []) := by
  refine ⟨checked,initial_source,stable,?_,inhabited,evidence⟩
  simpa only [GeneralNominalHeadLeafPlan189.children_empty plan rfl] using selected

end Yulang.GeneralNominalInitialLeafNonvacuity189
