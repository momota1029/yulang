import Yulang.GeneralDictionaryCycleEvidence
import Yulang.GeneralDictionaryStableFeedbackGap

/-! The new cycle rules do not imply Joint at every raw stable selection.
This explicit journal has a checked selected root and a consistent ordinary
context, but an inconsistent stale packet. Thus the example refutes the raw
SelectedJoint obligation, not EvidenceNode (whose models are empty here), and
makes no reachability claim. Astra's definitions remain unchanged. -/
namespace Yulang.GeneralDictionaryCycleEvidenceGap

open GeneralDeclarationExamples (roles)
open GeneralNominalRecursiveExamples (len lenRegistry lenRoot len_checked)
open GeneralNominalSaturationState GeneralNominalCycleSteps
open GeneralNominalDemandMerging (pointSite)

abbrev state : State roles :=
  { context := GeneralNominalCycleWrapper.context
    packets := [GeneralDictionaryStableFeedbackGap.contradictoryPacket]
    sites := [pointSite lenRoot] }

theorem no_models (model : GeneralNominalCommonBridge.Assignment) : ¬ Models state model := by
  intro valid
  have branch := valid.2.1 GeneralDictionaryStableFeedbackGap.contradictoryPacket (List.mem_singleton_self _)
  have original := (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ branch).1
  have atoms := ((GeneralNominalState.extend_models ..).mp original).2
  have bad := atoms (.tyLe (.base .int) (.base .str)) (List.mem_singleton_self _)
  have old := (CommonNominalFullModelMap.subtype_exact (.base .int) (.base .str)).mp bad
  cases (CommonRigidHeadInspection.base_iff .int .str).mp old

theorem context_consistent : GeneralNominalState.Models state.context.state GeneralNominalCycleWrapper.model :=
  GeneralNominalCycleWrapper.state_models

theorem context_not_complete : ¬ ContextComplete state :=
  fun complete => no_models _ (complete _ context_consistent)

theorem all_sources_known (source : Nat) (member : source ∈ GeneralNominalState.sources state.context.state) :
    GeneralNominalState.Known state.context.state source := by
  have alternatives : source = 0 ∨ source = 1 := by
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h <;> simp [h]
  rcases alternatives with rfl | rfl
  · exact ⟨0,rfl,Or.inl (by decide +kernel)⟩
  · exact ⟨1,rfl,Or.inr ⟨GeneralNominalCycleWrapper.descriptor,rfl⟩⟩

theorem generated_only_root (child : GeneralSourceDictionaries.Occurrence roles)
    (generated : Generated state lenRoot child) : child = lenRoot := by
  induction generated with
  | root => rfl
  | child _ member _ => cases member
  | alias _ _ member _ _ =>
    have same := List.mem_singleton.mp member
    exact congrArg GeneralNominalDemandMerging.Site.occurrence same

theorem stable : Stable lenRegistry state lenRoot := by
  intro focus generated
  have same := generated_only_root focus generated
  subst focus
  refine ⟨?_,?_,?_,?_⟩
  · intro _
    exact ⟨pointSite lenRoot,List.mem_singleton_self _,rfl⟩
  · intro packet _ enabled
    obtain ⟨model,valid,_⟩ := enabled.2.2.2.2.2.2.2.2.2.2.1
    exact False.elim (no_models model valid)
  · intro first one _ last two _
    have sameFirst := List.mem_singleton.mp one
    have sameLast := List.mem_singleton.mp two
    rw [sameFirst,sameLast]
    exact .refl _
  · intro _ _ source member _
    exact all_sources_known source member

theorem selected : GeneralNominalCycleK2.Local lenRegistry state.context lenRoot (.selected 30 []) :=
  GeneralNominalCycleRegressions.wrapper_len_selected

theorem not_joint : ¬ GeneralNominalJointCandidates.Joint lenRegistry state lenRoot 30 := by
  intro joint
  obtain ⟨model,valid⟩ := GeneralNominalJointCandidates.joint_consistent_with_journal joint
  exact no_models model valid

theorem checked : GeneralDeclarations.Checked lenRegistry := by
  refine ⟨by decide +kernel,?_⟩
  intro declaration member
  have same := List.mem_singleton.mp member
  subst declaration
  exact len_checked

/-- This explicit obstruction survives the change to cycle-based K2 and the
new Joint install guard. It is about arbitrary journal states, not execution. -/
theorem stable_selected_not_joint :
    GeneralDeclarations.Checked lenRegistry ∧ Stable lenRegistry state lenRoot ∧
    GeneralNominalCycleK2.Local lenRegistry state.context lenRoot (.selected 30 []) ∧
    ¬ GeneralNominalJointCandidates.Joint lenRegistry state lenRoot 30 ∧
    ¬ ContextComplete state ∧
    (∃ model, GeneralNominalState.Models state.context.state model) ∧
    (∀ model, ¬ Models state model) :=
  ⟨checked,stable,selected,not_joint,context_not_complete,⟨_,context_consistent⟩,no_models⟩

theorem no_raw_selectedJoint : ¬ GeneralDictionaryCycleEvidence.SelectedJoint roles := by
  intro joint
  exact not_joint (joint lenRegistry ⟨rfl,checked⟩ state lenRoot 30 [] stable selected)

end Yulang.GeneralDictionaryCycleEvidenceGap
