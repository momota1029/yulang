import Yulang.GeneralDictionaryCommittedEvidenceExamples

/-! Stability alone does not imply context feedback on the arbitrary State
carrier. The journal below is inconsistent while the ordinary context is not.
This is an invariant counterexample, not a refutation of EvidenceNode: an empty
journal model set makes universal model evidence vacuous. Reachability is not
claimed for this deliberately malformed journal. -/
namespace Yulang.GeneralDictionaryStableFeedbackGap

open GeneralNominalSaturationState GeneralNominalSaturationSteps
open GeneralNominalDemandMerging (pointSite)
open GeneralDictionaryRecursiveObstruction
open GeneralDeclarationExamples (roles)

abbrev contradictoryContext : GeneralNominalCandidates.Context :=
  ⟨GeneralNominalState.extend context.state [] [.tyLe (.base .int) (.base .str)], context.interpretation⟩

abbrev contradictoryPacket : Packet roles :=
  ⟨registry,contradictoryContext,pointSite root,declaration,declaration_checked,[(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)]⟩

abbrev state : State roles :=
  { context := GeneralNominalExamples.context true
    packets := [contradictoryPacket]
    sites := [pointSite root] }

theorem no_models (model : GeneralNominalCommonBridge.Assignment) : ¬ Models state model := by
  intro valid
  have branch := valid.2.1 contradictoryPacket (List.mem_singleton_self _)
  have original := (GeneralNominalRecursiveCandidates.branch_interval_sound _ _ _ _ _ _ _ branch).1
  have atoms := ((GeneralNominalState.extend_models ..).mp original).2
  have bad := atoms (.tyLe (.base .int) (.base .str)) (List.mem_singleton_self _)
  have old := (CommonNominalFullModelMap.subtype_exact (.base .int) (.base .str)).mp bad
  cases (CommonRigidHeadInspection.base_iff .int .str).mp old

theorem context_consistent : GeneralNominalState.Models state.context.state GeneralNominalExamples.model :=
  GeneralNominalExamples.state_models true

theorem context_not_complete : ¬ ContextComplete state :=
  fun complete => no_models _ (complete _ context_consistent)

theorem all_sources_known (source : Nat) (member : source ∈ GeneralNominalState.sources state.context.state) :
    GeneralNominalState.Known state.context.state source := by
  have alternatives : source = 0 ∨ source = 1 := by
    simp [GeneralNominalState.sources,List.ofFn_succ] at member
    rcases member with h | h | h | h <;> simp [h]
  rcases alternatives with rfl | rfl
  · exact ⟨0,rfl,Or.inr ⟨GeneralNominalExamples.listDescriptor,rfl⟩⟩
  · exact ⟨1,rfl,Or.inl (by decide +kernel)⟩

theorem generated_only_root (child : GeneralSourceDictionaries.Occurrence roles)
    (generated : Generated state root child) : child = root := by
  induction generated with
  | root => rfl
  | child _ member _ => cases member
  | alias _ _ member _ _ =>
    have same := List.mem_singleton.mp member
    exact congrArg GeneralNominalDemandMerging.Site.occurrence same

theorem stable : Stable registry state root := by
  intro focus generated
  have same := generated_only_root focus generated
  subst focus
  refine ⟨?_,?_,?_,?_⟩
  · intro _
    exact ⟨pointSite root,List.mem_singleton_self _,rfl⟩
  · intro packet _ enabled
    obtain ⟨model,valid,_⟩ := enabled.2.2.2.2.2.2.2.2.2.2
    exact False.elim (no_models model valid)
  · intro first one _ last two _
    have sameFirst := List.mem_singleton.mp one
    have sameLast := List.mem_singleton.mp two
    rw [sameFirst,sameLast]
    exact .refl _
  · intro _ _ source member _
    exact all_sources_known source member

/-- Exactly the failed implication. This is not a stable countermodel to source
Evidence: there are no models of this malformed journal. -/
theorem stable_does_not_imply_feedback :
    Stable registry state root ∧ ¬ ContextComplete state ∧
      (∃ model, GeneralNominalState.Models state.context.state model) ∧
      (∀ model, ¬ Models state model) :=
  ⟨stable,context_not_complete,⟨_,context_consistent⟩,no_models⟩

end Yulang.GeneralDictionaryStableFeedbackGap
