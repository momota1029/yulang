import Yulang.GeneralDictionarySupportCompletionGap

/-! InitialSource does not require satisfiability. This concrete inconsistent
source is genuinely initial/reachable; it is not a selected counterexample.
Model-conditioned evidence arguments must not silently supply the independent
model-free GeneratedChildren obligation. -/
namespace Yulang.GeneralDictionarySupportInhabitation
open GeneralNominalFeedbackObstruction GeneralNominalSaturationState

abbrev contradictory : GeneralNominalCandidates.Context :=
  ⟨GeneralNominalState.extend context.state [] [.tyLe (.base .int) (.base .str)],context.interpretation⟩

abbrev start := GeneralNominalSupport.initial contradictory root

theorem raw_no_models (model : GeneralNominalCommonBridge.Assignment) :
    ¬ GeneralNominalState.Models contradictory.state model := by
  intro valid
  have atoms := ((GeneralNominalState.extend_models ..).mp valid).2
  have bad := atoms (.tyLe (.base .int) (.base .str)) (List.mem_singleton_self _)
  have old := (CommonNominalFullModelMap.subtype_exact (.base .int) (.base .str)).mp bad
  cases (CommonRigidHeadInspection.base_iff .int .str).mp old

theorem initial_source : GeneralNominalSourceFormation.InitialSource registry contradictory root where
  roles_agree := GeneralNominalFeedbackObstruction.initial_source.roles_agree
  metadata := GeneralNominalFeedbackObstruction.initial_source.metadata
  linked := GeneralNominalFeedbackObstruction.initial_source.linked
  intervals := fun model valid => False.elim (raw_no_models model valid)
  below_seed := GeneralNominalFeedbackObstruction.initial_source.below_seed
  unallocated := GeneralNominalFeedbackObstruction.initial_source.unallocated

theorem actual_reachable : B4TargetV5.Reachable
    (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles) registry root start :=
  ⟨start,⟨contradictory,initial_source,rfl⟩,.refl⟩

theorem no_models (model : GeneralNominalCommonBridge.Assignment) : ¬ Models start.current model :=
  fun valid => raw_no_models model valid.1

theorem source_formation_does_not_imply_inhabited :
    ¬ (∀ state : GeneralNominalSupport.Tracked GeneralDeclarationExamples.roles,
      B4TargetV5.Reachable (GeneralNominalSupportBoundary.boundary GeneralDeclarationExamples.roles)
        registry root state → ∃ model, Models state.current model) := by
  intro claimed
  obtain ⟨model,valid⟩ := claimed start actual_reachable
  exact no_models model valid

end Yulang.GeneralDictionarySupportInhabitation
