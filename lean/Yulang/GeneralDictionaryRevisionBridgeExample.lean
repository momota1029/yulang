import Yulang.GeneralDictionaryRevisionParameterCoverage
import Yulang.GeneralDictionaryReobservationRefinementGap
import Yulang.GeneralDictionaryCurrentRevisionObstruction

/-! Nonvacuous semantic compatibility exactly where structural refinement fails.
The existing actual certified improving revision replaces interval (2,3) with
point (2,2). It preserves a positive journal model, yet cannot satisfy Refines.
No selection or full current dictionary transport is inferred. -/
namespace Yulang.GeneralDictionaryRevisionBridgeExample
open GeneralNominalFeedbackObstruction GeneralDictionaryCurrentRevisionObstruction
open GeneralNominalSaturationState GeneralNominalReobservationSteps

theorem positive_model : Models revised model := (certified.exact model).mpr installed_models

theorem no_refinement : ¬ Nonempty (GeneralNominalRefinements.Refines installed.context.state revision.snapshot) :=
  GeneralDictionaryReobservationRefinementGap.improving_not_refines revision improves

theorem cross_checks : GeneralNominalIntervalLaws.ParameterChecks installed.context.state.base model
    (.type ((2 : Fin 4),(3 : Fin 4))) (.type ((2 : Fin 4),(2 : Fin 4))) :=
  GeneralDictionaryRevisionArgumentBridge.cross_checks revision certified model positive_model
    (0 : Fin 4) GeneralNominalIntervalExamples.descriptor point rfl rfl 0 _ _ rfl rfl

theorem parameter_covered : ∃ parameter, point.arguments[0]? = some parameter ∧
    GeneralNominalIntervalLaws.ParameterChecks installed.context.state.base model (.type ((2 : Fin 4),(3 : Fin 4))) parameter :=
  GeneralDictionaryRevisionParameterCoverage.parameter_covered revision certified model positive_model
    (0 : Fin 4) GeneralNominalIntervalExamples.descriptor point rfl rfl 0 _ rfl

theorem shared_argument : ∃ value,
    GeneralNominalProjections.Observes model (.argument (.source 0) 0 0) value ∧
    GeneralNominalState.Fits installed.context.state.base model (.type ((2 : Fin 4),(3 : Fin 4))) value ∧
    GeneralNominalState.Fits installed.context.state.base model (.type ((2 : Fin 4),(2 : Fin 4))) value :=
  GeneralDictionaryRevisionArgumentBridge.shared_argument revision certified model positive_model
    (0 : Fin 4) GeneralNominalIntervalExamples.descriptor point rfl rfl 0 _ _ rfl rfl

theorem actual_positive_boundary :
    GeneralNominalReobservationSteps.Step registry root installed revised ∧
    Improves revision ∧ Models revised model ∧
    ¬ Nonempty (GeneralNominalRefinements.Refines installed.context.state revision.snapshot) ∧
    GeneralNominalIntervalLaws.ParameterChecks installed.context.state.base model (.type ((2 : Fin 4),(3 : Fin 4))) (.type ((2 : Fin 4),(2 : Fin 4))) :=
  ⟨actual_revision,improves,positive_model,no_refinement,cross_checks⟩
end Yulang.GeneralDictionaryRevisionBridgeExample
