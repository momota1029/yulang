import Yulang.GeneralDictionaryHistoricalRequestModels
import Yulang.GeneralDictionaryValueEvidence

/-! Historical finite request semantics through descriptor reobservation and
actual value-supported traces. This preserves semantic constraints, not the
current syntactic tree certificate or arbitrary candidate inspection. -/
namespace Yulang.GeneralDictionaryHistoricalValueRequests
open GeneralDictionaryObservedFiniteRequests GeneralNominalMaterialization
open GeneralNominalSaturationState GeneralDeclarations GeneralSourceDictionaries

/-- The extra reobservation rule replaces nominal descriptors, not the inputs
used to construct a materialization schema. -/
theorem at_generated {roles : Roles.RoleDecls} (registry : Registry)
    (before after : State roles) (focus : Occurrence roles)
    (step : GeneralNominalReobservationSteps.At registry before focus after)
    (requests : List Request) :
    generated after.context.state after.context.interpretation requests =
      generated before.context.state before.context.interpretation requests := by
  cases step with
  | ordinary action =>
    exact GeneralDictionaryHistoricalRequestModels.at_generated registry before after focus action requests
  | reobserve => rfl

theorem trace_generated {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after)
    (requests : List Request) :
    generated after.context.state after.context.interpretation requests =
      generated before.context.state before.context.interpretation requests := by
  induction path with
  | refl => rfl
  | tail _ step ih => exact (at_generated registry _ _ _ step.choose_spec.2 requests).trans ih

theorem generated_models_after_trace {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after model) :
    GeneralNominalMaterialization.Models after.context.state declaration capture report
      (generated after.context.state after.context.interpretation requests) model := by
  rw [trace_generated registry root before after path requests]
  have earlier := GeneralNominalReobservationSteps.steps_models path model valid
  have good := generated_valid before.context.state before.context.interpretation requests observed model earlier.1
  refine ⟨good.2.2,?_,?_,?_⟩
  · intro entry member; rw [good.1] at member; cases member
  · intro entry member; rw [good.1] at member; cases member
  · intro entry member; rw [good.1] at member; cases member

theorem generated_shape_after_trace {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalReobservationSteps.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests) :
    (generated after.context.state after.context.interpretation requests).variables = [] ∧
      (generated after.context.state after.context.interpretation requests).unknown = false := by
  rw [trace_generated registry root before after path requests]
  exact generated_shape _ _ _ observed

/-- Full value-supported transitions, including administrative reobservation,
are handled by their actual projection, not an invalid feedback-only cast. -/
theorem value_generated_models {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.current.context.state before.current.context.interpretation requests)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.current.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after.current model) :
    GeneralNominalMaterialization.Models after.current.context.state declaration capture report
      (generated after.current.context.state after.current.context.interpretation requests) model :=
  generated_models_after_trace registry root before.current after.current
    (GeneralDictionaryValueEvidence.steps_reobservation registry root before after path)
    requests observed declaration capture report model valid

theorem value_generated_shape {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : GeneralNominalSupport.Tracked roles)
    (path : B4Target.Steps (GeneralNominalValueSteps.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.current.context.state before.current.context.interpretation requests) :
    (generated after.current.context.state after.current.context.interpretation requests).variables = [] ∧
      (generated after.current.context.state after.current.context.interpretation requests).unknown = false :=
  generated_shape_after_trace registry root before.current after.current
    (GeneralDictionaryValueEvidence.steps_reobservation registry root before after path) requests observed

end Yulang.GeneralDictionaryHistoricalValueRequests
