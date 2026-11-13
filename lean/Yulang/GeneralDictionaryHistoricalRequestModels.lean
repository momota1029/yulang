import Yulang.GeneralDictionaryObservedFiniteRequests
import Yulang.GeneralDictionaryOrdinaryTrace

/-! Historical finite source observations validate fixed materialization requests
through arbitrary feedback traces. Syntactic observations need not persist. -/
namespace Yulang.GeneralDictionaryHistoricalRequestModels
open GeneralDictionaryObservedFiniteRequests
open GeneralNominalMaterialization GeneralNominalSaturationState
open GeneralDeclarations GeneralSourceDictionaries

/-- The schema depends on constructors and interpretation, not source views. -/
theorem generated_eq (before after : GeneralNominalCandidates.Context)
    (constructors : after.state.constructors = before.state.constructors)
    (interpretation : after.interpretation = before.interpretation)
    (requests : List Request) :
    generated after.state after.interpretation requests =
      generated before.state before.interpretation requests := by
  simp only [generated,constructors,interpretation]

theorem extension_generated (before after : GeneralNominalCandidates.Context)
    (growth : GeneralDictionaryOrdinaryTrace.Extension before after) (requests : List Request) :
    generated after.state after.interpretation requests =
      generated before.state before.interpretation requests := by
  obtain ⟨reserved,atoms,allocated,rfl⟩ := growth
  rfl

/-- Installation, merging, equality feedback and arbitrary certified refresh
retain the generated schema for a fixed request list. -/
theorem at_generated {roles : Roles.RoleDecls} (registry : Registry)
    (before after : State roles) (focus : Occurrence roles)
    (step : GeneralNominalFeedbackSteps.At registry before focus after) (requests : List Request) :
    generated after.context.state after.context.interpretation requests =
      generated before.context.state before.context.interpretation requests := by
  cases step with
  | enqueue => rfl
  | install packet enabled novel =>
    exact extension_generated _ _
      (GeneralDictionaryOrdinaryTrace.install_extension _ packet enabled.1.2.1) requests
  | merge first last _ _ _ _ =>
    exact extension_generated _ _ (GeneralDictionaryOrdinaryTrace.merge_extension _ first last) requests
  | refresh focus after certificate _ _ _ _ =>
    exact generated_eq _ _ certificate.refines.constructors certificate.interpretation requests
  | equate focus first last _ _ _ _ =>
    exact extension_generated _ _ (GeneralDictionaryOrdinaryTrace.equate_extension _ first last) requests

theorem trace_generated {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after)
    (requests : List Request) :
    generated after.context.state after.context.interpretation requests =
      generated before.context.state before.context.interpretation requests := by
  induction path with
  | refl => rfl
  | tail _ step ih => exact (at_generated registry _ _ _ step.choose_spec.2 requests).trans ih

/-- This asserts model validity, not syntactic preservation of the observation
certificate. No scalar-visibility or whole-view equality assumption occurs. -/
theorem generated_models_after_trace {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests)
    (declaration : Declaration) (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after model) :
    GeneralNominalMaterialization.Models after.context.state declaration capture report
      (generated after.context.state after.context.interpretation requests) model := by
  rw [trace_generated registry root before after path requests]
  have earlier := GeneralNominalFeedbackSteps.steps_models path model valid
  have good := generated_valid before.context.state before.context.interpretation requests observed model earlier.1
  refine ⟨good.2.2,?_,?_,?_⟩
  · intro entry member; rw [good.1] at member; cases member
  · intro entry member; rw [good.1] at member; cases member
  · intro entry member; rw [good.1] at member; cases member

theorem generated_shape_after_trace {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after)
    (requests : List Request)
    (observed : Observed before.context.state before.context.interpretation requests) :
    (generated after.context.state after.context.interpretation requests).variables = [] ∧
      (generated after.context.state after.context.interpretation requests).unknown = false := by
  rw [trace_generated registry root before after path requests]
  exact generated_shape _ _ _ observed

/-- Variable-only where clauses reduce actual materialization requests to the
same named root-output batch; arbitrary feedback is allowed in the trace. -/
theorem actual_requests_models_after_trace {roles : Roles.RoleDecls} (registry : Registry)
    (root : Occurrence roles) (before after : State roles)
    (path : B4Target.Steps (GeneralNominalFeedbackSteps.Step registry root) before after)
    (declaration : Declaration)
    (checked : DeclarationChecked registry.constructors roles declaration)
    (captures : GeneralNominalAllocation.Bindings)
    (variables : GeneralDictionaryVariableRequirements.VariableClauses declaration)
    (observed : Observed before.context.state before.context.interpretation (rootRequests declaration root))
    (capture : GeneralDeclarationDemands.Capture)
    (report : GeneralNominalRecursiveInspection.Report after.context.state)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models after model) :
    GeneralNominalMaterialization.Models after.context.state declaration capture report
      (generated after.context.state after.context.interpretation
        (requests after.context.state registry root declaration checked captures)) model := by
  rw [GeneralDictionaryObservedScalarRequests.requests_root _ _ _ _ _ _ variables]
  exact generated_models_after_trace registry root before after path _ observed declaration capture report model valid

end Yulang.GeneralDictionaryHistoricalRequestModels
