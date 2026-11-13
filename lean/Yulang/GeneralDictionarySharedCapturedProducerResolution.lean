import Yulang.GeneralDictionarySharedCapturedProducerGuard
import Yulang.GeneralDictionarySharedCapturedProducerEnabled
import Yulang.GeneralDictionarySharedCapturedConsequences
namespace Yulang.GeneralDictionarySharedCapturedProducerResolution
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalCommonBridge
open GeneralDictionarySharedOutputBinderScope GeneralDictionarySharedCapturedTargets
open GeneralDictionarySharedCapturedRefresh GeneralDictionarySharedCapturedProducer
open GeneralDeclarationExamples (roles)

theorem generated : Generated refreshed.current root producer :=
  GeneralDictionarySharedTrustTransport.generated_at
    GeneralDictionarySharedCapturedRefresh.step.choose_spec.2
    GeneralDictionarySharedCapturedInstallation.children_generated.1

noncomputable def installed : Tracked roles :=
  GeneralNominalSharedSteps.install refreshed candidate []

theorem install_step (novel : ¬ GeneralNominalFeedbackSteps.Committed refreshed.current candidate) :
    GeneralNominalSharedSteps.Step registry root refreshed installed :=
  ⟨producer,generated,.install candidate [] GeneralDictionarySharedCapturedProducerEnabled.enabled
    novel GeneralDictionarySharedCapturedProducerGuard.guard⟩

theorem installed_models : Models installed.current GeneralDictionarySharedCapturedModel.model :=
  (GeneralNominalSharedSteps.install_models (state := refreshed) (packet := candidate)
    (support := []) rfl _).mpr ⟨inhabited,branch_models⟩

theorem installed_scalar (assignment : Assignment) (valid : Models installed.current assignment) :
    CommonNominalFullCarrier.Equivalent (assignment 2).1 (.base .int) := by
  have pair := (GeneralNominalSharedSteps.install_models (state := refreshed) (packet := candidate)
    (support := []) rfl assignment).mp valid
  exact captured_int assignment pair.1 pair.2

theorem installed_context : installed.current.context = candidate.privateContext := rfl

/-- An enabled producer either already has committed semantic evidence, or
one actual guarded Shared step records it. No unproved novelty is assumed. -/
theorem resolved : ∃ finalState : Tracked roles,
    B4Target.Steps (GeneralNominalSharedSteps.Step registry root) refreshed finalState ∧
    GeneralNominalSharedSteps.SourceFormed registry root finalState ∧
    Models finalState.current GeneralDictionarySharedCapturedModel.model ∧
    (∀ assignment, Models finalState.current assignment →
      CommonNominalFullCarrier.Equivalent (assignment 2).1 (.base .int)) := by
  classical
  by_cases committed : GeneralNominalFeedbackSteps.Committed refreshed.current candidate
  · exact ⟨refreshed,.refl,formed,inhabited,fun assignment valid =>
      captured_int assignment valid (committed.1 assignment valid)⟩
  · have action := install_step committed
    exact ⟨installed,.tail (.refl) action,.update formed action,installed_models,installed_scalar⟩
end Yulang.GeneralDictionarySharedCapturedProducerResolution
