import Yulang.GeneralDictionarySharedCapturedProducerResolution
import Yulang.GeneralDictionarySharedCapturedNovelty
import Yulang.GeneralDictionaryCapturedScalarRefresh

/-! Actual captured producer installation and exact scalar observation.
Raw consumer readiness is not the stronger I26 trusted decision guard. -/
namespace Yulang.GeneralDictionarySharedCapturedResumption
open GeneralNominalSaturationState GeneralNominalSupport GeneralNominalCommonBridge
open GeneralDictionarySharedOutputBinderScope GeneralDictionarySharedCapturedTargets
open GeneralDictionarySharedCapturedProducer GeneralDictionarySharedCapturedProducerResolution
open GeneralDeclarationExamples (roles)

theorem producer_step : GeneralNominalSharedSteps.Step registry root
    GeneralDictionarySharedCapturedRefresh.refreshed installed :=
  install_step GeneralDictionarySharedCapturedNovelty.not_committed

theorem producer_formed : GeneralNominalSharedSteps.SourceFormed registry root installed :=
  .update GeneralDictionarySharedCapturedRefresh.formed producer_step

theorem producer_prefix : B4Target.Steps (GeneralNominalSharedSteps.Step registry root)
    GeneralDictionarySharedCapturedInstallable.start installed :=
  .tail GeneralDictionarySharedCapturedRefresh.shared_prefix producer_step

noncomputable abbrev observed : Tracked roles :=
  GeneralDictionaryCapturedScalarRefresh.refreshed installed

theorem scalar_step : GeneralNominalSharedSteps.Step registry root installed observed :=
  GeneralDictionaryCapturedScalarRefresh.step installed installed_context installed_scalar

theorem observed_formed : GeneralNominalSharedSteps.SourceFormed registry root observed :=
  .update producer_formed scalar_step

theorem observed_prefix : B4Target.Steps (GeneralNominalSharedSteps.Step registry root)
    GeneralDictionarySharedCapturedInstallable.start observed :=
  .tail producer_prefix scalar_step

theorem models_exact (assignment : Assignment) :
    Models observed.current assignment ↔ Models installed.current assignment :=
  GeneralDictionaryCapturedScalarRefresh.models_exact installed installed_context installed_scalar assignment

theorem inhabited : Models observed.current GeneralDictionarySharedCapturedModel.model :=
  (models_exact _).mpr installed_models

theorem scalar_consequence (assignment : Assignment) (valid : Models observed.current assignment) :
    CommonNominalFullCarrier.Equivalent (assignment 2).1 (.base .int) :=
  installed_scalar assignment ((models_exact assignment).mp valid)

theorem producer_recorded : candidate ∈ observed.current.packets := by
  change candidate ∈ candidate :: _
  exact List.mem_cons_self

theorem consumer_raw_ready : ¬ GeneralNominalState.RootPending observed.current.context.state consumer.demand :=
  GeneralDictionaryCapturedScalarRefresh.consumer_raw_ready

end Yulang.GeneralDictionarySharedCapturedResumption
