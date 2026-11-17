import Yulang.GeneralDictionaryUpper230Refresh
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryUpper230Step
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalInstall229
open GeneralDictionaryOptionalStage229
open GeneralDictionaryUpper230Base GeneralDictionaryUpper230Snapshot GeneralDictionaryUpper230Refresh

noncomputable abbrev after := GeneralNominalCenteredHeadMatStepJournal.refresh stage extendedContext

theorem known : GeneralNominalState.Known extendedSnapshot hi :=
  ⟨(5 : Fin 6),rfl,Or.inl (by decide +kernel)⟩

theorem step : GeneralDictionaryDefaultKernel208.Step registry root stage after :=
  ⟨root,.root,.refresh root extendedContext certificate hi
    GeneralDictionaryOptionalOpenRefresh229.upper_supported
    (GeneralDictionaryOptionalOpenRefresh229.generated_unknown 1) known⟩

theorem models (m : GeneralNominalCommonBridge.Assignment) :
    GeneralNominalCenteredHeadMatStepJournal.Models after m ↔
      GeneralNominalCenteredHeadMatStepJournal.Models stage m :=
  GeneralNominalCenteredHeadMatStepRefresh.refresh_models certificate

theorem inhabited : GeneralNominalCenteredHeadMatStepJournal.Models after model :=
  (models model).mpr stage_model

theorem reachable : B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles)
    sourceRegistry root after :=
  ⟨start,initial,.tail GeneralDictionaryOptionalReachable229.path step⟩

theorem not_stable : ¬ GeneralDictionaryHeadSharingBoundary220.Stable sourceRegistry stage root := by
  intro stable
  obtain ⟨focus,generated,action⟩ := step
  exact stable focus generated after action

theorem unresolved_output : ¬ GeneralNominalState.Known extendedSnapshot 4 :=
  GeneralDictionaryOptionalRegression229.no_output_refresh extendedContext certificate

theorem unresolved_lower : ¬ GeneralNominalState.Known extendedSnapshot lo :=
  GeneralDictionaryOptionalRegression229.no_lower_refresh extendedContext certificate

end Yulang.GeneralDictionaryUpper230Step
