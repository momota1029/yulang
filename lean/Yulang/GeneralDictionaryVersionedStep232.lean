import Yulang.GeneralDictionaryVersionedNovel232
import Yulang.GeneralDictionaryVersionedEvidence232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedStep232
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralDictionaryVersionedInstalled232
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232

theorem enabled : GeneralNominalVersionedInstallStep232.Enabled registry before effect := by
  refine ⟨rfl,snapshot,?_⟩
  obtain ⟨model,valid⟩ := GeneralDictionaryVersionedCompletion231.inhabited
  exact ⟨model,installation_models valid⟩

theorem step : GeneralNominalVersionedInstallStep232.Step registry root before installed :=
  .install effect enabled .root GeneralDictionaryVersionedNovel232.not_committed

/-- Actual old operational reachability followed by an actual new installation.
This is a migration trace, not full successor SourceBoundary Reachable/Stable. -/
theorem nonvacuous_migration :
    B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles) sourceRegistry root after ∧
    GeneralNominalVersionedInstallStep232.Step registry root before installed ∧
    (∃ model, Models installed model) ∧
    ∀ model, Models installed model →
      GeneralNominalVersionedEvidence231.Evidence registry installed.core model root (.node declaration.id []) :=
  ⟨GeneralDictionaryUpper230Step.reachable,step,inhabited,fun _ => GeneralDictionaryVersionedEvidence232.evidence⟩

end Yulang.GeneralDictionaryVersionedStep232
