import Yulang.GeneralNominalVersionedSourceBoundary232
import Yulang.GeneralDictionaryVersionedGuardedRegression232
namespace Yulang.GeneralDictionaryVersionedSourceRegression232
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedInstalled232
open GeneralNominalVersionedJournal232

theorem guarded_step : (GeneralNominalVersionedSourceBoundary232.boundary roles).Step sourceRegistry root before installed :=
  GeneralDictionaryVersionedGuarded232.step

theorem selected : GeneralNominalVersionedSourceBoundary232.Local sourceRegistry installed root (.selected declaration.id []) :=
  GeneralNominalVersionedSourceBoundary232.local_iff.mpr GeneralDictionaryVersionedEvidenceAt232.selected

theorem evidenceAt :
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedSourceBoundary232.boundary roles) sourceRegistry installed root :=
  GeneralNominalVersionedSourceBoundary232.evidenceAt_iff.mpr GeneralDictionaryVersionedEvidenceAt232.evidenceAt

/-- Source-facing encoded V8 regression with actual guarded installation.
The OLD reachable prefix is explicitly retained; a complete initial trace
using only the new boundary's Step relation is still a separate obligation. -/
theorem nonvacuous_source_repair :
    B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles)
      sourceRegistry root GeneralDictionaryUpper230Step.after ∧
    (GeneralNominalVersionedSourceBoundary232.boundary roles).Step sourceRegistry root before installed ∧
    (∃ model, Models installed model) ∧
    GeneralNominalVersionedSourceBoundary232.Local sourceRegistry installed root (.selected declaration.id []) ∧
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedSourceBoundary232.boundary roles) sourceRegistry installed root ∧
    ∀ model, Models installed model →
      (GeneralNominalVersionedSourceBoundary232.boundary roles).Evidence sourceRegistry installed model root (.node declaration.id []) :=
  ⟨GeneralDictionaryUpper230Step.reachable,guarded_step,inhabited,selected,evidenceAt,
    fun _ => GeneralDictionaryVersionedEvidence232.evidence⟩

end Yulang.GeneralDictionaryVersionedSourceRegression232
