import Yulang.GeneralDictionaryVersionedGuarded232
import Yulang.GeneralDictionaryVersionedEvidenceAt232
namespace Yulang.GeneralDictionaryVersionedGuardedRegression232
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedInstalled232
open GeneralNominalVersionedJournal232

/-- Exact proved migration milestone. The first reachability proposition is
explicitly the OLD boundary's; it is not relabeled as new-boundary Reachable.
The transition and EvidenceAt use the NEW guarded boundary. -/
theorem guarded_nonvacuous_repair :
    B4TargetV8.Reachable (GeneralDictionaryHeadSharingBoundary220.boundary roles)
      sourceRegistry root GeneralDictionaryUpper230Step.after ∧
    (GeneralNominalVersionedBoundary232.boundary roles).Step registry root before installed ∧
    (∃ model, Models installed model) ∧
    GeneralNominalVersionedBoundary232.Local registry installed root (.selected declaration.id []) ∧
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedBoundary232.boundary roles) registry installed root ∧
    ∀ model, Models installed model →
      (GeneralNominalVersionedBoundary232.boundary roles).Evidence registry installed model root (.node declaration.id []) :=
  ⟨GeneralDictionaryUpper230Step.reachable,GeneralDictionaryVersionedGuarded232.step,inhabited,
    GeneralDictionaryVersionedEvidenceAt232.selected,GeneralDictionaryVersionedEvidenceAt232.evidenceAt,
    fun _ => GeneralDictionaryVersionedEvidence232.evidence⟩

end Yulang.GeneralDictionaryVersionedGuardedRegression232
