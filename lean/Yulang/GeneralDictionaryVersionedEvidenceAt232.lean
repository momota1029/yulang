import Yulang.GeneralDictionaryVersionedSelected232
import Yulang.GeneralNominalVersionedBoundary232
import Yulang.B4SkeletonV8
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedEvidenceAt232
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedInstalled232
open GeneralNominalVersionedJournal232

theorem selected : GeneralNominalVersionedBoundary232.Local registry installed root (.selected declaration.id []) :=
  GeneralNominalVersionedBoundary232.local_iff.mpr GeneralDictionaryVersionedSelected232.selected

/-- The literal EvidenceAt of the actual guarded boundary, not a newly named
replacement. Root/generated scope is discharged concretely; no stability
assumption is needed for the conclusion in this terminal state. Operational
Reachable for this new boundary has NOT been proved by the migration path. -/
theorem evidenceAt : B4SkeletonV8.EvidenceAt (GeneralNominalVersionedBoundary232.boundary roles) registry installed root := by
  intro model valid demand key children dictionaries reached _stable _childStable chosen childEvidence
  have same : demand = root := reached.elim id GeneralDictionaryVersionedInstallClosed232.generated_only
  subst demand
  have same := GeneralNominalVersionedBoundary232.local_functional selected chosen
  cases same
  cases childEvidence
  exact GeneralDictionaryVersionedEvidence232.evidence valid

theorem nonvacuous :
    (∃ model, Models installed model) ∧
    GeneralNominalVersionedBoundary232.Local registry installed root (.selected declaration.id []) ∧
    B4SkeletonV8.EvidenceAt (GeneralNominalVersionedBoundary232.boundary roles) registry installed root ∧
    ∀ model, Models installed model →
      (GeneralNominalVersionedBoundary232.boundary roles).Evidence registry installed model root (.node declaration.id []) :=
  ⟨inhabited,selected,evidenceAt,fun _ => GeneralDictionaryVersionedEvidence232.evidence⟩

end Yulang.GeneralDictionaryVersionedEvidenceAt232
