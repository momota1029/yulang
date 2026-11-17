import Yulang.GeneralNominalVersionedMigration232
import Yulang.GeneralDictionaryVersionedStep232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedReachable232
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedInstalled232
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedMigration232

theorem old_path : B4Target.Steps (GeneralDictionaryDefaultKernel208.Step registry root)
    start GeneralDictionaryUpper230Step.after :=
  .tail GeneralDictionaryOptionalReachable229.path GeneralDictionaryUpper230Step.step

theorem reachable : Reachable registry context root installed :=
  .tail (lift_path old_path) (.install GeneralDictionaryVersionedStep232.step)

/-- Source-initial nonempty operational migration, retaining full old/new records.
No complete V8 boundary, final solver stability, or global termination is asserted. -/
theorem nonvacuous_reachable_evidence :
    Reachable registry context root installed ∧ (∃ m, Models installed m) ∧
    ∀ m, Models installed m →
      GeneralNominalVersionedEvidence231.Evidence registry installed.core m root (.node declaration.id []) :=
  ⟨reachable,inhabited,fun _ => GeneralDictionaryVersionedEvidence232.evidence⟩

end Yulang.GeneralDictionaryVersionedReachable232
