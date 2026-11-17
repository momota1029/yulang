import Yulang.GeneralDictionaryVersionedInstalled232
import Yulang.GeneralNominalVersionedInstallStep232
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace Yulang.GeneralDictionaryVersionedNovel232
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Step GeneralDictionaryUpper230Selected
open GeneralDictionaryVersionedNames231
open GeneralDictionaryVersionedInstalled232
open GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier

noncomputable def bad : Assignment :=
  GeneralNominalCenteredModelExtension.assign model names (fun _ => GeneralDictionaryOptionalOutput229.value)

theorem bad_old : GeneralNominalCenteredHeadMatStepJournal.Models after bad :=
  GeneralDictionaryDefaultJournalSupport213.models_assign after names (fun _ => GeneralDictionaryOptionalOutput229.value)
    (fun index => outside_journal index.val) GeneralDictionaryUpper230Step.inhabited

theorem bad_value (index : Fin 2) : (bad (names index)).1 = GeneralDictionaryOptionalOutput229.value :=
  GeneralNominalCenteredModelExtension.assign_value model names
    (fun _ => GeneralDictionaryOptionalOutput229.value) (by intro _ _ _; rfl) index

theorem bad_actual : (bad actual).1 = .emptyRecord := by
  have old : bad actual = model actual := by
    apply GeneralNominalCenteredModelExtension.assign_outside
    intro index same
    exact fresh_not_legacy index.val 8 same
  rw [old,actual_value]

theorem no_packet : ¬ GeneralNominalVersionedPlans231.Holds currentPlan bad := by
  intro valid
  have fits := GeneralNominalVersionedPlans231.shared_center valid.2.1
    (name := 0) (Or.inl (by decide +kernel))
  rw [GeneralDictionaryVersionedPacket231.binder_exact] at fits
  change GeneralNominalCaptureMerges.Fits bad
    ((GeneralNominalVersionedAllocation231.capture _ _ _ _ currentPacket.bindings).inputs 0) (bad actual).1 at fits
  rw [GeneralDictionaryUpper230Current.bindings_exact] at fits
  change Subtype (bad (names 0)).1 (bad actual).1 ∧ Subtype (bad actual).1 (bad (names 1)).1 at fits
  rw [bad_value 0,bad_value 1,bad_actual] at fits
  exact GeneralDictionaryOptionalOutput229.not_width fits

theorem not_committed : ¬ GeneralNominalVersionedInstallStep232.Committed before currentPlan := by
  intro committed
  exact no_packet (committed.1 bad ((lift_models after bad).mpr bad_old)).1

end Yulang.GeneralDictionaryVersionedNovel232
