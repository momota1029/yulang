import Yulang.GeneralNominalVersionedCapture231
import Yulang.GeneralDictionaryVersionedSupport231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedNames231
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Step
open GeneralNominalAggregateVersion231
open CommonNominalFullCarrier

abbrev oldBindings := GeneralDictionaryDefaultMergeRevisionProbe210.twice 0 4 2
abbrev newBindings := GeneralDictionaryDefaultMergeRevisionProbe210.twice 0 2 2
abbrev freshName (purpose : Nat) := slot snapshot.seed root.identity declaration.id purpose 0 newBindings
abbrev oldVersionName (purpose : Nat) := slot snapshot.seed root.identity declaration.id purpose 0 oldBindings

theorem version_changed (purpose : Nat) : oldVersionName purpose ≠ freshName purpose := by
  intro same
  have different := (slot_eq_iff snapshot.seed root.identity declaration.id purpose 0).mp same
  change [(4,2),(4,2)] = [(2,2),(2,2)] at different
  cases different

theorem fresh_above (purpose : Nat) : 4 < freshName purpose := above_seed _ _ _ _ _ _

theorem fresh_not_legacy (purpose other : Nat) :
    freshName purpose ≠ GeneralNominalCenters.fresh snapshot.seed root.identity declaration.id other 0 0 :=
  not_legacy_slot _ _ _ _ _ _ _ _ _ _

theorem fresh_outside (purpose : Nat) :
    freshName purpose ∉ GeneralDictionaryVersionedSupport231.pool := by
  intro member
  simp only [GeneralDictionaryVersionedSupport231.pool,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with eq | eq | eq | eq | eq | eq | eq | eq
  · have bound := fresh_above purpose; omega
  · have bound := fresh_above purpose; omega
  · have bound := fresh_above purpose; omega
  · have bound := fresh_above purpose; omega
  · have bound := fresh_above purpose; omega
  · exact fresh_not_legacy purpose 0 eq
  · exact fresh_not_legacy purpose 1 eq
  · exact fresh_not_legacy purpose 8 eq

theorem outside_journal (purpose : Nat) :
    freshName purpose ∉ GeneralDictionaryDefaultJournalSupport213.journalSources after :=
  fun present => fresh_outside purpose (GeneralDictionaryVersionedSupport231.journal_support present)

abbrev names (index : Fin 2) : Nat := freshName index.val
abbrev values (_ : Fin 2) : Ty := .emptyRecord
noncomputable def extended := GeneralNominalCenteredModelExtension.assign model names values

theorem retains_journal : GeneralNominalCenteredHeadMatStepJournal.Models after extended :=
  GeneralDictionaryDefaultJournalSupport213.models_assign after names values
    (fun index => outside_journal index.val) GeneralDictionaryUpper230Step.inhabited

theorem fresh_value (index : Fin 2) : (extended (names index)).1 = .emptyRecord :=
  GeneralNominalCenteredModelExtension.assign_value model names values (by intro _ _ _; rfl) index

theorem old_value (name : Nat) (member : name ∈ GeneralDictionaryVersionedSupport231.pool) :
    extended name = model name := by
  apply GeneralNominalCenteredModelExtension.assign_outside
  intro index same
  apply fresh_outside index.val
  change freshName index.val = name at same
  rw [same]
  exact member

theorem lower_retained : (extended lo).1 = GeneralDictionaryOptionalOutput229.value := by
  rw [old_value lo (by simp [GeneralDictionaryVersionedSupport231.pool])]
  exact lower_value

theorem upper_retained : (extended hi).1 = .emptyRecord := by
  rw [old_value hi (by simp [GeneralDictionaryVersionedSupport231.pool])]
  exact upper_value

theorem actual_retained : (extended actual).1 = .emptyRecord := by
  rw [old_value actual (by simp [GeneralDictionaryVersionedSupport231.pool])]
  exact actual_value

theorem two_retained : (extended 2).1 = .emptyRecord := by
  rw [old_value 2 (by simp [GeneralDictionaryVersionedSupport231.pool])]
  rfl

theorem output_retained : (extended 4).1 = GeneralDictionaryOptionalOutput229.value := by
  rw [old_value 4 (by simp [GeneralDictionaryVersionedSupport231.pool])]
  rfl
end Yulang.GeneralDictionaryVersionedNames231
