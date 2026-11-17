import Yulang.GeneralNominalVersionedAcyclic232
import Yulang.GeneralDictionaryVersionedInstalled232
import Yulang.GeneralDictionaryOptionalStageSafety229
set_option backward.isDefEq.respectTransparency false

/-! Concrete mixed-journal semantic acyclicity witnessed by the actual
installed model. New aggregate names have width form; all other sources retain
the earlier four-form assignment. Not a full solver stability theorem. -/
namespace Yulang.GeneralDictionaryVersionedAcyclic232
open GeneralDictionaryOptionalCycles229
open GeneralDictionaryVersionedNames231
open GeneralDictionaryVersionedInstalled232
open GeneralDictionaryOptionalInstall229

theorem model_form (identity : Nat) : ∃ form : Form, (extended identity).1 = form.value := by
  classical
  by_cases assigned : ∃ index : Fin 2, names index = identity
  · obtain ⟨index,rfl⟩ := assigned
    exact ⟨.width,fresh_value index⟩
  · have retained : extended identity = model identity :=
      GeneralNominalCenteredModelExtension.assign_outside model names values
        (fun index same => assigned ⟨index,same⟩)
    rw [retained]
    exact ⟨GeneralDictionaryOptionalStageSafety229.sourceForm identity,
      GeneralDictionaryOptionalStageSafety229.model_form identity⟩

theorem installed_model : GeneralNominalVersionedJournal232.Models installed extended :=
  (models_iff extended).mpr ⟨retains_journal,GeneralDictionaryVersionedMerge231.merge_model⟩

theorem acyclic (origin) : ¬ GeneralNominalVersionedCycles232.Cyclic installed origin :=
  GeneralNominalVersionedAcyclic232.acyclic installed_model model_form origin

theorem no_root_cycle (root) : ¬ GeneralNominalVersionedCycles232.RootCycle installed root := by
  rintro (⟨index,cycle⟩ | ⟨site,_,_,index,cycle⟩)
  · exact acyclic _ cycle
  · exact acyclic _ cycle

theorem no_candidate_cycle (registry root) :
    ¬ GeneralNominalVersionedCycles232.CandidateCycle registry installed root := by
  rintro ⟨plan,_,entry,_,cycle⟩
  exact acyclic _ cycle

end Yulang.GeneralDictionaryVersionedAcyclic232
