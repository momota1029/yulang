import Yulang.GeneralNominalRebaseViewActivation243
import Yulang.GeneralDictionaryRebaseActivation230243
set_option backward.isDefEq.respectTransparency false
/-! The concrete nominal and live expressions pass the executable activation
check even with both private cells already reserved. No kernel trace is added. -/
namespace Yulang.GeneralDictionaryRebaseViewActivation230243
open GeneralNominalRebaseViewActivation243
open GeneralNominalRebaseEscapedProjection242
open GeneralDictionaryRebaseActivation230243 (raw newEntries external_entries)
open GeneralDictionaryRebase230Private241 (publicAtoms rebased newBindings)
open GeneralDictionaryOptionalInstall229 (model)
open GeneralDictionaryJournalRefinement228Source (snapshot root)
open GeneralDictionaryOptionalInitial229 (declaration)
open Core.PresenceGeneration (CompTerm)

def view : GeneralNominalRebaseRawView243.View :=
 GeneralNominalRebaseRawView243.compile raw CompTerm.var

def sites : List GeneralNominalRebaseLiveView243.Site :=
 GeneralNominalRebaseLiveView243.compileAll GeneralDictionaryRebaseActivation230243.sites CompTerm.var

theorem finite_check : check newEntries view publicAtoms sites = true := by
 rw [show publicAtoms = GeneralNominalAllocation.cross GeneralDictionaryRebase230Private241.oldBindings ++
   GeneralNominalRecursiveInspection.selfChecks snapshot GeneralDictionaryOptionalInstall229.calculated by
     unfold GeneralDictionaryRebase230Private241.publicAtoms
     rw [GeneralDictionaryOptionalInstall229.report_exact]]
 decide

theorem checked : Checked newEntries view publicAtoms sites :=
 (check_iff newEntries view publicAtoms sites).mp finite_check

theorem original : Consumers view publicAtoms sites model := by
 have old := GeneralDictionaryRebaseActivation230243.original_consumers
 refine ⟨?_,old.2.1,?_⟩
 · exact (GeneralNominalRebaseRawView243.compile_exact raw CompTerm.var model).mpr old.1
 · exact (GeneralNominalRebaseLiveView243.all_holds
     GeneralDictionaryRebaseActivation230243.sites CompTerm.var model).mpr old.2.2

theorem activated : Preserves newEntries rebased model ∧ Definitions newEntries rebased ∧
 Consumers view publicAtoms sites rebased ∧ ValuesAgree sites rebased model :=
 activate newEntries (GeneralNominalRebaseDefinitions241.coherent snapshot.seed root.identity declaration.id
   newBindings declaration.inputNames) external_entries view publicAtoms sites checked model original

theorem all_sources (sourceModel : GeneralNominalCommonBridge.Assignment) :
 Consumers view publicAtoms sites sourceModel ↔
 ∃ next, Preserves newEntries next sourceModel ∧ Definitions newEntries next ∧
 Consumers view publicAtoms sites next ∧ ValuesAgree sites next sourceModel :=
 projection_iff newEntries (GeneralNominalRebaseDefinitions241.coherent snapshot.seed root.identity declaration.id
   newBindings declaration.inputNames) external_entries view publicAtoms sites checked sourceModel
end Yulang.GeneralDictionaryRebaseViewActivation230243
