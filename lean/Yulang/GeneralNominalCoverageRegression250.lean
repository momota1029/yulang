import Yulang.GeneralNominalCheckedInstall250
import Yulang.GeneralNominalPostInstallRegression250
/-! Certificate failures are not source-language rejection rules. These tests
show why public-model preservation alone does not guarantee all raw requests. -/
namespace Yulang.GeneralNominalCoverageRegression250
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 GeneralPresenceOwnerRewrite244
open GeneralNominalPostInstallRegression250 (frame)
open GeneralNominalJournalAppend250 (Delta)
open GeneralNominalFiniteInstallTrace250 (Command)
open GeneralNominalCheckedInstall250

def emptyDelta : Delta := ⟨[],[],[],[],[]⟩
def outside : Command := ⟨[(3,.emptyRecord)],emptyDelta⟩
def conflicting : Command := ⟨[(2,.exactEmpty),(2,.emptyRecord)],emptyDelta⟩

theorem outside_check_false : check frame outside = false := by decide

theorem outside_step_none : step frame outside = none := by simp [step,outside_check_false]

theorem conflicting_covered : GeneralNominalInstallCoverage250.coverageCheck frame.definitions conflicting.raw = true := by decide

theorem conflicting_incoherent : ¬ Coherent conflicting.raw := by
 intro coherent
 have impossible := coherent (2,.exactEmpty) (by simp [conflicting]) (2,.emptyRecord) (by simp [conflicting]) rfl
 cases impossible

theorem conflicting_check_false : check frame conflicting = false := by decide

theorem conflicting_step_none : step frame conflicting = none := by simp [step,conflicting_check_false]
end Yulang.GeneralNominalCoverageRegression250
