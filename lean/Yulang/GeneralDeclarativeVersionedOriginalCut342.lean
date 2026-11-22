import Yulang.GeneralDeclarativeVersionedRows342
import Yulang.GeneralDeclarativeStoppedObstruction341
import Yulang.GeneralWhereVersionRegression317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeclarativeVersionedOriginalCut342
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralLiveCompoundRegistry316 (registry sourceRegistry declaration)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralLiveCompoundFullResult316 (dictionary)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralWhereVersionInstall317 (before fixed Models)
open GeneralWhereVersionRootReport317 (plan same)
open GeneralWhereVersionCase317 (lower upper occ)
open GeneralWhereVersionCompiler317 (schema children)
open GeneralWhereVersionRegression317 (Accepts Evidence accepted_root acceptance_sound)
open GeneralWhereVersionSemantics317 (Holds)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralNominalCenteredFrame179 (Agree)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatSchemas (Equation)
open GeneralDeclarativeVersionedRows342 (ordinary)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralWhereVersionCommit317 (core)

theorem reported_targets :
    ((schema plan).equations.map (ordinary plan)).map GeneralDeclarativeHead320.Equation.left =
      [4,lower,upper] := by
  rw [GeneralDeclarativeVersionedRows342.fixed,
    ← GeneralWhereVersionRecompile317.schema_eq same,GeneralWhereVersionCase317.rows]
  rfl

/-- The exact original C316 fixture, not the distinct-binder C319
fixture. Its existing solver is still obstructed. In the isolated
versioned successor the genuinely reported children and the current
root frame have a conservative real common model. -/
theorem original_cut (m : Assignment) (fit : GeneralNominalVersionedJournal232.Models after m) :
    ¬ GeneralDeclarativeStoppedFold340.Produces sourceRegistry after root ∧
    GeneralWhereVersionInstall317.InstallStep sourceRegistry before fixed ∧
    Accepts root dictionary ∧
    ∃ n, Models fixed n ∧ Agree (sources after) m n ∧
      Frame registry core root declaration.id plan ∧ Holds plan n ∧ Evidence n root dictionary := by
  have prior : Models before m := ⟨fit,(by intro _ absent; cases absent)⟩
  obtain ⟨n,correct,sameNames⟩ := GeneralWhereVersionPreserve317.exact_legacy_projection m prior
  obtain ⟨frame,typed,_,_⟩ := GeneralWhereVersionCurrentCert317.current_certified n correct
  exact ⟨GeneralDeclarativeStoppedObstruction341.not_produces,GeneralWhereVersionInstall317.step,
    accepted_root,n,correct,sameNames,frame,typed,acceptance_sound n correct accepted_root⟩

end Yulang.GeneralDeclarativeVersionedOriginalCut342
