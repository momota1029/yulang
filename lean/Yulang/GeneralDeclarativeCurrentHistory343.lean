import Yulang.GeneralDeclarativeCurrentClosure343
import Yulang.GeneralDeclarativeVersionedStale342

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14500
set_option maxHeartbeats 7300000
namespace Yulang.GeneralDeclarativeCurrentHistory343
open GeneralDeclarativeCurrentWorld343 (now grows)
open GeneralDeclarativeCurrentClosure343 (dict rules one_model)
open GeneralDeclarativeFreshModel343 (kept)
open GeneralDeclarativeLogicalChild343 (child output)
open GeneralDeclarativeFreshValues343 (mode_match)
open GeneralDeclarativePlacement343 (view symbolic)
open GeneralDeclarativeVersionedStale342 (historical active_history)
open GeneralDeclarativeVersionedSeparation342 (not_current_lower)
open GeneralDeclarativeVersionedRootGuard342 (actualDemand)
open GeneralDeclarativeGrowth327 (restrict)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralWhereOriginSingleCells318 (oldChild loOld loNow)
open GeneralWherePhysicalCommit319 (final newChild)
open GeneralWhereVersionInstall317 (Models)
open GeneralWhereOriginSingleSource318 (sourceRegistry)
open GeneralDictionaryJournalRefinement228Source (interpretation)
open GeneralNominalCommonBridge (Assignment)
open GeneralStoppedPlacement335 (SameDemand Meaning demands_models)
open GeneralDeclarativeStoppedPaired341 (activeDemand Placement)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans eqv_symm)
open CommonRoleOutermostResolver (All₂ Classify)

/-- Comparing the historical raw site directly against the canonical
ordinary compiler output still fails, even after all justified new
aliases and fresh aggregate definitions have been added. -/
theorem cannot_substitute (m : Assignment) (raw : Models final m)
    (fit : GeneralDeclarativeHead320.Models now m) :
    ¬ SameDemand now (activeDemand final.mixed oldChild) (child kept) := by
  intro old
  have f : GeneralDeclarativeHead320.Models view m := restrict grows m fit
  have written : GeneralDeclarativeHead320.Models (output kept) m := ((model_append m).mp f).1
  have current := mode_match m raw written
  have both := (demands_models fit old).2.2
  rw [active_history] at both
  change All₂ (Meaning m) [historical] [symbolic] at both
  cases both with
  | cons lower _ =>
    exact not_current_lower m raw (eqv_trans lower.1 (eqv_symm current.1))

theorem nonvacuous :
    ∃ m, Models final m ∧ GeneralDeclarativeHead320.Models now m ∧
      Classify rules actualDemand (.selected dict) ∧
      GeneralDeclarativeExactDictionary337.Evidence sourceRegistry interpretation m actualDemand dict ∧
      Placement final.mixed now newChild.occurrence (child kept) ∧
      ¬ SameDemand now (activeDemand final.mixed oldChild) (child kept) := by
  obtain ⟨n,raw,_,valid,_,picked,dictionary,current⟩ := one_model _ GeneralWherePhysicalCommit319.models
  exact ⟨n,raw,valid,picked,dictionary,current,cannot_substitute n raw valid⟩

end Yulang.GeneralDeclarativeCurrentHistory343
