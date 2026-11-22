import Yulang.GeneralDeclarativeReceiptSplit343

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 9500000
namespace Yulang.GeneralDeclarativeOrderedProjection343
open GeneralDeclarativeCurrentWorld343 (now)
open GeneralDeclarativeCurrentClosure343 (rules tree dict selected one_model current_place)
open GeneralDeclarativeCurrentHistory343 (cannot_substitute)
open GeneralDeclarativeVersionedRootGuard342 (actualDemand original_arguments original_targets)
open GeneralDeclarativeVersionedPhysical342 (current actual_children)
open GeneralDeclarativeVersionedTree342 (CurrentInstance root_requests)
open GeneralDeclarativeVersionedReceipt342 (ownerOutput current_order)
open GeneralDeclarativeLogicalChild343 (child output)
open GeneralDeclarativeFreshModel343 (kept)
open GeneralDeclarativeVersionedStale342 (active_history)
open GeneralDeclarativeStoppedPaired341 (Placement activeDemand placement_targets)
open GeneralDeclarativeVersionedRows342 (ordinary)
open GeneralWherePhysicalCommit319 (final newChild emission)
open GeneralWherePhysicalCurrentRead319 (plan)
open GeneralWherePhysicalCurrentPick319 (sourceRoot centers)
open GeneralWherePhysicalReobserve319 (updated)
open GeneralWhereOriginSingleCells318 (oldChild)
open GeneralWhereVersionCompiler317 (children schema)
open GeneralWhereVersionInstall317 (Models)
open GeneralWhereOriginSingleSource318 (sourceRegistry)
open GeneralWhereOriginSupport318 (journalSources)
open GeneralDictionaryJournalRefinement228Source (root interpretation)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralStoppedPlacement335 (SameDemand)
open CommonRoleOutermostResolver (All₂ Classify)

theorem root_registered : sourceRoot ∈ final.mixed.core.sites := by
  change sourceRoot ∈ updated.mixed.core.sites ++ GeneralWhereVersionInstall317.emitted plan
  rw [centers]
  exact List.mem_append_left _ List.mem_cons_self

theorem root_place : Placement final.mixed now root actualDemand := by
  refine ⟨sourceRoot,root_registered,rfl,rfl,?_,rfl⟩
  change All₂ (GeneralStoppedPlacement335.SameCapture now) actualDemand.arguments actualDemand.arguments
  rw [original_arguments]
  exact .cons ⟨alias_refl _,alias_refl _,alias_refl _⟩ .nil

theorem ordered_places : All₂ (Placement final.mixed now) (children current) [child kept] := by
  rw [actual_children]
  exact .cons current_place .nil

theorem exact_targets :
    actualDemand.outputs = [⟨0,4⟩] ∧
    (child kept).outputs = GeneralNominalCenteredHeadOutputs.requests final.mixed.core newChild.occurrence ∧
    (schema current).equations.map (ordinary current) =
      [ownerOutput,GeneralDeclarativeVersionedChildView342.lower,GeneralDeclarativeVersionedChildView342.upper] :=
  ⟨original_targets,placement_targets current_place,current_order⟩

/-- The concrete ordered positive projection now has both an actual
root placement and a mode-by-mode child placement. The semantic
paired result, exact targets, and the archived-site exclusion are
simultaneous, not claims from separate models or separate runs. -/
theorem projected (m : Assignment) (fit : Models final m) :
    ∃ n, Models final n ∧ (∀ k ∈ journalSources final, n k = m k) ∧
      GeneralDeclarativeHead320.Models now n ∧
      Placement final.mixed now root actualDemand ∧
      All₂ (Placement final.mixed now) (children current) [child kept] ∧
      actualDemand.outputs = [⟨0,4⟩] ∧
      GeneralSourceDictionaries.ErasedEvidence (CurrentInstance n) root dict ∧
      Classify rules actualDemand (.selected dict) ∧
      GeneralDeclarativeExactDictionary337.Evidence sourceRegistry interpretation n actualDemand dict ∧
      ¬ SameDemand now (activeDemand final.mixed oldChild) (child kept) := by
  obtain ⟨n,raw,agrees,present,tree,latest,dictionary,_⟩ := one_model m fit
  exact ⟨n,raw,agrees,present,root_place,ordered_places,original_targets,tree,latest,dictionary,
    cannot_substitute n raw present⟩

end Yulang.GeneralDeclarativeOrderedProjection343
