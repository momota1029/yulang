import Yulang.GeneralDeclarativeNativeReplay347
import Yulang.GeneralDeclarativeCurrentBarrier345

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
set_option maxHeartbeats 24000000
namespace Yulang.GeneralDeclarativeNativePlacement347
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralLiveCompoundChildSite316 (child childSite)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralDictionaryJournalRefinement228Source (root roles snapshot)
open GeneralDeclarativeCurrentBarrier345 (view)
open GeneralDeclarativeRootReplay344 (actualDemand requests_exact)
open GeneralDeclarativeNativeReplay347 (keep no_same_endpoints)
open GeneralDeclarativeLogicalChild343 (output)
open GeneralDeclarativeStoppedPaired341 (Placement activeDemand)
open GeneralStoppedPlacement335 (demands_models Meaning)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalSaturationState (Alias)

theorem current_requests : requests after.core root = [⟨0,4⟩] := by
  classical
  unfold requests
  rw [GeneralLiveCompoundPost316.raw_sites_after]
  have same : Alias after.core.erased.current root.identity
      (GeneralNominalDemandMerging.pointSite root).occurrence.identity := .refl _
  simp [List.filter_cons,same]
  split <;> rfl

/-- The fixture uses the same effective root request list as the
standalone current compiler, not a modified demand. -/
theorem exact_root : actualDemand rootPlan view = GeneralDeclarativeVersionedRootGuard342.actualDemand := by
  have left : (actualDemand rootPlan view).outputs = [⟨0,4⟩] := by
    rw [requests_exact,GeneralLiveCompoundPostRootHead316.frame.occurrence_eq]
    exact current_requests
  have right := GeneralDeclarativeVersionedRootGuard342.original_targets
  have head : (actualDemand rootPlan view).arguments =
      GeneralDeclarativeVersionedRootGuard342.actualDemand.arguments := rfl
  have role : (actualDemand rootPlan view).role =
      GeneralDeclarativeVersionedRootGuard342.actualDemand.role := rfl
  generalize actualDemand rootPlan view = d at *
  generalize GeneralDeclarativeVersionedRootGuard342.actualDemand = e at *
  cases d; cases e
  simp_all

theorem literal_child {s : GeneralDeclarativeHead320.State} {d : GeneralDeclarativeDemand320.Demand}
    (placed : Placement after s child d) :
    GeneralStoppedPlacement335.SameDemand s (activeDemand after childSite) d := by
  obtain ⟨site,located,identity,agree⟩ := placed
  rw [GeneralLiveCompoundPost316.centers_after] at located
  rcases List.mem_cons.mp located with onRoot|onChild
  · subst site
    have bad : root.identity = child.identity := congrArg GeneralSourceDictionaries.Occurrence.identity identity
    exact False.elim ((by decide +kernel : root.identity ≠ child.identity) bad)
  · cases List.mem_singleton.mp onChild
    exact agree

theorem endpoints_of_placement {s : GeneralDeclarativeHead320.State} {m : Assignment} {a : Capture}
    (valid : GeneralDeclarativeHead320.Models s m)
    (placed : Placement after s child ⟨1,[a],[]⟩) :
    CommonNominalFullCarrier.Equivalent (m lo).1 (m a.lower).1 ∧
    CommonNominalFullCarrier.Equivalent (m hi).1 (m a.upper).1 := by
  have h := (demands_models valid (literal_child placed)).2.2
  change CommonRoleOutermostResolver.All₂ (Meaning m)
    ([⟨lo,childSite.center 0,hi⟩] : List Capture) [a] at h
  cases h with
  | cons exactArg _ => exact ⟨exactArg.1,exactArg.2.2⟩

/-- This is a semantic, not merely a fresh-name mismatch: no sound
ordinary view can place the independently compiled witnessed child
on the real legacy native site, with the current root and targets
unchanged. -/
theorem placement_impossible {s : GeneralDeclarativeHead320.State}
    (extension : GeneralDeclarativeGrowth327.Extends (output keep) s)
    (m : Assignment) (native : Models after m) (fit : GeneralDeclarativeHead320.Models s m) :
    ¬ Placement after s child (GeneralDeclarativeLogicalChild343.child keep) := by
  intro offered
  exact no_same_endpoints m native (GeneralDeclarativeGrowth327.restrict extension m fit)
    (endpoints_of_placement fit offered)

end Yulang.GeneralDeclarativeNativePlacement347
