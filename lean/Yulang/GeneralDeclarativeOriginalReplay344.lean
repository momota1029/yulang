import Yulang.GeneralDeclarativeStampedPort344
import Yulang.GeneralDeclarativeVersionedOriginalCut342

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 17000
set_option maxHeartbeats 11000000
namespace Yulang.GeneralDeclarativeOriginalReplay344
open GeneralWhereVersionInstall317 (before fixed Models InstallStep)
open GeneralWhereVersionSnapshot317 (context)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundRegistry316 (sourceRegistry)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralWhereVersionCommit317 (core)
open GeneralDictionaryJournalRefinement228Source (root)
open GeneralNominalCenteredHeadMatEffects (Ready)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeclarativeCommitPackage344 (Witness)
open GeneralDeclarativePackageBoundary344 (actual no_unchanged_stamp)

theorem ready : Ready fixed.mixed.core root rootPlan := by
  intro out touch
  rw [GeneralWhereVersionInstall317.mixed_eq] at touch
  have old := (GeneralWhereVersionCommit317.requests_iff root out).mp touch
  cases GeneralLiveCompoundAdmin316.all_requests GeneralLiveCompoundPost316.raw_sites_after old
  exact ⟨.explicit ⟨0,0,GeneralDictionaryOptionalExpression229.pattern⟩,rfl,rfl⟩

/-- Same original C316 fixture in the isolated C317 versioned
transaction, not the distinct-binder C319 example. The original
stopped solver has neither the required true versioned stamp nor
the old full raw packet producer. -/
theorem contrast (m : Assignment) (fit : Models fixed m) :
    ¬ GeneralDeclarativeStoppedFold340.Produces sourceRegistry after root ∧
    (∀ past, past.versionedWhere = [] → ¬ InstallStep sourceRegistry past before) ∧
    ∃ prepared view ports whereRows rootRows n,
      Witness fixed rootPlan m n [4] prepared view ports whereRows rootRows := by
  refine ⟨GeneralDeclarativeStoppedObstruction341.not_produces,?_,?_⟩
  · intro past same
    apply no_unchanged_stamp
    rw [same]
  · exact actual GeneralWhereVersionInstall317.step m fit [4] ready

end Yulang.GeneralDeclarativeOriginalReplay344
