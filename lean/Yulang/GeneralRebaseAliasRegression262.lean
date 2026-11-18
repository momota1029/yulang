import Yulang.GeneralRebaseRootTrace262

namespace Yulang.GeneralRebaseAliasRegression262
open GeneralFiniteAliasClosure262

theorem chain : connected [(0,1),(1,2)] 0 2 = true := by decide
theorem reversed : connected [(0,1),(1,2)] 2 0 = true := by decide
theorem disconnected : connected [(0,1),(2,3)] 0 3 = false := by decide
theorem isolated_same : connected [] 99 99 = true := by decide
theorem isolated_other : connected [] 99 100 = false := by decide
theorem outside_middle : connected [(4,99),(99,7)] 4 7 = true := by decide

open GeneralNominalCenteredHeadAllocMergeState
open GeneralNominalCenteredHeadAllocMergeConflict (focus)
open GeneralRebaseMergeRequests261 (outputs)

/-- The computed list agrees with the two real requests, not just membership. -/
theorem actual_requests (atoms) :
 GeneralRebaseExecutableRequests262.requests (stage atoms).core focus = outputs := by
 unfold GeneralRebaseExecutableRequests262.requests
 dsimp only
 change ((stage atoms).core.erased.current.sites.filter fun site =>
   GeneralFiniteAliasSearch262.connected (stage atoms).core.erased.current.aliases
     focus.identity site.occurrence.identity).flatMap (fun site => site.occurrence.demand.outputs) = outputs
 have same : (fun site : GeneralNominalDemandMerging.Site GeneralNominalCenteredHeadAllocMergeSource.roles =>
   GeneralFiniteAliasSearch262.connected (stage atoms).core.erased.current.aliases focus.identity site.occurrence.identity) =
   (fun site => GeneralFiniteAliasClosure262.connected (stage atoms).core.erased.current.aliases focus.identity site.occurrence.identity) :=
   funext fun site => GeneralFiniteAliasSearch262.reference_eq (stage atoms).core.erased.current focus.identity site.occurrence.identity
 rw [same]
 rfl
end Yulang.GeneralRebaseAliasRegression262
