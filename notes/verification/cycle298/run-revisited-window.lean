import Yulang.GeneralRebaseExplicitWindow298
open Yulang
open GeneralDictionaryOutputDepth252 (initial)
open GeneralRebasePreInstallReplay297 (after)
open GeneralRebaseExplicitWindow298.Actual (evaluated window)
open GeneralRebaseOutputDepthSuccessor271 (owner output)
open GeneralRebaseRefreshCode298 (rawCode)
open GeneralRebaseLocalProgram298 (emit)
open GeneralRebaseCandidateChecks267 (known)

def main : IO Unit := do
  let prior := GeneralRebaseLiveProjection264.project [owner] [output] initial
  let refreshed := GeneralRebaseLiveProjection264.project [owner] [output] after
  unless prior.remaining.length == 2 && refreshed.remaining == prior.remaining &&
      !(known initial.core.erased.current.context.state 0) && known after.core.erased.current.context.state 0 &&
      window.length == 1 && (emit rawCode).length == 1 && evaluated.map (·.remaining) == [[]] do
    throw (IO.userError "actual revisited source replay diverged")
  IO.println "PASS the actual earlier raw observation changes while both projected lists still contain two facts."
  IO.println "PASS the verified local program at the new representative yields one strict exit with no remaining facts."
  IO.println "A separate Lean proof supplies the actual raw install and exact model/leaf payload; the runtime replays the finite data only."
