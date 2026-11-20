import Yulang.GeneralDepthTwoPhaseCut300

open Yulang
open GeneralGeneratedNestedSource299 (initial root)
open GeneralDepthTwoFirstInstall300 (after)
open GeneralDepthTwoSecondInstall300 (final)
open GeneralGeneratedNestedPredictions299 (middle terminal)

def main : IO Unit := do
  let midRaw := after.core.erased.current.sites.map (fun x => x.occurrence.identity)
  let finalRaw := final.core.erased.current.sites.map (fun x => x.occurrence.identity)
  unless midRaw == [root.identity,middle.identity] &&
      finalRaw == [root.identity,middle.identity,terminal.identity] do
    throw (IO.userError "wrong recorded raw occurrence set")
  IO.println "PASS the terminal frame's raw occurrence is absent before the second install"
  let a := GeneralNominalVersionedRefresh232.refresh initial after.core.erased.current.context
  let b := GeneralNominalVersionedRefresh232.refresh after final.core.erased.current.context
  unless a.core.erased.current.edges.length == 0 && b.core.erased.current.edges.length == 1 do
    throw (IO.userError "refresh comparison unexpectedly emitted a raw edge")
  IO.println "PASS structural refresh with the later context does not reproduce either install's edge change"
