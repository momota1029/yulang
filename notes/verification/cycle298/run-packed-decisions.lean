import Yulang.GeneralRebaseAlignedScan298
open Yulang
open GeneralRebasePackedDepthDecision298 (base body ask)
open GeneralRebasePackedDecision298 (reduce encode)
open GeneralRebasePreInstallReplay297 (after candidate xs)
open GeneralRebaseAlignedScan298 (scan symbolic)
open GeneralRebaseSymbolicQuestions298 (Body)

def check : Body → Option Bool
 | .head _ => some true
 | .install _ sign => reduce (ask sign) (encode base (body sign) xs)
 | .mergeFailure _ => none

def onlyUnknown : Body → Option Bool
 | .head _ => none
 | other => check other

def main : IO Unit := do
  let positive := check (body .pass)
  let negative := check (body .reject)
  let good := symbolic after [candidate] check
  let double := symbolic after [candidate,candidate] check
  let deferred := symbolic after [candidate] onlyUnknown
  let unknownRow := reduce (fun _ => none) (encode base (body .pass) xs)
  unless positive == some true && negative == some true && unknownRow.isNone &&
      (scan after good).length == 1 && (scan after double).length == 2 && (scan after deferred).isEmpty do
    throw (IO.userError "packed query or aligned plan scan diverged")
  IO.println "PASS the refreshed candidate answers both signs over the same two checked packed rows."
  IO.println "PASS unresolved packed rows give unknown, not a negative certificate."
  IO.println "PASS aligned scan retains repeated plan rows and defers a lone unknown head."
  IO.println "The duplicate list is deliberately supplied as a data control; the actual source enumerates one row."
