import Yulang.GeneralRebaseSignedIndex297
import Yulang.GeneralRebaseDepthCompiler297
open Yulang
open GeneralDictionaryOutputDepth252 (initial plan)
open GeneralDictionaryOutputDepthInstall252 (smallModel)
open GeneralRebaseSignedDepth297 (pool)
open GeneralRebasePriorWitness297 (values)
open GeneralRebaseSignedIndex297 (lookup)

def main : IO Unit := do
  let yes := fun _ m => GeneralRebaseSignedDepth297.nested m
  let ps := [plan,plan]
  let samples := values pool
  let ask := lookup ps samples (fun _ => true) yes
  let noPrior := lookup ps samples (fun _ => false) yes
  let onlyAccept := lookup ps [GeneralDictionaryOutputDepth252.model] (fun _ => true) yes
  let onlyReject := lookup ps [smallModel] (fun _ => true) yes
  unless (ask 0 .pass,ask 0 .reject) == (some true,some true) &&
      (ask 1 .pass,ask 1 .reject) == (some true,some true) &&
      ask 2 .pass == none && ask 2 .reject == none &&
      (noPrior 0 .pass,noPrior 0 .reject) == (some false,some false) &&
      (onlyAccept 0 .pass,onlyAccept 0 .reject) == (some true,some false) &&
      (onlyReject 0 .pass,onlyReject 0 .reject) == (some false,some true) do
    throw (IO.userError "signed model polarity controls diverged")
  IO.println "PASS duplicate entries preserve the same answer at distinct list positions; an out-of-range position remains absent."
  IO.println "PASS both signs, neither sign, pass-only, and reject-only are distinct signed table replies."
  IO.println "Fixture rows are actual source models; filtered-away or intentionally incomplete rows do not certify semantic absence."
