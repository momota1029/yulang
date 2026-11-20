import Yulang.GeneralRebaseSourceMetadata297
open Yulang
open GeneralDictionaryOutputDepth252 (sourceRegistry initial root)
open GeneralRebaseSignedDepth297 (checked)
open GeneralRebasePreInstallReplay297 (after xs entries)
open GeneralRebaseSourceQuestions297 renaming entries → beforeEntries
open GeneralRebaseSignedIndex297 (lookup)
open GeneralRebaseCandidateChecks267 (known)

def main : IO Unit := do
  let test := fun _ a => GeneralRebaseSignedDepth297.nested a
  let before := beforeEntries sourceRegistry initial root checked
  let beforeReply := lookup before xs (fun _ => true) test 0
  let afterReply := lookup entries xs (fun _ => true) test 0
  let sourceKinds := fun s n => known (GeneralRebaseSourceMetadata297.current s).state n
  unless before.length == 1 && entries.length == 1 &&
      !sourceKinds initial 0 && sourceKinds after 0 && !sourceKinds initial 1 && sourceKinds after 1 &&
      beforeReply .pass == some true && beforeReply .reject == some true &&
      afterReply .pass == beforeReply .pass && afterReply .reject == beforeReply .reject do
    throw (IO.userError "pre-install transport diverged")
  IO.println "PASS actual pre-install refresh recognizes source coordinates 0 and 1."
  IO.println "PASS the freshly enumerated candidate retains both signed answers using the same two verified assignments."
  IO.println "The raw administrative state changed; no general phase or termination conclusion is drawn."
