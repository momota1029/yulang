import Yulang.GeneralRebaseMergeWitnessFixture297
open Yulang
open GeneralRebaseMergeWitnessFixture297
open GeneralRebaseMergeQuestions297 (equal shape)

def main : IO Unit := do
  let positive := EqualCenter.pair
  let negative := DifferentCenter.pair
  let actual := GeneralRebaseMergeScan267.scan GeneralRebaseMergeRegression264.sample
    GeneralNominalCenteredHeadAllocMergeSource.root (fun a b => equal [] ActualStep.tested (a,b))
  let a := GeneralNominalCenteredHeadAllocMergeInstall.aSite.occurrence.identity
  let b := GeneralNominalCenteredHeadAllocMergeInstall.bSite.occurrence.identity
  unless shape positive && !(GeneralRebaseMergeCenters267.same positive.1 positive.2) &&
      equal [] EqualCenter.test positive && shape negative &&
      !(equal [GeneralDictionaryOutputDepth252.model] DifferentCenter.test negative) &&
      equal [] DifferentCenter.test negative &&
      actual.any (fun pair => pair.1.occurrence.identity == a && pair.2.occurrence.identity == b) do
    throw (IO.userError "merge witness controls diverged")
  IO.println "PASS distinct literal centers with equal modeled input; checked no-counterexample comparison returns true."
  IO.println "PASS distinct modeled inputs in the same structural shape; actual prior assignment returns a merge counterexample."
  IO.println "PASS removing the necessary comparison witness produces a false positive in the raw Boolean reduction; coverage is essential."
  IO.println "PASS the registered pair in the existing mixed-kernel merge stress fixture is listed."
  IO.println "These first two pairs are comparison fixtures, not assertions of fully reachable merge steps."
