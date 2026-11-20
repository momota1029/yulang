import Yulang.GeneralRebaseRawDepthReplay297
import Yulang.GeneralRebaseRawSafetyBits297
open Yulang
open GeneralDictionaryOutputDepth252 (sourceRegistry initial root plan)
open GeneralRebaseSignedDepth297 (checked pool)
open GeneralRebaseRawDepthReplay297 (checks safety)
open GeneralRebasePriorWitness297 (values)
open GeneralRebaseOutputDepthSuccessor271 (owner output)
open GeneralRebaseSourceWitnessProgram297 (callbacks)
open GeneralRebaseRawObserver297 (observe)
open GeneralRebaseRawSafetyBits297 (run Bits)

def main : IO Unit := do
  let ps := GeneralRebaseSourceQuestions297.entries sourceRegistry initial root checked
  let xs := values pool
  let index := fun i sign => GeneralRebaseSignedIndex297.lookup ps xs checks.old checks.candidate i sign
  let cb := callbacks xs checks
  let before := GeneralRebaseLiveProjection264.project [owner] [output] initial
  let ones := observe sourceRegistry initial root checked xs checks safety [owner] [output] before
  let nexts := ones.map (GeneralRebaseStep258.write before)
  let noSafe := observe sourceRegistry initial root checked xs checks (fun _ => false) [owner] [output] before
  let noNovel := GeneralRebaseSourceObserver267.installAt sourceRegistry initial root root checked
    {cb with novelty := fun _ _ => false}
  let noJoint := GeneralRebaseSourceObserver267.installAt sourceRegistry initial root root checked
    {cb with joint := fun _ _ => false}
  let hazard : Bits := ⟨some false,some true,none,none⟩
  let missing : Bits := ⟨some false,some false,none,some false⟩
  let safe : Bits := ⟨some false,some false,some false,some false⟩
  unless ps.length == 1 &&
      index 0 .pass == some true && index 0 .reject == some true &&
      index 1 .pass == none && (cb.head root plan) == some true &&
      before.remaining.length == 2 && ones.length == 1 && nexts.map (·.remaining.length) == [0] &&
      noSafe.isEmpty && noNovel.isEmpty && noJoint.isEmpty &&
      run hazard == some false && run missing == none && run safe == some true do
    throw (IO.userError "B4 strict nested-output replay diverged")
  IO.println "PASS actual generated root: one candidate, one strict projected proposal; remaining facts 2 -> 0."
  IO.println "PASS prior assignments agree on input coordinates and rows; candidate output returns both pass and reject."
  IO.println "PASS replay lookup distinguishes index 0 pass/reject from absent index 1."
  IO.println "PASS disabling raw safety, omitting the semantic novelty witness or omitting the joint witness yields no install."
  IO.println "PASS independent SafeKnown replies distinguish all clear, unknown, and confirmed unsafe."
