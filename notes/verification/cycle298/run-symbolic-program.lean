import Yulang.GeneralRebaseRequestMultiplicity298
import Yulang.GeneralRebasePackedSource298
open Yulang
open Core.PresenceGeneration (CompTerm)
open GeneralDictionaryOutputDepth252 (sourceRegistry root initial)
open GeneralRebasePreInstallReplay297 (after)
open GeneralRebaseSignedDepth297 (checked)
open GeneralRebaseSymbolicQuestions298 (Body program)

def tags : Body → Nat
 | .head _ => 0
 | .install _ .pass => 1
 | .install _ .reject => 2
 | .mergeFailure _ => 3

def main : IO Unit := do
  let p := program sourceRegistry initial root checked CompTerm.var
  let q := program sourceRegistry after root checked CompTerm.var
  let dup := GeneralRebaseRequestMultiplicity298.compiled
  let rq := GeneralRebaseExecutableRequests262.requests GeneralRebaseRequestMultiplicity298.doubled root
  unless p.jobs.map tags == [0,1,2,3] && q.jobs.map tags == [0,1,2,3] &&
      p.jobs[4]?.isNone && q.jobs[4]?.isNone &&
      rq.map (fun x => (x.name,x.target)) == [(0,3),(0,3)] &&
      dup.equations.length == 2 && dup.equalities.length == 8 do
    throw (IO.userError "symbolic program did not preserve jobs or repeated output data")
  IO.println "PASS actual initial and refreshed programs enumerate head, install pass, install reject and merge failure."
  IO.println "PASS missing index 4 stays absent in both programs."
  IO.println "PASS repeated request data control retains [target 3, target 3], two equations and eight pair atoms."
  IO.println "The repeated requests were supplied to a constructed test state; no extra raw source path is claimed."
