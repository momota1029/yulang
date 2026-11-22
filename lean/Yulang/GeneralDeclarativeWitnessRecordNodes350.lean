import Yulang.GeneralDeclarativeWitnessRecordHeader350
import Yulang.GeneralDeclarativeWitnessWhole350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessRecordNodes350
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessRecordHeader350 (replay replay_first replay_sound)
open GeneralDeclarativeWitnessForest350 (ProblemTree Global Node anchor)
open GeneralDeclarativeWitnessOneRecord350 (Anchor pointPortal compilerCtx selected replayElection)
open GeneralDeclarativeWitnessAllocation350 (entries)
open GeneralDeclarativeWitnessManifest349 (attach)
open GeneralDeclarativeWitnessProjection349 (decode)
open GeneralDeclarativeWitnessRecordHead350 (know)
open GeneralDeclarativeWitnessRecordReplay350 (Wire)
open GeneralDeclarativeWitnessPointInput349 (pick)
open GeneralSourceMetadataBareBundle291 (compile reassemble)
open GeneralSourceMetadataBundle291 (SourceBundle)
open GeneralDeclarativeWitnessProblem349 (Problem first_sound)

theorem same_table {p : Problem} {w} {s t : SourceBundle}
    (ok : replay p w = some s) (expected : compile p.source = some t) : s = t := by
  have base := (replay_first ok).1
  obtain ⟨source,valid,_⟩ := first_sound base
  have ready := reassemble s valid
  rw [source,expected] at ready
  exact (Option.some.inj ready).symm

def decodeNode {p : ProblemTree} (env : Global p) (path : List Nat) (d : Demand) (wire : Wire) :
    Option (Node env d) := do
  let plan := anchor p path d
  match header : replay plan.problem ⟨d.outputs⟩ with
  | none => none
  | some table =>
    let same : table = env.table := same_table header env.tableOrigin
    match chosen : pick (pointPortal plan.problem) table with
    | none => none
    | some decl =>
      match ha : d.arguments, hp : decl.head with
      | [arg],[pat] =>
        let original ← attach plan.before p.manifest
        let projection ← decode original arg pat wire.sourceProjection
        let current ← decode env.live arg pat wire.currentProjection
        let ready ← know env.live arg.lower wire.readinessRow wire.readinessLink
        if nn : current.shape ≠ [] then
          if rankOK : GeneralDeclarativeWitnessRank350.check p.current wire.ranks = true then
            if a : GeneralDeclarativeWitnessAllocation350.check projection plan.keep p.current
                wire.slots wire.projections = true then do
              let compiler ← GeneralDeclarativeWitnessCompiler350.decode
                (compilerCtx projection table decl) p.current wire.emitted
              let fit := GeneralDeclarativeWitnessAllocation350.sound a
              let election := replayElection env.live ha hp chosen current nn ready rankOK
              let step := selected ha hp projection fit.1 election compiler
              pure ⟨decl,compiler.compiled.kids,entries projection plan.keep,
                same ▸ step,wire.emitted.outputRows,
                (fun _ => ⟨by rw [compiler.fixed]; exact GeneralDeclarativeWitnessCompiler350.fixed_targets compiler.run,
                  fun m fit => (GeneralDeclarativeWitnessCompiler350.fixed_in_current compiler m fit).2⟩),
                fit.2.2⟩
            else none
          else none
        else none
      | _,_ => none

end Yulang.GeneralDeclarativeWitnessRecordNodes350
