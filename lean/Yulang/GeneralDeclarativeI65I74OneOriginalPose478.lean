import Yulang.GeneralDeclarativeI65I74OriginalPoseSegments478
import Yulang.GeneralDeclarativeI65I74MixedInputReplay477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460 (Address)
open WrittenPattern460.PhysicalOrigin (Pose)
open ObservationAlternatives473 (Positions Place)
open LiteralVisits473 (StepWire Checkpoint)

abbrev MixedPoseResult478 := List Pose × List QueryStep476 × Place × Bool

def mixedActions478 (route : List (StepWire × Checkpoint n)) : List (Address × Checkpoint n) :=
  route.map fun (wire,check) => (wire.action,check)

def restoreStepSegments478 (path : List (List Pose)) (actions : List (Address × Checkpoint n)) :
    List (StepWire × Checkpoint n) :=
  (actions.zip path).map fun ((action,check),segment) => (⟨action,segment⟩,check)

theorem restore_relative_coordinates_keeps_exact_supplied_step_wires478
    (route : List (StepWire × Checkpoint n)) :
    restoreStepSegments478 (route.map (fun x => x.1.written)) (mixedActions478 route) = route := by
  induction route with
  | nil => rfl
  | cons lead tail ih =>
    obtain ⟨⟨action,written⟩,check⟩ := lead
    exact congrArg ((⟨action,written⟩,check) :: ·) ih

def readMixedWithOneOriginalPose478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire}
    (r : BeforeCapture a gd w)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer first : Checkpoint n)
    (startField : Nat) (actions : List (Address × Checkpoint n)) (fullPose : List Pose) :
    Option MixedPoseResult478 := do
  let picked ← recoverFixedOriginalSegments478 r.head.orig.original
    (.field startField :: actions.map Prod.fst) fullPose
  match picked.1 with
  | [] => none
  | firstPose :: steps =>
    let chosen ← checkFixedFieldChoice476 r startField firstPose
    let verified ← readMixedFieldReport477 chosen table rel outer first (restoreStepSegments478 steps actions)
    pure (verified.result.pose,verified.result.compiled,verified.result.place,verified.result.bit)

theorem one_pinned_original_pose_replays_exact_same_mixed_reader_result478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {table : Positions n} {rel : List (Fin n × Fin n)}
    {outer first : Checkpoint n} {route : List (StepWire × Checkpoint n)}
    (trial : MixedFieldReport477 fixed table rel outer first route)
    (read : readMixedFieldReport477 fixed table rel outer first route = some trial) :
    readMixedWithOneOriginalPose478 r table rel outer first fixed.label
        (mixedActions478 route) trial.result.pose =
      some (trial.result.pose,trial.result.compiled,trial.result.place,trial.result.bit) := by
  have path := exact_original_report_pose_alone_recovers_its_relative_segments478 trial
  have simple := original_fixed_field_replays_in_same_input476 fixed
  have sameActions : (mixedActions478 route).map Prod.fst = route.map (fun x => x.1.action) := by
    simp [mixedActions478,List.map_map,Function.comp_def]
  simp [readMixedWithOneOriginalPose478,sameActions,path,simple]
  let readProjection := fun (chosen : List (StepWire × Checkpoint n)) =>
    (readMixedFieldReport477 fixed table rel outer first chosen).bind
      (fun result => some (result.result.pose,result.result.compiled,result.result.place,result.result.bit))
  have samePath := congrArg readProjection (restore_relative_coordinates_keeps_exact_supplied_step_wires478 route)
  have final : readProjection route = some (trial.result.pose,trial.result.compiled,trial.result.place,trial.result.bit) := by
    simp [readProjection,read]
  exact samePath.trans final


end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
