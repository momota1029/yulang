import Yulang.GeneralDeclarativeI65I74SamePhaseInputCoordinates478
import Yulang.GeneralDeclarativeI65I74ReadOriginalActionPath478

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarationPatterns (Pattern)
open WrittenPattern460 (Address)
open WrittenPattern460.PhysicalOrigin (Pose)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint StepWire)

structure RelativeFieldPlan478 (n : Nat) where
  field : Nat
  initial : List Pose
  rest : List (StepWire × Checkpoint n)

def quotePlanByOriginalPose478 (p : Pattern) (literal : List Pose)
    (stops : List (Checkpoint n)) : Option (RelativeFieldPlan478 n) := do
  let original ← parseOriginalActionPath478 p literal
  match original.actions, original.segments with
  | .field field :: actions, first :: tail =>
    if actions.length = stops.length ∧ tail.length = stops.length then
      some ⟨field,first,restoreStepSegments478 tail (actions.zip stops)⟩
    else none
  | _,_ => none

theorem zip_exact_actions_with_original_checkpoints478 (route : List (StepWire × Checkpoint n)) :
    (route.map (fun x => x.1.action)).zip (route.map Prod.snd) = mixedActions478 route := by
  induction route with
  | nil => rfl
  | cons a more ih =>
    rcases a with ⟨wire,check⟩
    exact congrArg ((wire.action,check) :: ·) ih

theorem one_original_pose_and_checkpoints_recreate_the_entire_old_plan478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {table : Positions n} {rel : List (Fin n × Fin n)}
    {outer first : Checkpoint n} {route : List (StepWire × Checkpoint n)}
    (result : MixedFieldReport477 fixed table rel outer first route) :
    quotePlanByOriginalPose478 r.head.orig.original result.result.pose (route.map Prod.snd) =
      some ⟨fixed.label,fixed.path,route⟩ := by
  have lookup := exact_original_report_pose_alone_recovers_its_relative_segments478 result
  obtain ⟨independent,flatten⟩ := recovery_uses_just_the_independently_fixed_original_word478.mp lookup
  have parsed := literal_full_pose_reads_all_old_actions_and_segments478 independent
  have projected := congrArg (Option.map fun x => (x.actions,x.segments))
    parsed
  change (parseOriginalActionPath478 r.head.orig.original
      (fixed.path :: route.map (fun x => x.1.written)).flatten).map (fun x => (x.actions,x.segments)) =
      some (.field fixed.label :: route.map (fun x => x.1.action),fixed.path :: route.map (fun x => x.1.written))
    at projected
  rw [flatten] at projected
  unfold quotePlanByOriginalPose478
  cases h : parseOriginalActionPath478 r.head.orig.original result.result.pose with
  | none => simp [h] at projected
  | some data =>
    have same : (data.actions,data.segments) =
        (.field fixed.label :: route.map (fun x => x.1.action),fixed.path :: route.map (fun x => x.1.written)) := by
      simpa [h] using projected
    obtain ⟨actions,poses⟩ := Prod.mk.inj same
    simp [actions,poses,zip_exact_actions_with_original_checkpoints478,
      restore_relative_coordinates_keeps_exact_supplied_step_wires478]

/-- Only these literal coordinate choices are expected from a source
event in the studied case. Quotient checkpoints and raw/author tables
remain separate inputs. This checker does not issue an event. -/
structure OriginalEventFootprint478 where
  argument : Nat
  reads : List SourceIndexPair478
  originalPose : List Pose

def replayEventFootprint478 {n : Nat} {p : FullProblem} {t : Table}
    (a : Attached (rawAt p) t) (gd : CheckedTable p.old.state.core.current)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer first : Checkpoint n)
    (checkpoints : List (Checkpoint n)) (q : OriginalEventFootprint478) :
    Option SamePhaseInputObservation478 := do
  let before ← readSingletonInputBeforeCapture478 a gd q.argument q.reads
  let plan ← quotePlanByOriginalPose478 before.2.head.orig.original q.originalPose checkpoints
  let fixed ← checkFixedFieldChoice476 before.2 plan.field plan.initial
  let verified ← readMixedFieldReport477 fixed table rel outer first plan.rest
  pure ⟨before.1.frame,before.1.source.headArgument,
    verified.result.pose,verified.result.compiled,verified.result.place,verified.result.bit⟩

theorem exact_old_report_replays_with_only_the_original_event_coordinates478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {table : Positions n} {rel : List (Fin n × Fin n)}
    {outer first : Checkpoint n} {route : List (StepWire × Checkpoint n)}
    (actual : MixedFieldReport477 fixed table rel outer first route)
    (read : readMixedFieldReport477 fixed table rel outer first route = some actual) :
    replayEventFootprint478 a gd table rel outer first (route.map Prod.snd)
      ⟨w.source.headArgument,w.offered.map StampedRead.indexPair478,actual.result.pose⟩ =
    some ⟨w.frame,w.source.headArgument,actual.result.pose,actual.result.compiled,actual.result.place,actual.result.bit⟩ := by
  have phase := exact_accepted_input_needs_neither_frame_nor_visible_ordinal_as_data478 r
  have syntaxPlan := one_original_pose_and_checkpoints_recreate_the_entire_old_plan478 actual
  have exactField := original_fixed_field_replays_in_same_input476 fixed
  simp [replayEventFootprint478,phase,syntaxPlan,exactField,read]

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
