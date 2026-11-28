import Yulang.GeneralDeclarativeI65I74SingletonInput478
import Yulang.GeneralDeclarativeI65I74OneOriginalPoseExact478

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open GeneralDeclarativeWitnessScopedBindings359 (FrameKey)
open WrittenPattern460 (Address)
open WrittenPattern460.PhysicalOrigin (Pose)
open ObservationAlternatives473 (Positions)
open LiteralVisits473 (Checkpoint StepWire)

/-- Fields to be tied to the genuine upstream input event. The packet
is only address data; callers do not gain authority by constructing it. -/
structure SamePhaseInputCoordinates478 where
  headArgument : Nat
  oldReads : List SourceIndexPair478
  field : Nat
  literal : List Pose

structure SamePhaseInputObservation478 where
  frame : FrameKey
  rootArgument : Nat
  outcome : MixedPoseResult478

def checkSamePhaseInputCoordinates478 {n : Nat} {p : FullProblem} {t : Table}
    (a : Attached (rawAt p) t) (gd : CheckedTable p.old.state.core.current)
    (table : Positions n) (rel : List (Fin n × Fin n)) (outer first : Checkpoint n)
    (schedule : List (Address × Checkpoint n)) (q : SamePhaseInputCoordinates478) :
    Option SamePhaseInputObservation478 := do
  let before ← readSingletonInputBeforeCapture478 a gd q.headArgument q.oldReads
  let out ← readMixedWithOneOriginalPose478 before.2 table rel outer first q.field schedule q.literal
  pure ⟨before.1.frame,before.1.source.headArgument,out⟩

theorem same_phase_coordinates_replay_the_actual_old_source_and_report478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {table : Positions n} {rel : List (Fin n × Fin n)}
    {outer first : Checkpoint n} {route : List (StepWire × Checkpoint n)}
    (result : MixedFieldReport477 fixed table rel outer first route)
    (yes : readMixedFieldReport477 fixed table rel outer first route = some result) :
    checkSamePhaseInputCoordinates478 a gd table rel outer first (mixedActions478 route)
      ⟨w.source.headArgument,w.offered.map StampedRead.indexPair478,fixed.label,result.result.pose⟩ =
      some ⟨w.frame,w.source.headArgument,
        result.result.pose,result.result.compiled,result.result.place,result.result.bit⟩ := by
  have old := exact_accepted_input_needs_neither_frame_nor_visible_ordinal_as_data478 r
  have report := one_pinned_original_pose_replays_exact_same_mixed_reader_result478 result yes
  simp [checkSamePhaseInputCoordinates478,old,report]

theorem compact_same_phase_success_has_the_exact_input_and_its_independent_replay478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {table : Positions n} {rel : List (Fin n × Fin n)}
    {outer first : Checkpoint n} {schedule : List (Address × Checkpoint n)}
    {q : SamePhaseInputCoordinates478} {out : SamePhaseInputObservation478}
    (success : checkSamePhaseInputCoordinates478 a gd table rel outer first schedule q = some out) :
    ∃ (w : BeforeCaptureWire) (r : BeforeCapture a gd w)
      (fixed : FixedFieldChoice476 r) (route : List (StepWire × Checkpoint n))
      (answer : MixedFieldReport477 fixed table rel outer first route),
      w.source.headArgument = q.headArgument ∧ w.offered.map StampedRead.indexPair478 = q.oldReads ∧
      w.frame = out.frame ∧ out.rootArgument = q.headArgument ∧
      fixed.label = q.field ∧ mixedActions478 route = schedule ∧ answer.result.pose = q.literal ∧
      readMixedFieldReport477 fixed table rel outer first route = some answer ∧
      out.outcome = (answer.result.pose,answer.result.compiled,answer.result.place,answer.result.bit) := by
  unfold checkSamePhaseInputCoordinates478 at success
  cases previous : readSingletonInputBeforeCapture478 a gd q.headArgument q.oldReads with
  | none => simp [previous] at success
  | some before =>
    obtain ⟨w,r⟩ := before
    have parsed := (old_before_capture_exists_exactly_from_the_same_indexed_input478
      (a := a) (gd := gd) ⟨⟨0,q.headArgument⟩,q.oldReads⟩).mp (by
        change (readSingletonInputBeforeCapture478 a gd q.headArgument q.oldReads).isSome = true
        simp [previous])
    obtain ⟨matchWire,code,⟨matchRead⟩⟩ := parsed
    have replay := recovering_from_exact_input_indices_keeps_frame_and_actual_capture478 matchRead
    rw [code] at replay
    change readIndexedBeforeCapture478 a gd ⟨⟨0,q.headArgument⟩,q.oldReads⟩ = some ⟨w,r⟩ at previous
    have wireSame := congrArg Sigma.fst (Option.some.inj (replay.symm.trans previous))
    change matchWire = w at wireSame
    subst matchWire
    have arg : w.source.headArgument = q.headArgument :=
      congrArg (fun x => x.head.headArgument) code
    have reads : w.offered.map StampedRead.indexPair478 = q.oldReads :=
      congrArg IndexedBeforeCapture478.rows code
    cases picked : readMixedWithOneOriginalPose478 r table rel outer first q.field schedule q.literal with
    | none =>
      simp [readSingletonInputBeforeCapture478,previous,picked] at success
    | some result =>
      have frameOut : (⟨w.frame,w.source.headArgument,result⟩ : SamePhaseInputObservation478) = out :=
        by simpa [readSingletonInputBeforeCapture478,previous,picked] using success
      subst out
      obtain ⟨fixed,route,answer,field,exactSchedule,original,yes,output⟩ :=
        recovering_one_full_pose_cannot_change_any_requested_action_or_original_site478 picked
      exact ⟨w,r,fixed,route,answer,arg,reads,rfl,arg,field,exactSchedule,original,yes,output⟩

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
