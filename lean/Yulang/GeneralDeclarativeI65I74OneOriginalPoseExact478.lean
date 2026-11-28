import Yulang.GeneralDeclarativeI65I74OneOriginalPose478
import Yulang.GeneralDeclarativeI65I74MixedInputReplay477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open WrittenPattern460 (Address)
open WrittenPattern460.PhysicalOrigin (Pose atSource)
open ObservationAlternatives473 (Positions Place)
open LiteralVisits473 (StepWire Checkpoint)

theorem written_action_has_exactly_one_segment_per_checked_action478
    {source : GeneralDeclarationPatterns.Pattern} {actions : List Address}
    {segments : List (List Pose)} {last : GeneralDeclarationPatterns.Pattern}
    (read : WrittenActionTrail478 source actions segments last) :
    segments.length = actions.length := by
  induction read with
  | stop => rfl
  | step _ _ ih => simp [ih]

theorem restored_action_list_is_exact_when_every_address_recovered478
    {n : Nat} (addresses : List (Address × Checkpoint n)) (pieces : List (List Pose))
    (same : pieces.length = addresses.length) :
    mixedActions478 (restoreStepSegments478 pieces addresses) = addresses ∧
      (restoreStepSegments478 pieces addresses).map (fun x => x.1.written) = pieces := by
  induction addresses generalizing pieces with
  | nil => cases pieces <;> simp_all [mixedActions478,restoreStepSegments478]
  | cons action actions ih =>
    cases pieces with
    | nil => simp at same
    | cons piece rest =>
      obtain ⟨literal,check⟩ := action
      have equal := Nat.succ.inj same
      obtain ⟨old,original⟩ := ih rest equal
      exact ⟨congrArg ((literal,check) :: ·) old,congrArg (piece :: ·) original⟩

theorem recovering_one_full_pose_cannot_change_any_requested_action_or_original_site478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {outer first : Checkpoint n} {startField : Nat} {actions : List (Address × Checkpoint n)}
    {full : List Pose} {answer : MixedPoseResult478}
    (seen : readMixedWithOneOriginalPose478 r table rel outer first startField actions full = some answer) :
    ∃ (fixed : FixedFieldChoice476 r) (wires : List (StepWire × Checkpoint n))
      (verified : MixedFieldReport477 fixed table rel outer first wires),
      fixed.label = startField ∧ mixedActions478 wires = actions ∧ verified.result.pose = full ∧
      readMixedFieldReport477 fixed table rel outer first wires = some verified ∧
      answer = (verified.result.pose,verified.result.compiled,verified.result.place,verified.result.bit) := by
  unfold readMixedWithOneOriginalPose478 at seen
  cases recovered : recoverFixedOriginalSegments478 r.head.orig.original (.field startField :: actions.map Prod.fst) full with
  | none => simp [recovered] at seen
  | some got =>
    obtain ⟨parts,last⟩ := got
    rcases parts with _ | ⟨initial,tail⟩
    · simp [recovered] at seen
    · cases seeded : checkFixedFieldChoice476 r startField initial with
      | none => simp [recovered,seeded] at seen
      | some fixed =>
        let wires := restoreStepSegments478 tail actions
        cases ran : readMixedFieldReport477 fixed table rel outer first wires with
        | none => simp [recovered,seeded] at seen; rw [ran] at seen; cases seen
        | some verified =>
          have fit := recovery_uses_just_the_independently_fixed_original_word478.mp recovered
          have length : tail.length = actions.length := by
            have sizes := written_action_has_exactly_one_segment_per_checked_action478 fit.1
            simpa using Nat.succ.inj sizes
          have scripts := restored_action_list_is_exact_when_every_address_recovered478 actions tail length
          have exactSeed : fixed.label = startField ∧ fixed.path = initial := by
            unfold checkFixedFieldChoice476 at seeded
            obtain ⟨found,_,heq⟩ := Option.map_eq_some_iff.mp seeded
            exact ⟨congrArg FixedFieldChoice476.label heq.symm,congrArg FixedFieldChoice476.path heq.symm⟩
          obtain ⟨sameLabel,fixedInitial⟩ := exactSeed
          have pose := (mixed_field_report_keeps_same_input_and_finishes_at_the_actual_quotient477 verified).1
          have kept : verified.result.pose = full := by
            unfold wires at pose
            rw [fixedInitial] at pose
            have xyz : (restoreStepSegments478 tail actions).flatMap (fun x => x.1.written) = tail.flatten := by
              simpa [List.flatMap] using congrArg List.flatten scripts.2
            rw [xyz] at pose
            exact pose.trans fit.2
          refine ⟨fixed,wires,verified,sameLabel,scripts.1,kept,ran,?_⟩
          simp only [recovered,seeded,bind,Option.bind] at seen
          change ((readMixedFieldReport477 fixed table rel outer first wires).bind (fun result => some _)) = some answer at seen
          rw [ran] at seen
          exact (Option.some.inj seen).symm


end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
