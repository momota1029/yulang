import Yulang.GeneralDeclarativeI65I74MixedInputReplay477

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open GeneralDeclarationPatterns (Pattern)
open WrittenPattern460 (Address)
open WrittenPattern460.PhysicalOrigin (Pose atSource exact_original_occurrences literal_occurrence)
open LiteralVisits473 (written_pose_append_is_exact StepWire Checkpoint)
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationAlternatives473 (Positions)

/-- Enumerate original lexical paths on the already chosen actions.
Only source syntax is read; this is neither a new visitation rule nor
a selection among multiple valid written occurrences. -/
def originalActionChoices478 (source : Pattern) :
    List Address → List (List (List Pose) × Pattern)
  | [] => [([],source)]
  | action :: rest =>
    (WrittenPattern460.PhysicalOrigin.children source action).flatMap fun (segment,sub) =>
      (originalActionChoices478 sub rest).map fun (pieces,last) =>
        (segment :: pieces,last)

inductive WrittenActionTrail478 : Pattern → List Address → List (List Pose) → Pattern → Prop where
  | stop : WrittenActionTrail478 p [] [] p
  | step : WrittenPattern460.PhysicalOrigin.Origin p a pose child → WrittenActionTrail478 child rest pieces terminal →
      WrittenActionTrail478 p (a :: rest) (pose :: pieces) terminal

theorem structurally_enumerated_original_origins_are_exact478
    (p : Pattern) (actions : List Address) (parts : List (List Pose)) (last : Pattern) :
    (parts,last) ∈ originalActionChoices478 p actions ↔ WrittenActionTrail478 p actions parts last := by
  induction actions generalizing p parts last with
  | nil =>
    constructor
    · intro yes
      have both : (parts,last) = ([],p) := by simpa [originalActionChoices478] using yes
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj both
      exact .stop
    · intro yes
      cases yes
      simp [originalActionChoices478]
  | cons a rest ih =>
    constructor
    · intro yes
      obtain ⟨⟨one,child⟩,head,tail⟩ := List.mem_flatMap.mp yes
      obtain ⟨⟨someParts,lastNode⟩,part,equal⟩ := List.mem_map.mp tail
      have same : (one :: someParts,lastNode) = (parts,last) := equal
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj same
      exact .step ((exact_original_occurrences ..).mp head) ((ih ..).mp part)
    · intro yes
      cases yes with
      | step origin tail =>
        exact List.mem_flatMap.mpr
          ⟨_,(exact_original_occurrences ..).mpr origin,List.mem_map.mpr ⟨_,(ih ..).mpr tail,rfl⟩⟩

theorem enumerated_route_has_literal_composed_end_in_the_original_syntax478
    {p : Pattern} {actions : List Address} {parts : List (List Pose)} {last : Pattern}
    (proof : WrittenActionTrail478 p actions parts last) :
    atSource p parts.flatten = some last := by
  induction proof with
  | stop => rfl
  | step origin tail ih =>
    simp only [List.flatten_cons,written_pose_append_is_exact,literal_occurrence origin]
    exact ih

theorem each_checked_mixed_route_is_one_of_the_finite_original_lexical_paths478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {table : Positions n} {rel : List (Fin n × Fin n)}
    {trace : LocatedCapture476 w.offered} {source finish : MixedPoint477 r table rel}
    {route : List (StepWire × Checkpoint n)}
    (legal : MixedTrail477 trace source route finish) :
    ((route.map (fun x => x.1.written)),finish.source) ∈
      originalActionChoices478 source.source (route.map (fun x => x.1.action)) := by
  apply (structurally_enumerated_original_origins_are_exact478 ..).mpr
  induction legal with
  | stop => exact .stop
  | step hop tail ih => exact .step hop.accepted.writtenFrom ih



open WrittenPattern460.PhysicalOrigin (Origin)

theorem same_written_action_has_no_different_prefix_of_one_literal_word478
    {source : Pattern} {action : Address} {a b : List Pose} {subA subB : Pattern}
    (left : WrittenPattern460.PhysicalOrigin.Origin source action a subA)
    (right : WrittenPattern460.PhysicalOrigin.Origin source action b subB)
    {tailA tailB : List Pose} (same : a ++ tailA = b ++ tailB) : a = b := by
  induction left generalizing b subB tailA tailB with
  | app _ => cases right; rfl
  | field =>
    cases right with
    | field => rfl
    | tail notSame _ => exact (notSame rfl).elim
  | tail notSame reach ih =>
    cases right with
    | field => exact (notSame rfl).elim
    | tail _ comes =>
      have eq := (List.cons.inj same).2
      exact congrArg (Pose.tail :: ·) (ih comes eq)
  | tag => cases right; rfl
  | left _ reach ih =>
    cases right with
    | left _ comes =>
      have eq := (List.cons.inj same).2
      exact congrArg (Pose.left :: ·) (ih comes eq)
    | right _ _ => cases same
  | right _ reach ih =>
    cases right with
    | left _ _ => cases same
    | right _ comes =>
      have eq := (List.cons.inj same).2
      exact congrArg (Pose.right :: ·) (ih comes eq)

theorem fixed_full_original_word_determines_every_relative_segment478
    {source : Pattern} {acts : List Address} {left right : List (List Pose)} {u v : Pattern}
    (r₁ : WrittenActionTrail478 source acts left u) (r₂ : WrittenActionTrail478 source acts right v)
    (same : left.flatten = right.flatten) :
    left = right ∧ u = v := by
  induction r₁ generalizing right v with
  | stop => cases r₂; exact ⟨rfl,rfl⟩
  | step origin tail ih =>
    cases r₂ with
    | step other rest =>
      simp only [List.flatten_cons] at same
      have seg := same_written_action_has_no_different_prefix_of_one_literal_word478 origin other same
      cases seg
      have sub := Option.some.inj ((literal_occurrence origin).symm.trans (literal_occurrence other))
      cases sub
      have afterwards := List.append_cancel_left same
      obtain ⟨rfl,rfl⟩ := ih rest afterwards
      exact ⟨rfl,rfl⟩



def recoverFixedOriginalSegments478 (source : Pattern) (actions : List Address) (literal : List Pose) :
    Option (List (List Pose) × Pattern) :=
  (originalActionChoices478 source actions).find? fun entry => decide (entry.1.flatten = literal)

theorem recovery_uses_just_the_independently_fixed_original_word478
    {source : Pattern} {actions : List Address} {literal : List Pose}
    {segments : List (List Pose)} {last : Pattern} :
    recoverFixedOriginalSegments478 source actions literal = some (segments,last) ↔
      WrittenActionTrail478 source actions segments last ∧ segments.flatten = literal := by
  constructor
  · intro yes
    have found := List.mem_of_find?_eq_some yes
    have valid := List.find?_some yes
    exact ⟨(structurally_enumerated_original_origins_are_exact478 ..).mp found,of_decide_eq_true valid⟩
  · rintro ⟨candidate,pose⟩
    have inList := (structurally_enumerated_original_origins_are_exact478 ..).mpr candidate
    cases get : recoverFixedOriginalSegments478 source actions literal with
    | none =>
      have no := List.find?_eq_none.mp get
      exact False.elim (no _ inList (decide_eq_true pose))
    | some entry =>
      obtain ⟨a,b⟩ := entry
      have accepted := (structurally_enumerated_original_origins_are_exact478 ..).mp
        (List.mem_of_find?_eq_some get)
      have decided := List.find?_some
        (p := fun e : List (List Pose) × Pattern => decide (e.1.flatten = literal)) get
      have exactPose : a.flatten = literal := of_decide_eq_true decided
      obtain ⟨rfl,rfl⟩ := fixed_full_original_word_determines_every_relative_segment478
        accepted candidate (exactPose.trans pose.symm)
      rfl



theorem exact_original_report_pose_alone_recovers_its_relative_segments478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {w : BeforeCaptureWire} {r : BeforeCapture a gd w}
    {fixed : FixedFieldChoice476 r} {table : Positions n} {rel : List (Fin n × Fin n)}
    {outer first : Checkpoint n} {route : List (StepWire × Checkpoint n)}
    (field : MixedFieldReport477 fixed table rel outer first route) :
    recoverFixedOriginalSegments478 r.head.orig.original
      (.field fixed.label :: route.map (fun x => x.1.action)) field.result.pose =
      some (fixed.path :: route.map (fun x => x.1.written),field.result.source) := by
  apply recovery_uses_just_the_independently_fixed_original_word478.mpr
  have firstSource := fixed.original.selectedWritten
  have same := (forwarded_old_read_uses_the_very_same_prechecked_head_and_row
    r fixed.label fixed.path fixed.original).1
  change WrittenPattern460.PhysicalOrigin.Origin fixed.original.head.orig.original
    (.field fixed.label) fixed.path fixed.original.sourcePattern at firstSource
  rw [same] at firstSource
  have actualStart := field.seed.start.written
  rw [field.seed.original] at actualStart
  have exactStart : field.seed.start.source = fixed.original.sourcePattern :=
    Option.some.inj (actualStart.symm.trans (literal_occurrence firstSource))
  have rest := (structurally_enumerated_original_origins_are_exact478 ..).mp
    (each_checked_mixed_route_is_one_of_the_finite_original_lexical_paths478 field.visits)
  refine ⟨.step firstSource (exactStart ▸ rest),?_⟩
  have endPose := (mixed_field_report_keeps_same_input_and_finishes_at_the_actual_quotient477 field).1
  simpa [List.flatten_cons,List.flatMap] using endPose.symm


end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
