import Yulang.GeneralDeclarativeI65I74ReplayEventFootprint478

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

private theorem zipper_preserves_the_chosen_actions_and_checks478
    {acts : List Address} {points : List (Checkpoint n)}
    (same : acts.length = points.length) :
    (acts.zip points).map Prod.fst = acts ∧ (acts.zip points).map Prod.snd = points := by
  induction acts generalizing points with
  | nil => cases points <;> simp_all
  | cons hd tl ih =>
    cases points with
    | nil => simp at same
    | cons atPoint past =>
      obtain ⟨l,r⟩ := ih (Nat.succ.inj same)
      exact ⟨congrArg (hd :: ·) l,congrArg (atPoint :: ·) r⟩

theorem accepted_pose_plan_has_exact_action_trail_and_exact_checkpoint_count478
    {n : Nat} {source : Pattern} {literal : List Pose}
    {stops : List (Checkpoint n)} {plan : RelativeFieldPlan478 n}
    (accept : quotePlanByOriginalPose478 source literal stops = some plan) :
    ∃ last : Pattern,
      WrittenActionTrail478 source (.field plan.field :: plan.rest.map (fun x => x.1.action))
        (plan.initial :: plan.rest.map (fun x => x.1.written)) last ∧
      (plan.initial :: plan.rest.map (fun x => x.1.written)).flatten = literal ∧
      plan.rest.map Prod.snd = stops := by
  unfold quotePlanByOriginalPose478 at accept
  cases scan : parseOriginalActionPath478 source literal with
  | none => simp [scan] at accept
  | some parsed =>
    simp only [scan,bind,Option.bind] at accept
    split at accept
    · rename_i first actions start tail actionEq segmentEq
      split at accept
      · rename_i lengths
        have same := Option.some.inj accept
        subst plan
        have zip := zipper_preserves_the_chosen_actions_and_checks478 lengths.1
        have length : tail.length = (actions.zip stops).length := by
          have via := congrArg List.length zip.2
          rw [List.length_map] at via
          omega
        obtain ⟨paired,parts⟩ :=
          restored_action_list_is_exact_when_every_address_recovered478 (actions.zip stops) tail length
        have actEq := congrArg (List.map Prod.fst) paired
        have pointsEq := congrArg (List.map Prod.snd) paired
        have firstTrail := parsed.trail
        rw [actionEq,segmentEq] at firstTrail
        refine ⟨parsed.last,?_,?_,?_⟩
        · have originalActions : (restoreStepSegments478 tail (actions.zip stops)).map (fun x => x.1.action) = actions := by
            simpa [mixedActions478,List.map_map,Function.comp_def,zip.1] using actEq
          simpa [originalActions,parts] using firstTrail
        · have exact := parsed.exact
          rw [segmentEq] at exact
          simpa [parts] using exact
        · simpa [mixedActions478,List.map_map,Function.comp_def,zip.2] using pointsEq
      · cases accept
    · cases accept

theorem compact_footprint_checks_only_the_exact_full_original_pose478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {table : Positions n}
    {rel : List (Fin n × Fin n)} {outer first : Checkpoint n}
    {checkpoints : List (Checkpoint n)} {q : OriginalEventFootprint478}
    {out : SamePhaseInputObservation478}
    (run : replayEventFootprint478 a gd table rel outer first checkpoints q = some out) :
    ∃ (field : Nat) (schedule : List (Address × Checkpoint n)),
      schedule.map Prod.snd = checkpoints ∧
      checkSamePhaseInputCoordinates478 a gd table rel outer first schedule
        ⟨q.argument,q.reads,field,q.originalPose⟩ = some out := by
  unfold replayEventFootprint478 at run
  cases before : readSingletonInputBeforeCapture478 a gd q.argument q.reads with
  | none => simp [before] at run
  | some entry =>
    simp only [before,bind,Option.bind] at run
    cases plan : quotePlanByOriginalPose478 entry.2.head.orig.original q.originalPose checkpoints with
    | none => simp [plan] at run
    | some found =>
      simp only [plan] at run
      cases seed : checkFixedFieldChoice476 entry.2 found.field found.initial with
      | none => simp [seed] at run
      | some fixed =>
        simp only [seed] at run
        cases actual : readMixedFieldReport477 fixed table rel outer first found.rest with
        | none => simp [actual] at run
        | some report =>
          have info : (⟨entry.1.frame,entry.1.source.headArgument,
              report.result.pose,report.result.compiled,report.result.place,report.result.bit⟩ :
                SamePhaseInputObservation478) = out := by simpa [actual,pure] using run
          obtain ⟨_,_,physical,checks⟩ :=
            accepted_pose_plan_has_exact_action_trail_and_exact_checkpoint_count478 plan
          have key : fixed.label = found.field ∧ fixed.path = found.initial := by
            unfold checkFixedFieldChoice476 at seed
            obtain ⟨stamped,_,same⟩ := Option.map_eq_some_iff.mp seed
            exact ⟨congrArg FixedFieldChoice476.label same.symm,congrArg FixedFieldChoice476.path same.symm⟩
          have reportPose : report.result.pose = q.originalPose := by
            have loc := (mixed_field_report_keeps_same_input_and_finishes_at_the_actual_quotient477 report).1
            rw [key.2] at loc
            simpa [List.flatMap,List.flatten_cons] using loc.trans physical
          have existing := one_pinned_original_pose_replays_exact_same_mixed_reader_result478 report actual
          rw [key.1,reportPose] at existing
          rw [reportPose] at info
          refine ⟨found.field,mixedActions478 found.rest,?_,?_⟩
          · simpa [mixedActions478,List.map_map,Function.comp_def] using checks
          · simp [checkSamePhaseInputCoordinates478,before,existing,info]

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
