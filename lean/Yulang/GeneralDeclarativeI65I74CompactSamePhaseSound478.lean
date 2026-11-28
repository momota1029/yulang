import Yulang.GeneralDeclarativeI65I74SamePhaseInputCoordinates478

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open GeneralDeclarativeWitnessOrigins350 (Table Attached)
open ObservationAlternatives473 (Positions graphOf oldPosition)
open QuotientObservation471 (ReturnsUpToEquality)
open CommonRoleRegularGraph (successors)
open LiteralVisits473 (Checkpoint)
open GeneralDeclarativeTermWalk322 (Walk Occurrence)
open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem checked_compact_input_keeps_exact_original_occurrence_and_ordinal478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {table : Positions n}
    {rel : List (Fin n × Fin n)} {outer first : Checkpoint n} {schedule}
    {q : SamePhaseInputCoordinates478} {out : SamePhaseInputObservation478}
    (success : checkSamePhaseInputCoordinates478 a gd table rel outer first schedule q = some out) :
    out.frame.occurrence = p.old.root.occurrence ∧
    ∃ declaration, (registryAt p)[out.frame.sourceOrdinal]? = some declaration ∧
      out.frame.declaration = declaration.id ∧ out.rootArgument = q.headArgument ∧ out.outcome.1 = q.literal := by
  obtain ⟨w,r,_,_,_,_,_,same,arg,_,_,literal,_,reported⟩ :=
    compact_same_phase_success_has_the_exact_input_and_its_independent_replay478 success
  obtain ⟨request,impl,registry,_,_,_⟩ := literal_frame_and_input_rows_before_any_capture r
  refine ⟨same ▸ request,r.head.orig.declaration,same ▸ registry,same ▸ impl,arg,?_⟩
  simp [reported,literal]

theorem compact_same_phase_sound_against_the_same_raw_graph_and_fitting_states478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {table : Positions n}
    {rel : List (Fin n × Fin n)} {outer first : Checkpoint n} {schedule}
    {q : SamePhaseInputCoordinates478} {out : SamePhaseInputObservation478}
    (read : checkSamePhaseInputCoordinates478 a gd table rel outer first schedule q = some out) :
    ∃ through : Fin n,
      oldPosition table through = out.outcome.2.2.1 ∧
      (out.outcome.2.2.2 = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) through) ∧
      SafeEdgeTrail477 (successors (graphOf p.old.state.core table))
        (ReturnsUpToEquality (graphOf p.old.state.core table)) outer.which
        (first.which :: schedule.map fun x => x.2.which) through ∧
      ∃ (input : Nat) (code rebuilt : Expr) (uses : List Occurrence),
        (∀ m : Model, FitsFull p.state m →
          GeneralDeclarativeRepeatedActual323.eqAt m.assignment (.variable input) rebuilt) ∧
        Walk .actual rebuilt code uses := by
  obtain ⟨w,r,fixed,route,answer,_,_,_,_,_,same,_,_,value⟩ :=
    compact_same_phase_success_has_the_exact_input_and_its_independent_replay478 read
  obtain ⟨_,_,atEnd,meaning,typing⟩ :=
    mixed_field_report_keeps_same_input_and_finishes_at_the_actual_quotient477 answer
  have tail := mixed_field_report_preserves_full_safe_path_after_its_original_root477 answer
  have sameCheckpoints : schedule.map (fun x => x.2.which) = route.map (fun x => x.2.which) := by
    rw [←same]
    simp [mixedActions478,List.map_map,Function.comp_def]
  obtain ⟨rebuilt,model,through⟩ := typing
  rw [value]
  exact ⟨answer.result.checkpoint.which,atEnd,meaning,sameCheckpoints.symm ▸ tail,
    r.head.orig.capture.lower,r.head.orig.code,rebuilt,answer.captured.uses,model,through⟩

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
