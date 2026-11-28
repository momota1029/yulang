import Yulang.GeneralDeclarativeI65I74ReplayEventFootprintExact478
import Yulang.GeneralDeclarativeI65I74CompactSamePhaseSound478

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

theorem referenced_event_can_be_checked_against_one_original_fitting_state478
    {n : Nat} {p : FullProblem} {t : Table} {a : Attached (rawAt p) t}
    {gd : CheckedTable p.old.state.core.current} {table : Positions n}
    {rel : List (Fin n × Fin n)} {outer first : Checkpoint n} {checkpoints : List (Checkpoint n)}
    {q : OriginalEventFootprint478} {out : SamePhaseInputObservation478}
    (read : replayEventFootprint478 a gd table rel outer first checkpoints q = some out) :
    out.frame.occurrence = p.old.root.occurrence ∧ out.rootArgument = q.argument ∧
    out.outcome.1 = q.originalPose ∧
    (∃ declaration, (registryAt p)[out.frame.sourceOrdinal]? = some declaration ∧
      out.frame.declaration = declaration.id) ∧
    ∃ destination : Fin n,
      oldPosition table destination = out.outcome.2.2.1 ∧
      (out.outcome.2.2.2 = true ↔ ReturnsUpToEquality (graphOf p.old.state.core table) destination) ∧
      SafeEdgeTrail477 (successors (graphOf p.old.state.core table))
        (ReturnsUpToEquality (graphOf p.old.state.core table)) outer.which
        (first.which :: checkpoints.map (·.which)) destination ∧
      ∃ (input : Nat) (code rebuilt : Expr) (uses : List Occurrence),
        (∀ m : Model, FitsFull p.state m →
          GeneralDeclarativeRepeatedActual323.eqAt m.assignment (.variable input) rebuilt) ∧
        Walk .actual rebuilt code uses := by
  obtain ⟨field,schedule,same,checked⟩ := compact_footprint_checks_only_the_exact_full_original_pose478 read
  obtain ⟨root,decl,ordinal,declared,arg,literal⟩ := checked_compact_input_keeps_exact_original_occurrence_and_ordinal478 checked
  obtain ⟨site,atSite,meaning,walk,typed⟩ := compact_same_phase_sound_against_the_same_raw_graph_and_fitting_states478 checked
  have sameCheckpoints : schedule.map (fun x => x.2.which) = checkpoints.map (·.which) := by
    have exact := congrArg (List.map (fun x : Checkpoint n => x.which)) same
    simpa [List.map_map,Function.comp_def] using exact
  rw [sameCheckpoints] at walk
  exact ⟨root,arg,literal,⟨decl,ordinal,declared⟩,site,atSite,meaning,walk,typed⟩

end Yulang.GeneralDeclarativeI65.I72.InputCoordinates475
