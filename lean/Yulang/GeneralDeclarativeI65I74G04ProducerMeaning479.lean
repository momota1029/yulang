import Yulang.GeneralDeclarativeI65I74G04Producer479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open QuotientObservation471 (ReturnsUpToEquality)
open CommonRoleRegularGraph (successors)
open InputCoordinates475 (SafeEdgeTrail477)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open LiteralVisits473 (StepWire)

theorem named_producer_retains_the_independent_same_state_meaning479
    (producer : G04Producer)
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {relations}
    (basis : PriorPhase) (event : TypedInput p gd pos relations)
    (valid : basis.ExactFor event) :
    ∃ (emit : InputPhaseEmission) (wire : InputInspectionWire n),
      emit n p gd pos relations basis event = some wire ∧
      IssueIsFaithful basis event wire ∧
      (event.report.outcome.2.2.2 = true ↔
        ReturnsUpToEquality (graphOf p.old.state.core pos) event.final.index) ∧
      SafeEdgeTrail477 (successors (graphOf p.old.state.core pos))
        (ReturnsUpToEquality (graphOf p.old.state.core pos)) event.root.index
        (wire.route.trail.tail.map (fun x => x.2.which)) event.final.index ∧
      ∃ rebuilt : Expr, (∀ m : Model, FitsFull p.state m →
        GeneralDeclarativeRepeatedActual323.eqAt m.assignment
          (.variable event.head.orig.capture.lower) rebuilt) ∧
        Walk .actual rebuilt event.head.orig.code event.uses := by
  obtain ⟨emit,wire,emitted,validWire⟩ :=
    named_producer_premise_supplies_an_issued_exact_report479 producer basis event valid
  obtain ⟨safePath,bit⟩ := declarative_trail_reads_existing_edges_and_returns_at_the_terminal479 event.visits
  refine ⟨emit,wire,emitted,validWire,bit,?_,independent_input_has_one_walk_in_every_original_full_fit479 event⟩
  rw [validWire.1.2.2.2.2]
  exact .step event.enters.edge event.rootSafe safePath

theorem an_exact_emission_has_the_same_literal_report_on_its_actual_branch479
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {relations} {basis : PriorPhase} {event : TypedInput p gd pos relations}
    {wire : InputInspectionWire n} (issued : IssueIsFaithful basis event wire) :
    match event.backing,wire.payload with
    | .source _,.authored data =>
        readSourceIssueAtRoute p gd pos relations wire.route data = some event.report
    | .released _ phase _ _ _ _ _,.released data =>
        readReleasedIssueAtRoute p gd pos relations phase wire.route data = some event.report
    | _,_ => False := by
  have just := issued.2
  cases hb : event.backing <;> cases hw : wire.payload <;> rw [hb,hw] at just <;>
    first | exact just.2.2.2.2.2 | exact just.2.2.2 | exact just

end Yulang.GeneralDeclarativeI65.I72.Producer479
