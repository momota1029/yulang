import Yulang.GeneralDeclarativeI65I74FlatSound481
import Yulang.GeneralDeclarativeI65I74G04ProducerMeaning479
import Yulang.GeneralDeclarativeI65I74TypedRootSafety482

namespace Yulang.GeneralDeclarativeI65.I72.Producer479
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable)
open ObservationAlternatives473 (Positions graphOf)
open LiteralVisits473 (GuardedObservationInput)
open TypedRootSafety482 (AllRootSafe)
open InputCoordinates475 (SamePhaseInputObservation478 SafeEdgeTrail477)
open QuotientObservation471 (ReturnsUpToEquality)
open CommonRoleRegularGraph (successors)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralDeclarativeRepeatedActual323 (eqAt)

/-- Remaining single-visible-candidate signed entry obligation. The right tag
retains a choice of input authority; it is not inferred from the report. The
old flat inputs and their meaning stay unchanged. The signed test consumes
finite data on the original problem, not a proof of the event being tested.
Safety covers the actual request roots before this local diagnostic. The
attached prior belongs to the caller; the checker cannot choose a new one. -/
def G04Entry : Prop :=
  ∀ (p : FullProblem) (gd : CheckedTable p.old.state.core.current),
  ∃ check : (n : Nat) → Positions n → List (Fin n × Fin n) → PriorPhase →
      Sum Flat481.FlatReport SamePhaseInputObservation478 →
      Sum Flat481.FlatWitness (InputInspectionWire n × List (Fin n)) → Bool,
    let safe := fun (n : Nat) (pos : Positions n) (rel : List (Fin n × Fin n))
        (roots : List (Fin n)) =>
      AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (fun a => a.lower)) roots ∧
      ∀ site ∈ roots, GuardedObservationInput p.old.state.core pos rel site
    (∀ n pos rel basis r w, check n pos rel basis (.inl r) (.inl w) =
      Flat481.check_full_flat p r w) ∧
    (∀ n pos rel basis old signed oldWire signedWire,
      check n pos rel basis (.inl old) (.inr signedWire) = false ∧
      check n pos rel basis (.inr signed) (.inl oldWire) = false) ∧
    (∀ n pos rel basis report wire,
      check n pos rel basis (.inr report) (.inr wire) = true ↔
        ∃ event : TypedInput p gd pos rel, basis.ExactFor event ∧
          IssueIsFaithful basis event wire.1 ∧
          safe n pos rel wire.2 ∧ report = event.report) ∧
    (∀ n pos rel basis (event : TypedInput p gd pos rel), basis.ExactFor event →
      (∃ roots, safe n pos rel roots) →
      ∃ wire : InputInspectionWire n × List (Fin n), IssueIsFaithful basis event wire.1 ∧
        safe n pos rel wire.2 ∧
        check n pos rel basis (.inr event.report) (.inr wire) = true) ∧
    ∀ n pos rel basis report wire, check n pos rel basis (.inr report) (.inr wire) = true →
      ∃ event : TypedInput p gd pos rel, basis.ExactFor event ∧
        IssueIsFaithful basis event wire.1 ∧ report = event.report ∧
        safe n pos rel wire.2 ∧
        (report.outcome.2.2.2 = true ↔
          ReturnsUpToEquality (graphOf p.old.state.core pos) event.final.index) ∧
        SafeEdgeTrail477 (successors (graphOf p.old.state.core pos))
          (ReturnsUpToEquality (graphOf p.old.state.core pos)) event.root.index
          (wire.1.route.trail.tail.map (fun x => x.2.which)) event.final.index ∧
        ∃ rebuilt : Expr,
          (∀ m : Model, FitsFull p.state m →
            eqAt m.assignment (.variable event.head.orig.capture.lower) rebuilt) ∧
          Walk .actual rebuilt event.head.orig.code event.uses

end Yulang.GeneralDeclarativeI65.I72.Producer479
