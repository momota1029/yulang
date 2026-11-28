import Yulang.GeneralDeclarativeI65I74TypedRootPinnedCard482
import Yulang.GeneralDeclarativeI65I74TypedFocusTrail482
import Yulang.GeneralDeclarativeI65I74TypedRootSafety482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable PrecheckedHead readPrecheckedHead)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open Producer479 (PriorPhase RouteWire Site siteAt readRoute Trail)
open LiteralVisits473 (Checkpoint)
open InputCoordinates475 (rawAt SamePhaseInputObservation478 SourceIndexPair478)
open TypedRootSafety482 (requestRootCheck AllRootSafe requestRootCheckSound)
open QuotientObservation471 (ReturnsUpToEquality)
open GeneralDeclarativeOrigins321 (Supported)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCenteredHeadMatExpressions (Expr)

structure WholeAuthoredWire (n : Nat) where
  route : RouteWire n
  source : ReadCard
  initialAuthor : Nat
  roots : List (Checkpoint n)

structure WholeAuthoredReceipt {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (positions : Positions n)
    (rel : List (Fin n × Fin n)) (basis : PriorPhase) (wire : WholeAuthoredWire n) where
  initial : AuthoredCardRouteReceipt
  rootChecked : requestRootCheck p positions rel wire.roots = true
  bound : runRootPinnedAuthoredCard p gd positions rel basis wire.route wire.source wire.initialAuthor = some initial
  original : PrecheckedHead (p := p.old) gd
  atHead : readPrecheckedHead gd ⟨0,wire.route.argument⟩ = some original
  here : Site p.old.state.core positions
  startExact : siteAt (s := p.old.state.core) (pos := positions) wire.route.trail.cursor.which
    original.orig.original original.orig.code = some here
  reportTrace : PinnedSignedFocus (p := p) basis.authors here wire.source rel wire.route.trail
  samePlace : initial.output.outcome.2.2.1 = oldPosition positions reportTrace.focus.finish.index
  sameBit : initial.output.outcome.2.2.2 = reportTrace.bit

private def asProof {α : Type} (x : Option α) : Option {a // x = some a} :=
  match x with | some a => some ⟨a,rfl⟩ | none => none

def readWholeAuthoredFocus {n : Nat} (p : FullProblem) (gd : CheckedTable p.old.state.core.current)
    (positions : Positions n) (rel : List (Fin n × Fin n)) (basis : PriorPhase)
    (wire : WholeAuthoredWire n) : Option (WholeAuthoredReceipt p gd positions rel basis wire) := do
  if roots : requestRootCheck p positions rel wire.roots = true then
    let initial ← asProof (runRootPinnedAuthoredCard p gd positions rel basis
      wire.route wire.source wire.initialAuthor)
    let head ← asProof (readPrecheckedHead (p := p.old) gd ⟨0,wire.route.argument⟩)
    let here ← asProof (siteAt (s := p.old.state.core) (pos := positions)
      wire.route.trail.cursor.which head.val.orig.original head.val.orig.code)
    let routed ← readPinnedSignedFocus (p := p) basis.authors here.val wire.source rel wire.route.trail
    if terminal : initial.val.output.outcome.2.2.1 = oldPosition positions routed.focus.finish.index ∧
        initial.val.output.outcome.2.2.2 = routed.bit then
      pure ⟨initial.val,roots,initial.property,head.val,head.property,here.val,here.property,
        routed,terminal.1,terminal.2⟩
    else none
  else none

theorem whole_authored_report_checks_actual_roots_selected_trail_and_same_fit
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel : List (Fin n × Fin n)} {basis : PriorPhase}
    {wire : WholeAuthoredWire n} {done : Nat → Prop} {support : Supported (rawAt p) done}
    (authority : ∀ row ∈ basis.authors.authored, support.derivesFrom row .source)
    (out : WholeAuthoredReceipt p gd pos rel basis wire) :
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (fun a => a.lower))
      (wire.roots.map Checkpoint.which) ∧
    readRoute p gd pos rel wire.route = some out.initial.output ∧
    Trail p.old.state.core pos rel out.here (wire.route.trail.tail.map Prod.fst)
      (wire.route.trail.tail.map (fun x => x.2.which)) out.reportTrace.focus.finish out.reportTrace.bit ∧
    FocusedChain (p := p) basis.authors out.here wire.source wire.route.trail.tail
      out.reportTrace.focus.finish out.reportTrace.focus.selected out.reportTrace.focus.reads ∧
    (out.initial.output.outcome.2.2.2 = true ↔
      ReturnsUpToEquality (graphOf p.old.state.core pos) out.reportTrace.focus.finish.index) ∧
    ∃ rebuilt : Expr,
      (∀ m : Model, FitsFull p.state m →
        eqAt m.assignment (.variable out.original.orig.capture.lower) rebuilt) ∧
      Walk .actual rebuilt out.original.orig.code out.initial.used := by
  have roots := requestRootCheckSound _ _ _ _ out.rootChecked
  have focused := pinned_signed_focus_reflects_same_trail_and_every_read out.reportTrace
  have correct := (Producer479.declarative_trail_reads_existing_edges_and_returns_at_the_terminal479 focused.1).2
  obtain ⟨geometry,head,row,rebuilt,headRead,_,_,_,_,meaning,walk⟩ :=
    successful_root_pin_preserves_exact_ordinary_origins_and_same_fit authority out.bound
  have sameHead := Option.some.inj (headRead.symm.trans out.atHead)
  subst head
  exact ⟨roots,geometry,focused.1,focused.2,out.sameBit.symm ▸ correct,rebuilt,meaning,walk⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
