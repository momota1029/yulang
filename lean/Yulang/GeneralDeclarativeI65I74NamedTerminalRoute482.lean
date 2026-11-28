import Yulang.GeneralDeclarativeI65I74TypedWholeAuthoredFocus482
import Yulang.GeneralDeclarativeI65I74AuthoredTerminalCompare482
import Yulang.GeneralDeclarativeI65I74TypedFocusMeaning482

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
open RetainedFull445 (FullProblem)
open Producer479 (PriorPhase RouteWire Site Hop siteAt readRoute readHop)
open PreparedDeclarations463 (CheckedTable PrecheckedHead readPrecheckedHead)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open LiteralVisits473 (Checkpoint StepWire ReadStep readLiteralVisitStep)
open InputCoordinates475 (rawAt SamePhaseInputObservation478)
open TypedRootSafety482 (requestRootCheck requestRootCheckSound AllRootSafe)
open QuotientObservation471 (ReturnsUpToEquality)
open GeneralDeclarativeWitnessOrigins350 (attach)
open GeneralDeclarativeTermWalk322 (Walk)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)

structure NamedTerminalWire (n : Nat) where
  argument : Nat
  declarationOrdinal : Nat
  cursor : Checkpoint n
  beforeLast : List (StepWire × Checkpoint n)
  move : StepWire
  terminal : Checkpoint n
  source : ReadCard
  initialAuthor : Nat
  roots : List (Checkpoint n)

def NamedTerminalWire.route (wire : NamedTerminalWire n) : RouteWire n :=
  ⟨wire.argument,wire.declarationOrdinal,⟨wire.cursor,wire.beforeLast ++ [(wire.move,wire.terminal)]⟩⟩

structure NamedTerminalReceipt {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (positions : Positions n)
    (rel : List (Fin n × Fin n)) (basis : PriorPhase) (wire : NamedTerminalWire n) where
  original : PrecheckedHead (p := p.old) gd
  headRead : readPrecheckedHead gd ⟨0,wire.argument⟩ = some original
  here : Site p.old.state.core positions
  startExact : siteAt (s := p.old.state.core) (pos := positions) wire.cursor.which
    original.orig.original original.orig.code = some here
  rootChecked : requestRootCheck p positions rel wire.roots = true
  initial : AuthoredCardRouteReceipt
  bound : runRootPinnedAuthoredCard p gd positions rel basis wire.route wire.source wire.initialAuthor = some initial
  prefixResult : FocusResult (p := p) basis.authors here wire.source wire.beforeLast
  literalStep : ReadStep p.old.state.core wire.move prefixResult.finish.pattern prefixResult.finish.query prefixResult.finish.term
  literalCheck : readLiteralVisitStep p.old.state.core prefixResult.finish.pattern prefixResult.finish.query
    prefixResult.finish.term wire.move = some literalStep
  last : Site p.old.state.core positions
  lastRead : readHop prefixResult.finish wire.move wire.terminal.which = some last
  childQuery : literalStep.childQuery = last.query
  logicalName : Nat
  childNamed : literalStep.actualRawChild = .variable logicalName
  finalCard : ReadCard
  pickedCard : subCard wire.move.action prefixResult.selected = some finalCard
  conclusion : AuthoredTerminalCompare p basis.authors positions rel wire.terminal logicalName last.query finalCard
  samePlace : initial.output.outcome.2.2.1 = oldPosition positions last.index
  sameBit : initial.output.outcome.2.2.2 = conclusion.sign

private def verified {A : Type} (x : Option A) : Option {v // x = some v} :=
  match x with | some v => some ⟨v,rfl⟩ | none => none

/-- No other action may follow the bisimilar endpoint. Intermediate
visits still use exact authored arrival. This reuses the original route
and does not rewrite either of the terminal physical presentations. -/
def readNamedTerminalRoute {n : Nat} (p : FullProblem)
    (gd : CheckedTable p.old.state.core.current) (positions : Positions n)
    (rel : List (Fin n × Fin n)) (basis : PriorPhase) (wire : NamedTerminalWire n) :
    Option (NamedTerminalReceipt p gd positions rel basis wire) := do
  if roots : requestRootCheck p positions rel wire.roots = true then
    let head ← verified (readPrecheckedHead (p := p.old) gd ⟨0,wire.argument⟩)
    let first ← verified (siteAt (s := p.old.state.core) (pos := positions)
      wire.cursor.which head.val.orig.original head.val.orig.code)
    let old ← verified (runRootPinnedAuthoredCard p gd positions rel basis wire.route wire.source wire.initialAuthor)
    let before ← readFocusedChain (p := p) basis.authors first.val wire.source wire.beforeLast
    let step ← verified (readLiteralVisitStep p.old.state.core before.finish.pattern
      before.finish.query before.finish.term wire.move)
    let last ← verified (readHop before.finish wire.move wire.terminal.which)
    let card ← verified (subCard wire.move.action before.selected)
    match owner : step.val.actualRawChild with
    | .variable logicalName =>
      if q : eqExpr step.val.childQuery last.val.query = true then
        let terminal ← readAuthoredTerminalCompare p basis.authors positions rel wire.terminal logicalName last.val.query card.val
        if same : old.val.output.outcome.2.2.1 = oldPosition positions last.val.index ∧
            old.val.output.outcome.2.2.2 = terminal.sign then
          pure ⟨head.val,head.property,first.val,first.property,roots,old.val,old.property,
            before,step.val,step.property,last.val,last.property,(eq_expr _ _).mp q,
            logicalName,owner,card.val,card.property,terminal,same.1,same.2⟩
        else none
      else none
    | _ => none
  else none

theorem original_terminal_report_with_distinct_author_is_sound
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current} {pos : Positions n} {rel : List (Fin n × Fin n)}
    {basis : PriorPhase} {wire : NamedTerminalWire n}
    (out : NamedTerminalReceipt p gd pos rel basis wire)
    {done : Nat → Prop} {support : GeneralDeclarativeOrigins321.Supported (rawAt p) done}
    (authority : ∀ row ∈ basis.authors.authored, support.derivesFrom row .source) :
    AllRootSafe p.old.state.core pos (p.old.root.demand.arguments.map (fun a => a.lower))
      (wire.roots.map Checkpoint.which) ∧
    readRoute p gd pos rel wire.route = some out.initial.output ∧
    Nonempty (Hop out.prefixResult.finish out.last wire.move) ∧
    FocusMeaning (p := p) basis.authors out.here wire.source wire.beforeLast
      out.prefixResult.finish out.prefixResult.selected out.prefixResult.reads ∧
    (out.initial.output.outcome.2.2.2 = true ↔
      ReturnsUpToEquality (graphOf p.old.state.core pos) out.conclusion.lexical) ∧
    ∃ rebuilt : Expr, (∀ m : Model, FitsFull p.state m → eqAt m.assignment out.conclusion.row.right rebuilt) ∧
      Walk .actual rebuilt out.last.query out.conclusion.marks := by
  obtain ⟨attached,_,_,_,_,_,_,_,_,_,_,_,geometry⟩ := actual_root_pinned_read_iff.mp out.bound
  have supportExact := distinct_old_terminal_presentation_never_changes_exact_regular_sign out.conclusion
  have actualSign := supportExact.2.2.2.2.2
  have picked := (Producer479.reified_hop_keeps_the_same_old_place479 out.lastRead).2
  exact ⟨requestRootCheckSound _ _ _ _ out.rootChecked,geometry,picked,
    every_actual_focused_site_has_typed_meaning_in_same_fits attached authority out.prefixResult.trail,
    out.sameBit.symm ▸ actualSign,
    authored_terminal_compare_has_old_typed_meaning_in_every_same_fit authority attached out.conclusion⟩

end Yulang.GeneralDeclarativeI65.I72.SourceExposure481.ClosedBank
