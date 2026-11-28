import Yulang.GeneralDeclarativeI65I74ProducerReport479

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.Producer479

open RetainedFull445 (FullProblem)
open PreparedDeclarations463 (CheckedTable PrecheckedHead readPrecheckedHead)
open GeneralDeclarativeHead320 (Equation)
open ObservationAlternatives473 (Positions oldPosition graphOf)
open LiteralVisits473 (terminalIsField pathEndsWithField StepWire)
open InputCoordinates475 (rawAt registryAt SafeEdgeTrail477 oneCompiledStep477 SamePhaseInputObservation478)
open QuotientObservation471 (ReturnsUpToEquality)
open CommonRoleRegularGraph (successors)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)

/-- Local geometry reflection for an arbitrary successful route check.
The separate source/complete authority predicates do not follow from
this shape check. -/
theorem a_checked_route_reflects_one_actual_safe_prefix_and_exact_terminal480
    {n : Nat} {p : FullProblem} {gd : CheckedTable p.old.state.core.current}
    {pos : Positions n} {rel} {w : RouteWire n} {out}
    (run : readRoute p gd pos rel w = some out) :
    ∃ (head : PrecheckedHead (p := p.old) gd)
        (first finish : Site p.old.state.core pos) (row : Equation) (bit : Bool),
      visible p.old.state.core p.old.root = [head.orig.declaration] ∧
      (registryAt p)[w.declarationOrdinal]? = some head.orig.declaration ∧
      head.orig.location.headArgument = w.argument ∧
      first.pattern = head.orig.original ∧ first.query = head.orig.code ∧
      first.index = w.trail.cursor.which ∧
      oldPosition pos first.index = .logical head.orig.capture.lower ∧
      (rawAt p).equations[(pos.cells.get first.index).oldOrdinal]? = some row ∧
      row.left = head.orig.capture.lower ∧ row.right = first.term ∧
      rootedInField w.trail.tail = true ∧ pathEndsWithField (w.trail.tail.map Prod.fst) ∧
      Trail p.old.state.core pos rel first (w.trail.tail.map Prod.fst)
        (w.trail.tail.map (fun x => x.2.which)) finish bit ∧
      out = ⟨⟨p.old.root.occurrence,head.orig.declaration.id,w.declarationOrdinal⟩,
        w.argument,w.trail.tail.flatMap (fun x => x.1.written),
        w.trail.tail.map (fun x => oneCompiledStep477 x.1.action),oldPosition pos finish.index,bit⟩ := by
  unfold readRoute at run
  cases headRead : readPrecheckedHead (p := p.old) gd ⟨0,w.argument⟩ with
  | none => simp [headRead] at run
  | some head =>
    simp only [headRead,bind,Option.bind] at run
    split at run
    · rename_i scope
      cases rootRead : siteAt (s := p.old.state.core) (pos := pos) w.trail.cursor.which
            head.orig.original head.orig.code with
      | none => simp [rootRead] at run
      | some first =>
        simp only [rootRead] at run
        cases rowRead : (rawAt p).equations[(pos.cells.get w.trail.cursor.which).oldOrdinal]? with
        | none => simp [rowRead] at run
        | some row =>
          simp only [rowRead] at run
          split at run
          · rename_i rootScope
            cases seen : readTrail rel first w.trail with
            | none => simp [seen] at run
            | some result =>
              rcases result with ⟨finish,bit⟩
              simp only [seen,pure,Option.some.injEq] at run
              obtain ⟨loc,trace⟩ := finite_trail_wire_reflects_exact_selected_path479 seen
              have heads : first.pattern = head.orig.original ∧ first.query = head.orig.code := by
                unfold siteAt at rootRead
                split at rootRead
                · cases rootRead
                · cases rootRead
                  exact ⟨rfl,rfl⟩
              exact ⟨head,first,finish,row,bit,scope.2.1,scope.2.2,scope.1,heads.1,heads.2,
                loc.symm,loc ▸ rootScope.1,loc ▸ rowRead,rootScope.2.1,
                (eq_expr ..).mp rootScope.2.2.1,rootScope.2.2.2.1,
                LiteralVisits473.terminal_selector_is_exact.mp rootScope.2.2.2.2,trace,run.symm⟩
          · cases run
    · cases run

end Yulang.GeneralDeclarativeI65.I72.Producer479
