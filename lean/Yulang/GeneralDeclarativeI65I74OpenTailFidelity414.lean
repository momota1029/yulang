import Yulang.GeneralDeclarativeI65I74OpenTailDeclaration414

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.OpenTail414
open GeneralDeclarativeI65
open Checker408 (Problem Result)

structure PendingLocation where
  occurrence : List Nat
  role : Nat
  declaration : Nat
  whereClause : Nat
  root : Nat
  label : Nat
  field : Nat
  tail : Nat
  binder : Nat
  deriving DecidableEq, Repr

def OpenVerified.location {p : Problem} (v : OpenVerified p) : PendingLocation :=
  ⟨p.root.occurrence,p.root.demand.role,v.pending.candidate.decl.id,v.pending.candidate.clause,
    v.pending.input.root,v.pending.input.label,v.pending.input.field,v.pending.input.tail,
    v.pending.candidate.binder⟩

def locate (p : Problem) (w : OpenWire) : Option PendingLocation :=
  (replayOpen414 p w).map OpenVerified.location

theorem literal_open_coordinates_cohere414 {s q} (a b : OpenInput s q) :
    a.root = b.root ∧ a.label = b.label ∧ a.field = b.field ∧ a.tail = b.tail := by
  have exact := List.cons.inj (a.exactRows.symm.trans b.exactRows)
  have names := GeneralDeclarativeHead320.Equation.mk.inj exact.1
  exact ⟨names.1, (GeneralNominalCenteredHeadMatExpressions.Expr.record.inj names.2).1,
    GeneralNominalCenteredHeadMatExpressions.Expr.variable.inj (GeneralNominalCenteredHeadMatExpressions.Expr.record.inj names.2).2.1,
    GeneralNominalCenteredHeadMatExpressions.Expr.variable.inj (GeneralNominalCenteredHeadMatExpressions.Expr.record.inj names.2).2.2⟩

theorem exact_checked_open_locations_are_coherent414 {p : Problem}
    (v w : OpenVerified p) : v.location = w.location := by
  let a := v.pending.candidate
  let b := w.pending.candidate
  have sameDeclaration : a.decl = b.decl :=
    (List.cons.inj (a.exactVisible.symm.trans b.exactVisible)).1
  have sameWhere := (congrArg GeneralDeclarations.Declaration.requirements sameDeclaration)
  have clauseEq := List.cons.inj (a.requirements.symm.trans (sameWhere.trans b.requirements))
  have coord := literal_open_coordinates_cohere414 v.pending.input w.pending.input
  have exactClause : a.clause = b.clause := congrArg GeneralDeclarations.Clause.id clauseEq.1
  have args := congrArg GeneralDeclarations.Clause.arguments clauseEq.1
  have exactBinder : a.binder = b.binder :=
    GeneralDeclarationPatterns.Pattern.var.inj (List.cons.inj args).1
  change PendingLocation.mk _ _ a.decl.id a.clause _ _ _ _ a.binder =
    PendingLocation.mk _ _ b.decl.id b.clause _ _ _ _ b.binder
  rw [sameDeclaration,exactClause,coord.1,coord.2.1,coord.2.2.1,coord.2.2.2,exactBinder]

theorem two_wires_cannot_reassign_the_checked_tail414 (p : Problem) {u v : OpenWire}
    {a b : PendingLocation} (first : locate p u = some a) (second : locate p v = some b) :
    a = b := by
  unfold locate at first second
  cases x : replayOpen414 p u with
  | none => simp [x] at first
  | some left =>
    cases y : replayOpen414 p v with
    | none => simp [y] at second
    | some right =>
      simp only [x,Option.map_some,Option.some.injEq] at first
      simp only [y,Option.map_some,Option.some.injEq] at second
      exact first.symm.trans ((exact_checked_open_locations_are_coherent414 left right).trans second)

theorem no_pending_trace_can_issue_a_where_or_fixed_write414 {p : Problem}
    (scan : OpenVerified p) {t e} (trace : SourceTrace R6 p.state p.root t e) :
    t = .pending ∧ e = none ∧ writes trace = [] := by
  cases trace with
  | rootK2 cyclic => exact (scan.rootSafe cyclic).elim
  | selected event _ prior _ _ => exact (no_R4_election_on_open_tail414 scan.pending event prior).elim
  | other v _ rule _ =>
    rcases rule with before|⟨_,rfl,_⟩
    · exact (no_R5_diagnostic_on_open_tail414 scan.pending before).elim
    · exact ⟨rfl,rfl,rfl⟩

end Yulang.GeneralDeclarativeI65.I72.OpenTail414
