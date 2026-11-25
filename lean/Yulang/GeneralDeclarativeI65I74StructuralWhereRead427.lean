import Yulang.GeneralDeclarativeI65I74StructuralWhereSource427

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
open GeneralDeclarations (Clause)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeWitnessLiteral349 (eqExpr eq_expr)

structure RecordArgumentWire427 where
  clauseOrdinal : Nat
  argumentOrdinal : Nat
  rowOrdinal : Nat

private theorem capture_eq_point427 (a : Capture) (n : Nat)
    (h : a.lower = n ∧ a.center = n ∧ a.upper = n) : a = point n := by
  cases a
  dsimp at h
  obtain ⟨a,b,c⟩ := h
  subst_vars
  rfl

/-- The witness names addresses only. Child path, binder and constructor
come from original source; the name is recovered from the actual stored
row and checked against the original placement, not from the report. -/
def readOriginalRecordArgument427 {s q} (f : AuthoredBodyFrame393 s q)
    (wire : RecordArgumentWire427) :
    Option (OriginalRecordArgument427 f wire.clauseOrdinal wire.argumentOrdinal) := do
  match atClause : f.decl.requirements[wire.clauseOrdinal]? with
  | none => none
  | some clause =>
    match atArg : clause.arguments[wire.argumentOrdinal]? with
    | some (.record label (.var binder) (.app empty [])) =>
      if inside : binder ∈ f.decl.inputNames then
        match compiled : translateWhere427 s (writtenRecord427 label binder empty) with
        | none => none
        | some expr =>
          if exactCode : eqExpr expr (recordCode427 label binder) = true then
            match rowAt : s.current.ordinary.equations[wire.rowOrdinal]? with
            | none => none
            | some row =>
              let a := f.placement.compound clause wire.argumentOrdinal
              if address : a.lower = row.left ∧ a.center = row.left ∧ a.upper = row.left then
                if actual : eqExpr row.right (writtenRow427 f row.left label binder).right = true then
                  have rowExact : row = writtenRow427 f row.left label binder := by
                    cases row
                    exact congrArg (Equation.mk _) ((eq_expr ..).mp actual)
                  pure ⟨clause,atClause,label,binder,empty,atArg,inside,
                    compiled.trans (congrArg some ((eq_expr ..).mp exactCode)),row.left,
                    capture_eq_point427 a _ address,wire.rowOrdinal,
                    rowAt.trans (congrArg some rowExact)⟩
                else none
              else none
          else none
      else none
    | _ => none

theorem read_where_argument_reflects_exact_child_and_stored_row427 {s q f wire a}
    (_ : readOriginalRecordArgument427 (s:=s) (q:=q) f wire = some a) :
    (frameWhereKids400 f)[wire.clauseOrdinal]? = some a.child ∧
      a.child.demand.arguments[wire.argumentOrdinal]? = some (point a.name) ∧
      s.current.ordinary.equations[a.rowOrdinal]? = some (writtenRow427 f a.name a.label a.binder) :=
  ⟨structural_where_keeps_original_child_at_ordinal427 a,
    structural_where_child_argument_is_placed_point427 a,a.retained⟩

end Yulang.GeneralDeclarativeI65.StructuralWhere427
