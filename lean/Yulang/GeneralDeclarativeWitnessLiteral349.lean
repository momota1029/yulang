import Yulang.GeneralDeclarativeWitnessGround349

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessLiteral349
open Core.PresenceGeneration (RowTerm TyTerm)
open PresenceNormalForm (Atom)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarativeHead320 (Equation State Models)
open GeneralDeclarativeGrowth327 (Extends restrict)
open GeneralDeclarativeCurrentReceipt330 (Receipt literal)
open GeneralDeclarativeWitnessProblem349 (splitAnd)

deriving instance DecidableEq for RowTerm
deriving instance DecidableEq for TyTerm
deriving instance DecidableEq for Atom
mutual
def eqExpr : Expr → Expr → Bool
  | .variable a,.variable b => decide (a = b)
  | .primitive k xs,.primitive l ys => decide (k = l) && eqExprs xs ys
  | .nominal k xs,.nominal l ys => decide (k = l) && eqExprs xs ys
  | .record k a t,.record l b u => (decide (k = l) && eqExpr a b) && eqExpr t u
  | .variant k a,.variant l b => decide (k = l) && eqExpr a b
  | .join a b,.join c d => eqExpr a c && eqExpr b d
  | _,_ => false
termination_by e _ => sizeOf e

def eqExprs : List Expr → List Expr → Bool
  | [],[] => true
  | a::as,b::bs => eqExpr a b && eqExprs as bs
  | _,_ => false
termination_by es _ => sizeOf es
end

mutual
theorem eq_expr (x y : Expr) : eqExpr x y = true ↔ x = y := by
  cases x <;> cases y
  case primitive.primitive k xs l ys =>
    rw [eqExpr.eq_def]
    simp only [Bool.and_eq_true,decide_eq_true_eq,eq_exprs xs ys,Expr.primitive.injEq]
  case nominal.nominal k xs l ys =>
    rw [eqExpr.eq_def]
    simp only [Bool.and_eq_true,decide_eq_true_eq,eq_exprs xs ys,Expr.nominal.injEq]
  case record.record k a tail l b rest =>
    rw [eqExpr.eq_def]
    simp only [Bool.and_eq_true,decide_eq_true_eq,eq_expr a b,eq_expr tail rest,
      Expr.record.injEq,and_assoc]
  case variant.variant k a l b =>
    rw [eqExpr.eq_def]
    simp only [Bool.and_eq_true,decide_eq_true_eq,eq_expr a b,Expr.variant.injEq]
  case join.join a b c d =>
    rw [eqExpr.eq_def]
    simp only [Bool.and_eq_true,eq_expr a c,eq_expr b d,Expr.join.injEq]
  all_goals simp [eqExpr.eq_def]
termination_by sizeOf x

theorem eq_exprs (x y : List Expr) : eqExprs x y = true ↔ x = y := by
  cases x <;> cases y
  case cons.cons a as b bs =>
    rw [eqExprs.eq_def,Bool.and_eq_true,eq_expr a b,eq_exprs as bs,List.cons.injEq]
  all_goals simp [eqExprs.eq_def]
termination_by sizeOf x
end

local instance : DecidableEq Expr := fun a b => decidable_of_iff (eqExpr a b = true) (eq_expr a b)

deriving instance DecidableEq for Equation

/-- General structural literal comparison: tags, argument order, nominal
keys, record payload and tail, and all type/row atoms are compared.
It does not assert semantic equivalence of unequal terms. -/
def preserves (a b : State) : Bool :=
  (a.normal.ordinary.all (fun v => decide (v ∈ b.normal.ordinary)) &&
    a.normal.intervals.all (fun v => decide (v ∈ b.normal.intervals))) &&
  a.equations.all (fun v => decide (v ∈ b.equations))

theorem preserves_iff (a b : State) : preserves a b = true ↔ Extends a b := by
  simp only [preserves,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq]
  exact ⟨fun h => ⟨fun x seen => h.1.1 x seen,fun x seen => h.1.2 x seen,fun x seen => h.2 x seen⟩,
    fun h => ⟨⟨fun _ seen => h.constraints seen,fun _ seen => h.intervals seen⟩,fun _ seen => h.equations seen⟩⟩

theorem receipt {a b : State} (ok : preserves a b = true) : Receipt a b :=
  literal ((preserves_iff a b).mp ok)

theorem relays_same_model {a b : State} (ok : preserves a b = true) (m) (m_b : Models b m) :
    Models a m :=
  restrict ((preserves_iff a b).mp ok) m m_b

def sameRows (expected claimed : List Equation) : Bool := decide (claimed = expected)

theorem rows_exact (expected claimed : List Equation) :
    sameRows expected claimed = true ↔ claimed = expected := decide_eq_true_iff

theorem rows_ordinal {expected claimed : List Equation}
    (verified : sameRows expected claimed = true) (ix : Nat) :
    claimed[ix]? = expected[ix]? := by rw [(rows_exact _ _).mp verified]

end Yulang.GeneralDeclarativeWitnessLiteral349
