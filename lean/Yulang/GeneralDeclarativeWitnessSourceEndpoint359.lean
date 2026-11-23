import Yulang.GeneralDeclarativeWitnessOpenSpine359

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessSourceEndpoint359
open GeneralDeclarativeHead320 (Equation State Models)
open GeneralDeclarativeWitnessAuthoredProjection358 (Source)
open GeneralDeclarativeWitnessOpenSpine359 (Path sem read_in_model)
open GeneralDeclarativeBounds319 (Bound bound_sound)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty Equivalent Subtype subtype_trans)
open GeneralDeclarativeExactDelete337 (subtract congruent monotone)

inductive Witness where
  | literal (expr : Expr)
  | linked (path : Path)

def Witness.code (root : Nat) : Witness → Expr
  | .literal expr => expr
  | .linked path => path.expand root

inductive Read (source : Source) (s : State) (root : Nat) : Witness → Prop where
  | literal {expr : Expr} :
      (⟨root,expr⟩ : Equation) ∈ source.authored → (⟨root,expr⟩ : Equation) ∈ s.equations →
      Read source s root (.literal expr)
  | linked {path : Path} :
      GeneralDeclarativeWitnessOpenSpine359.Read source s root path → Read source s root (.linked path)

def check (source : Source) (s : State) (root : Nat) : Witness → Bool
  | .literal expr => decide (((⟨root,expr⟩ : Equation) ∈ source.authored) ∧ (⟨root,expr⟩ : Equation) ∈ s.equations)
  | .linked path => GeneralDeclarativeWitnessOpenSpine359.check source s root path

theorem check_exact {source s root w} : check source s root w = true ↔ Read source s root w := by
  cases w with
  | literal expr =>
    simp only [check,decide_eq_true_eq]
    exact ⟨fun row => .literal row.1 row.2,fun h => by cases h with | literal author current => exact ⟨author,current⟩⟩
  | linked path =>
    rw [check,GeneralDeclarativeWitnessOpenSpine359.check_exact]
    exact ⟨Read.linked,fun h => by cases h; assumption⟩

theorem endpoint_in_model {source s root w} (read : Read source s root w)
    (m : Assignment) (fit : Models s m) : Equivalent (m root).1 (sem m (w.code root)) := by
  cases read with
  | literal _ current => exact fit.2 _ current
  | linked proof => exact read_in_model proof m fit

theorem residual_endpoints {source s} {arg : Capture} {lo hi}
    (left : Read source s arg.lower lo) (right : Read source s arg.upper hi)
    (direct : Bound s.normal arg.lower arg.center ∧ Bound s.normal arg.center arg.upper)
    (m : Assignment) (fit : Models s m) (keys : List Nat) :
    Equivalent (subtract keys (m arg.lower).1) (subtract keys (sem m (lo.code arg.lower))) ∧
    Equivalent (subtract keys (m arg.upper).1) (subtract keys (sem m (hi.code arg.upper))) ∧
    Subtype (subtract keys (sem m (lo.code arg.lower))) (subtract keys (m arg.center).1) ∧
    Subtype (subtract keys (m arg.center).1) (subtract keys (sem m (hi.code arg.upper))) := by
  have low := endpoint_in_model left m fit
  have high := endpoint_in_model right m fit
  exact ⟨congruent keys low,congruent keys high,
    monotone keys (subtype_trans low.2 (bound_sound m fit.1 direct.1)),
    monotone keys (subtype_trans (bound_sound m fit.1 direct.2) high.1)⟩

end Yulang.GeneralDeclarativeWitnessSourceEndpoint359
