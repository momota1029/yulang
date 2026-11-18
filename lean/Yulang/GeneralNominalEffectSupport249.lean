import Yulang.GeneralNominalRebaseEffectView243
import Yulang.GeneralPresenceConsumerSupport246

/-! Total finite support and literal evaluation preservation for actual
materialized effect expressions, including primitive and nominal argument lists. -/
namespace Yulang.GeneralNominalEffectSupport249
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralNominalRebaseEffectView243
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralPresenceConsumerSupport246

mutual
 def support : Expr → List Nat
 | .source term => typedReads term
 | .primitive _ arguments | .nominal _ arguments => supports arguments
 | .record _ payload tail | .join payload tail => support payload ++ support tail
 | .variant _ payload => support payload
 def supports : List Expr → List Nat
 | [] => []
 | first :: rest => support first ++ supports rest
end

mutual
 theorem eval_equal (expression : Expr) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ support expression, (first n).1 = (last n).1) :
 eval first expression = eval last expression := by
 cases expression with
 | source term => exact type_eval_equal model first last rows term types
 | primitive constructor arguments => simp only [eval,evals_equal arguments first last rows types]
 | nominal name arguments => simp only [eval,evals_equal arguments first last rows types]
 | record label payload tail => simp only [eval,
     eval_equal payload first last rows (fun n h => types n (List.mem_append_left _ h)),
     eval_equal tail first last rows (fun n h => types n (List.mem_append_right _ h))]
 | join payload tail => simp only [eval,
     eval_equal payload first last rows (fun n h => types n (List.mem_append_left _ h)),
     eval_equal tail first last rows (fun n h => types n (List.mem_append_right _ h))]
 | variant tag payload => simp only [eval,eval_equal payload first last rows types]
 theorem evals_equal (expressions : List Expr) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ supports expressions, (first n).1 = (last n).1) :
 evals first expressions = evals last expressions := by
 cases expressions with
 | nil => rfl
 | cons expression rest => simp only [evals,
     eval_equal expression first last rows (fun n h => types n (List.mem_append_left _ h)),
     evals_equal rest first last rows (fun n h => types n (List.mem_append_right _ h))]
end

def equationReads (equation : Equation) : List Nat := typedReads equation.target ++ support equation.expression

theorem equation_iff (equation : Equation) (first last : Assignment)
 (rows : ∀ n, (first n).2 = (last n).2)
 (types : ∀ n ∈ equationReads equation, (first n).1 = (last n).1) :
 equation.Holds first ↔ equation.Holds last := by
 simp only [Equation.Holds,
   type_eval_equal model first last rows equation.target (fun n h => types n (List.mem_append_left _ h)),
   eval_equal equation.expression first last rows (fun n h => types n (List.mem_append_right _ h))]
end Yulang.GeneralNominalEffectSupport249
