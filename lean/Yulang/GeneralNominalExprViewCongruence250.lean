import Yulang.GeneralNominalRebaseEffectView243
import Yulang.GeneralDictionaryDefaultExpression209
import Yulang.GeneralNominalRawCongruence238
namespace Yulang.GeneralNominalExprViewCongruence250
open GeneralNominalAssignmentCongruence238 (Same type_eval)
open GeneralNominalRawCongruence238 (equiv_iff)
open GeneralNominalRebaseEffectView243
open GeneralNominalCommonBridge (Assignment)
open GeneralDictionaryDefaultExpression209
open CommonNominalFullCarrier
open CommonRoleOutermostResolver (All₂)
variable {first last : Assignment}
mutual
 theorem eval_equivalent (same : Same first last) (expression : Expr) :
 Equivalent (eval first expression) (eval last expression) := by
 cases expression with
 | source term => exact type_eval same term
 | primitive constructor arguments => exact primitive_equivalent constructor (evals_equivalent same arguments)
 | nominal name arguments => exact nominal_equivalent name (evals_equivalent same arguments)
 | record label payload tail =>
   have a := eval_equivalent same payload
   have b := eval_equivalent same tail
   exact ⟨common_record_mono label a.1 b.1,common_record_mono label a.2 b.2⟩
 | variant tag payload =>
   have a := eval_equivalent same payload
   exact ⟨(common_variant_iff tag _ _).mpr a.1,(common_variant_iff tag _ _).mpr a.2⟩
 | join a b =>
   have one := eval_equivalent same a
   have two := eval_equivalent same b
   exact ⟨common_union_mono one.1 two.1,common_union_mono one.2 two.2⟩
 theorem evals_equivalent (same : Same first last) (expressions : List Expr) :
 All₂ Equivalent (evals first expressions) (evals last expressions) := by
 cases expressions with
 | nil => exact .nil
 | cons head rest => exact .cons (eval_equivalent same head) (evals_equivalent same rest)
end

theorem equation_iff (same : Same first last) (equation : Equation) :
 equation.Holds first ↔ equation.Holds last :=
 equiv_iff (type_eval same equation.target) (eval_equivalent same equation.expression)
end Yulang.GeneralNominalExprViewCongruence250
