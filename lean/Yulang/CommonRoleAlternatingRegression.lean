import Yulang.CommonRolePathDecomposition

/-! A genuine two-round dependency: structural decomposition creates an edge,
then that edge enables another structural decomposition. -/
namespace Yulang.CommonRoleAlternatingRegression
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)

def input : List (Atom (Fin 4)) :=
  [.tyLe (.pair (.var 0) (.base .int)) (.var 2),
   .tyLe (.var 2) (.pair (.var 1) (.base .int)),
   .tyLe (.pair (.base .int) (.var 3)) (.var 0),
   .tyLe (.var 1) (.pair (.base .int) (.base .bool)),
   .tyLe (.base .int) (.var 3)]

theorem first_pass_misses : CommonRoleRecursivePaths.check
    (CommonRolePathDecomposition.normalize input) = false := by decide

theorem second_pass_detects : CommonRoleRecursivePaths.check
    (CommonRolePathDecomposition.normalize
      (CommonRolePathDecomposition.normalize input)) = true := by decide

theorem no_model (a : Fin 4 → Comp Common.model) : ¬ All Common.model a input := by
  intro h
  exact CommonRoleRecursivePaths.checked_no_model_all _ second_pass_detects a
    ((CommonRolePathDecomposition.normalize_exact _ a).mpr
      ((CommonRolePathDecomposition.normalize_exact _ a).mpr h))
end Yulang.CommonRoleAlternatingRegression
