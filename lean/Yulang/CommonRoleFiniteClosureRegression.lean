import Yulang.CommonRoleFiniteStructuralClosure
import Yulang.CommonRoleAlternatingRegression

/-! A small carrier witnesses alternating transitivity and payload decomposition.
Its extra atoms are candidates, not assumptions: only derived indices are emitted. -/
namespace Yulang.CommonRoleFiniteClosureRegression
open Core.PresenceGeneration (Comp)
open PresenceNormalForm (Atom All)
open CommonRoleFiniteStructuralClosure (close model_exact)

def extra : List (Atom (Fin 4)) :=
  [.tyLe (.pair (.var 0) (.base .int)) (.pair (.var 1) (.base .int)),
   .tyLe (.var 0) (.var 1),
   .tyLe (.pair (.base .int) (.var 3)) (.var 1),
   .tyLe (.pair (.base .int) (.var 3)) (.pair (.base .int) (.base .bool)),
   .tyLe (.var 3) (.base .bool)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem alternating_detected : CommonRoleRecursivePaths.check
    (close CommonRoleAlternatingRegression.input extra) = true := by decide

theorem input_no_model (a : Fin 4 → Comp Common.model) :
    ¬ All Common.model a CommonRoleAlternatingRegression.input := by
  intro h
  exact CommonRoleRecursivePaths.checked_no_model_all _ alternating_detected a
    ((model_exact _ _ a).mpr h)

end Yulang.CommonRoleFiniteClosureRegression
