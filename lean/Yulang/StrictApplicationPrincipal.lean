import Yulang.StrictApplication
import Yulang.OperationalCorrespondence

/-!
# Strict evaluation from the existing recursive principal formula

The source of the constraints is the actual two-let lowering, including all
lambda bodies and handler arms. A solution is interpreted by the existing
structural model with union/intersection and value-restricted polymorphic let.
No annotated-checker acceptance or operational bound is supplied separately.
Solving this general formula and resolving source shapes remain separate tasks.
-/

namespace Yulang.StrictApplicationPrincipal

open Directed OperationalTyping OperationalCorrespondence

def principal (expression : Expr n Key Atom [] shape) :
    RecursiveEffects.Scheme Key (Fin n) Empty :=
  OperationalCorrespondence.principal (StrictApplication.compile expression)

theorem principal_operationally_valid [DecidableEq Key]
    (expression : Expr n Key Atom [] shape) (output : CoreComp n Key)
    (solution : (principal expression).Holds (Model n Key) (SignedStructural.rowView n Key)
      (Inference.extend Empty.elim output)) :
    CompHolds output (StrictApplication.eval Env.nil expression) := by
  rw [← StrictApplication.compile_correct]
  exact OperationalCorrespondence.principal_operationally_valid
    (StrictApplication.compile expression) output solution

theorem principal_effect_bound [DecidableEq Key]
    (expression : Expr n Key Atom [] shape) (output : CoreComp n Key)
    (solution : (principal expression).Holds (Model n Key) (SignedStructural.rowView n Key)
      (Inference.extend Empty.elim output)) :
    Computation.BoundedBy output.2 (StrictApplication.eval Env.nil expression) :=
  (principal_operationally_valid expression output solution).1

end Yulang.StrictApplicationPrincipal
