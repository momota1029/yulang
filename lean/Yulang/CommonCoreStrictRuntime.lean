import Yulang.CommonCoreStrictApplication
import Yulang.CoreInference
import Yulang.CoreResolved

/-!
# Operational meaning of the common strict-application lowering

The pair capture used by the common source solver has exactly the written-order
request tree of the existing two-let strict lowering. These are equal trees,
including every payload, continuation and returned function; equality of row
sets alone would not establish evaluation order.

The source and resolved macros erase to one shared Core expression constructor
pattern. The argument is evaluated once before the function receives its pure
value. The two operands keep their original lexical environments.
-/

namespace Yulang.CommonCoreStrictRuntime

open Directed OperationalTyping

private theorem bind_assoc (action : Computation n Key Payload Response A)
    (first : A → Computation n Key Payload Response B)
    (last : B → Computation n Key Payload Response C) :
    (action.bind first).bind last = action.bind (fun value => (first value).bind last) := by
  induction action with
  | pure value => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request occurrence payload) (funext ih)

def forceApplication (function : Expr n Key Atom Γ (.arrow a b))
    (argument : Expr n Key Atom Γ a) : Expr n Key Atom Γ b :=
  .letE (.pair function argument) (.app (.fst (.var .here)) (.snd (.var .here)))

/-- One constructor pattern shared by the actual common inference lowering
and the independently evaluated, resolved lowering. -/
def coreForceApplication (function argument : Core.Expr signature) : Core.Expr signature :=
  .letE none (.pair function argument) (.app (.fst (.var 0)) (.snd (.var 0)))

theorem source_erasure (function argument : Inference.Expr) :
    Core.Required.embed (CommonCoreStrictApplication.forceApplication function argument) =
      coreForceApplication (Core.Required.embed function) (Core.Required.embed argument) := rfl

theorem operational_erasure (function : Expr n Key Atom Γ (.arrow a b))
    (argument : Expr n Key Atom Γ a) :
    Core.Resolved.operational (forceApplication function argument) =
      coreForceApplication (Core.Resolved.operational function)
        (Core.Resolved.operational argument) := rfl

/-- Every finite resolved shape context, every runtime environment, arbitrary
function and argument computations, and the complete signed request tree. -/
theorem eval_forceApplication [DecidableEq Key]
    (function : Expr n Key Atom Γ (.arrow a b)) (argument : Expr n Key Atom Γ a)
    (runtime : Env (Tree n Key Atom) Γ) :
    OperationalTyping.eval runtime (forceApplication function argument) =
      (OperationalTyping.eval runtime function).bind (fun f =>
        (OperationalTyping.eval runtime argument).bind (fun value => f (.pure value))) := by
  simp only [forceApplication, OperationalTyping.eval, Env.cons_here, bind_assoc,
    Computation.bind]

theorem eval_agrees_with_two_lets [DecidableEq Key]
    (function : Expr n Key Atom Γ (.arrow a b)) (argument : Expr n Key Atom Γ a)
    (runtime : Env (Tree n Key Atom) Γ) :
    OperationalTyping.eval runtime (forceApplication function argument) =
      OperationalTyping.eval runtime (StrictApplication.forceApplication function argument) := by
  rw [eval_forceApplication, StrictApplication.eval_forceApplication]

/-- The resolved checker retains both operand rows and the result row in
written order, and checks only the pure argument value against the input. -/
theorem infer_forceApplication [DecidableEq Key]
    (function : Expr n Key Atom Γ (.arrow a b)) (argument : Expr n Key Atom Γ a)
    (types : Env (CTy n Key) Γ) (input : CTy n Key a) (output : CTy n Key b)
    (functionRow : Row n Key) (actual : CTy n Key a)
    (functionInferred : OperationalTyping.infer types function =
      some ⟨CTy.arrow input output, functionRow⟩)
    (argumentInferred : OperationalTyping.infer types argument = some actual)
    (compatible : CLe (CTy.pure actual.value) input) :
    OperationalTyping.infer types (forceApplication function argument) =
      some ⟨output.value, functionRow ++ (actual.row ++ output.row)⟩ := by
  have checked : checkC (⟨actual.value, []⟩ : CTy n Key a)
      (⟨input.value, input.row⟩ : CTy n Key a) = true :=
    (checkC_exact (CTy.pure actual.value) input).mpr compatible
  simp [forceApplication, OperationalTyping.infer, functionInferred, argumentInferred,
    CTy.arrow, CTy.pure, checked, List.append_assoc]

end Yulang.CommonCoreStrictRuntime
