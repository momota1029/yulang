import Yulang.MultiOperationHandlerInference

/-!
# The partial-payload syntax checker and its incoming permission gate

The supplied permission mask is checked against every written arm, regardless
of reachability, refutability or guard. Payload dispatch changes the residual
row, not decision 41. Syntax inference and safety apply to nested partial
handlers through `MultiOperationHandlerTyping`; this wrapper supplies the
incoming mask for one delimiter, as `MultiOperationIncomingInference` does
for total tables. It does not derive masks from source or transport closures
to a fresh coordinate.
-/

namespace Yulang.MultiOperationPayloadInference

open Directed OperationalTyping MultiOperationPayloadHandlers

structure Handler (n : Nat) (Key Atom : Type) (context : List Shape) (result : Shape) where
  input : Shape
  count : Nat
  permission : Permission Key
  arms : Fin count → Arm Key Atom
  target : VTy n Key result
  action : MultiOperationHandlerTyping.Expr n Key Atom context input
  onReturn : MultiOperationHandlerTyping.Expr n Key Atom (input :: context) result
  onArm : Fin count → MultiOperationHandlerTyping.Expr n Key Atom (.atom :: .arrow .atom input :: context) result

def Handler.toExpr (handler : Handler n Key Atom context result) :
    MultiOperationHandlerTyping.Expr n Key Atom context result :=
  .partialHandler handler.arms handler.target handler.action handler.onReturn handler.onArm

def Permitted (handler : Handler n Key Atom context result) : Prop :=
  ∀ index, handler.permission (handler.arms index).key = true

inductive Typing [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) (output : CTy n Key result) : Prop where
  | incoming : Permitted handler → MultiOperationHandlerTyping.Typing types handler.toExpr output →
      Typing types handler output

def infer [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) : Option (CTy n Key result) :=
  if checkPermission handler.permission handler.arms then
    MultiOperationHandlerTyping.infer types handler.toExpr
  else none

def eval [DecidableEq Key] (runtime : Env (Tree n Key Atom) context)
    (handler : Handler n Key Atom context result) : Tree n Key Atom result :=
  MultiOperationHandlerTyping.eval runtime handler.toExpr

theorem typing_iff [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) (output : CTy n Key result) :
    Typing types handler output ↔
      Permitted handler ∧ MultiOperationHandlerTyping.Typing types handler.toExpr output := by
  constructor
  · intro typed
    cases typed with
    | incoming allowed actual => exact ⟨allowed, actual⟩
  · rintro ⟨allowed, actual⟩
    exact .incoming allowed actual

theorem infer_exact [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) (output : CTy n Key result) :
    infer types handler = some output ↔ Typing types handler output := by
  cases allowed : checkPermission handler.permission handler.arms <;>
    simp [infer, typing_iff, Permitted, ← checkPermission_exact, allowed,
      MultiOperationHandlerTyping.infer_exact]

theorem denied_arm_rejected [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) (index : Fin handler.count)
    (denied : handler.permission (handler.arms index).key = false) :
    infer types handler = none := by
  simp [infer, checkPermission_rejects handler.permission handler.arms index denied]

theorem typing_evaluates [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) (output : CTy n Key result)
    (typed : Typing types handler output)
    (runtime : Env (Tree n Key Atom) context) (environment : EnvValid types runtime) :
    Valid output (eval runtime handler) :=
  MultiOperationHandlerTyping.typing_evaluates ((typing_iff _ _ _).mp typed).2 runtime environment

/-- No additional assumption about the evaluation of action or arms is needed. -/
theorem inferred_operationally_valid [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) (output : CTy n Key result)
    (accepted : infer types handler = some output)
    (runtime : Env (Tree n Key Atom) context) (environment : EnvValid types runtime) :
    Valid output (eval runtime handler) :=
  typing_evaluates types handler output ((infer_exact _ _ _).mp accepted) runtime environment

theorem closed_empty_row_returns [DecidableEq Key]
    (handler : Handler n Key Atom [] result) (valueType : VTy n Key result)
    (accepted : infer Env.nil handler = some ⟨valueType, []⟩) :
    ∃ value, eval Env.nil handler = .pure value ∧ ValidValue valueType value :=
  MultiOperationHandlerTyping.closed_empty_row_returns handler.toExpr valueType
    ((typing_iff _ _ _).mp ((infer_exact _ _ _).mp accepted)).2

end Yulang.MultiOperationPayloadInference

namespace Yulang.MultiOperationHandlerTyping

open Directed OperationalTyping MultiOperationHandlers MultiOperationPayloadHandlers

/-- Replacing a total table by its irrefutable payload-arm representation
preserves the complete request tree, including every continuation branch. -/
theorem eval_total_as_partial [DecidableEq Key]
    (runtime : Env (Tree n Key Atom) context) (operations : Operations Key count)
    (target : VTy n Key b) (action : Expr n Key Atom context a)
    (onReturn : Expr n Key Atom (a :: context) b)
    (onOperation : Fin count → Expr n Key Atom (.atom :: .arrow .atom a :: context) b) :
    eval runtime (.partialHandler (ofOperations operations) target action onReturn onOperation) =
      eval runtime (.handler operations target action onReturn onOperation) :=
  handle_ofOperations operations _ _ _

theorem infer_total_as_partial [DecidableEq Key]
    (types : Env (CTy n Key) context) (operations : Operations Key count)
    (target : VTy n Key b) (action : Expr n Key Atom context a)
    (onReturn : Expr n Key Atom (a :: context) b)
    (onOperation : Fin count → Expr n Key Atom (.atom :: .arrow .atom a :: context) b) :
    infer types (.partialHandler (ofOperations operations) target action onReturn onOperation) =
      infer types (.handler operations target action onReturn onOperation) := by
  simp only [infer, ofOperations_removedKeys]

theorem typing_total_as_partial [DecidableEq Key]
    (types : Env (CTy n Key) context) (operations : Operations Key count)
    (target : VTy n Key b) (action : Expr n Key Atom context a)
    (onReturn : Expr n Key Atom (a :: context) b)
    (onOperation : Fin count → Expr n Key Atom (.atom :: .arrow .atom a :: context) b)
    (output : CTy n Key b) :
    Typing types (.partialHandler (ofOperations operations) target action onReturn onOperation) output ↔
      Typing types (.handler operations target action onReturn onOperation) output := by
  rw [← infer_exact, ← infer_exact, infer_total_as_partial]

end Yulang.MultiOperationHandlerTyping
