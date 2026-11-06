import Yulang.MultiOperationHandlerInference

/-!
# Compose an explicit incoming permission mask with syntax inference

The ordinary resolved `MultiOperationHandlerTyping.Expr.handler` has no
permission argument. This wrapper carries a supplied incoming-action mask
alongside that exact top-level handler syntax. Its executable checker first
rejects any denied operation arm, then invokes the existing syntax checker.
The independent judgement combines permission membership and actual syntax
typing, with no evaluator or runtime-bound premise.

The wrapper does not alter the underlying syntax or its signed coordinates.
In particular it does not insert `HandlerPermissions.enterTree`: transporting
source syntax and closures to a fresh coordinate is a separate elaboration
obligation. `inferred_opens_incoming_gate` connects the same permission check
to `checkedIncoming`, but does not assert that the two evaluations are equal.
Source mask inference, mixed-origin classification and operation payload arm
resolution remain outside this explicitly supplied contract.
-/

namespace Yulang.MultiOperationIncomingInference

open Directed OperationalTyping MultiOperationHandlers

/-- One resolved handler plus its explicit incoming-action permission contract.
The permission is static metadata; all executable bodies are ordinary syntax. -/
structure Handler (n : Nat) (Key Atom : Type) (context : List Shape) (result : Shape) where
  input : Shape
  count : Nat
  permission : Permission Key
  operations : Operations Key count
  target : VTy n Key result
  action : MultiOperationHandlerTyping.Expr n Key Atom context input
  onReturn : MultiOperationHandlerTyping.Expr n Key Atom (input :: context) result
  onOperation : Fin count →
    MultiOperationHandlerTyping.Expr n Key Atom (.atom :: .arrow .atom input :: context) result

def Handler.toExpr (handler : Handler n Key Atom context result) :
    MultiOperationHandlerTyping.Expr n Key Atom context result :=
  .handler handler.operations handler.target handler.action handler.onReturn handler.onOperation

/-- Permission membership is independent of the executable Boolean check. -/
def Permitted (handler : Handler n Key Atom context result) : Prop :=
  ∀ index, handler.permission (handler.operations.key index) = true

inductive Typing [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) (output : CTy n Key result) : Prop where
  | incoming : Permitted handler → MultiOperationHandlerTyping.Typing types handler.toExpr output →
      Typing types handler output

def infer [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) : Option (CTy n Key result) :=
  if checkPermission handler.permission handler.operations then
    MultiOperationHandlerTyping.infer types handler.toExpr
  else none

/-- The evaluator is unchanged. Source lowering must install the appropriate
signed boundary before using a supplied incoming contract for that boundary. -/
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
    | incoming permitted actual => exact ⟨permitted, actual⟩
  · rintro ⟨permitted, actual⟩
    exact .incoming permitted actual

/-- The permission gate and ordinary syntax checker together are exact for
an independently defined typing judgement. -/
theorem infer_exact [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) (output : CTy n Key result) :
    infer types handler = some output ↔ Typing types handler output := by
  cases allowed : checkPermission handler.permission handler.operations <;>
    simp [infer, typing_iff, Permitted, ← checkPermission_exact, allowed,
      MultiOperationHandlerTyping.infer_exact]

/-- This states the composition boundary explicitly: success requires both
all permitted keys and success of the existing ordinary syntax checker. -/
theorem infer_success_iff [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) (output : CTy n Key result) :
    infer types handler = some output ↔
      Permitted handler ∧ MultiOperationHandlerTyping.infer types handler.toExpr = some output := by
  rw [infer_exact, typing_iff, MultiOperationHandlerTyping.infer_exact]

/-- An unpermitted arm is rejected even if its body is unreachable or the
ordinary handler already has a successful inferred type. -/
theorem denied_arm_rejected [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) (index : Fin handler.count)
    (denied : handler.permission (handler.operations.key index) = false) :
    infer types handler = none := by
  simp [infer, checkPermission_rejects handler.permission handler.operations index denied]

theorem typing_evaluates [DecidableEq Key] (types : Env (CTy n Key) context)
    (handler : Handler n Key Atom context result) (output : CTy n Key result)
    (typed : Typing types handler output)
    (runtime : Env (Tree n Key Atom) context) (environment : EnvValid types runtime) :
    Valid output (eval runtime handler) :=
  MultiOperationHandlerTyping.typing_evaluates ((typing_iff _ _ _).mp typed).2 runtime environment

/-- Action and arm safety come from actual syntax typing. The only semantic
premise for an open expression is validity of its external environment. -/
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

/-- Static success opens the existing checked incoming runtime's permission
gate for this exact operation table. This is a gate correspondence, not a
fresh-coordinate transport theorem for `Handler.toExpr`. -/
theorem inferred_opens_incoming_gate [DecidableEq Key]
    (types : Env (CTy n Key) context) (handler : Handler n Key Atom context result)
    (output : CTy n Key result) (accepted : infer types handler = some output)
    (onReturn : A → Computation (scopes + 1) Key Payload Response B)
    (onOperation : Fin handler.count → Payload →
      (Response → Computation (scopes + 1) Key Payload Response A) →
        Computation (scopes + 1) Key Payload Response B)
    (action : Computation scopes Key Payload Response A) :
    checkedIncoming handler.permission handler.operations onReturn onOperation action =
      .ok (handleIncoming handler.permission handler.operations onReturn onOperation action) := by
  have permitted := ((typing_iff _ _ _).mp ((infer_exact _ _ _).mp accepted)).1
  have checked := (checkPermission_exact handler.permission handler.operations).mpr permitted
  simp [checkedIncoming, checked]

namespace Examples

def one : Operations Nat 1 :=
  ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

def denied : Handler 0 Nat Nat [] .atom where
  input := .atom
  count := 1
  permission := fun _ => false
  operations := one
  target := .atom
  action := .lit 5
  onReturn := .var .here
  onOperation := fun _ => .lit 8

def allowed : Handler 0 Nat Nat [] .atom :=
  { denied with permission := fun _ => true }

theorem permission_does_not_rewrite_syntax : allowed.toExpr = denied.toExpr := rfl

theorem ordinary_infer_accepts_denied_handler :
    MultiOperationHandlerTyping.infer Env.nil denied.toExpr = some (CTy.pure .atom) := rfl

theorem explicit_denied_rejects : infer Env.nil denied = none := rfl

theorem explicit_allowed_accepts : infer Env.nil allowed = some (CTy.pure .atom) := rfl

theorem allowed_typed : Typing Env.nil allowed (CTy.pure .atom) :=
  (infer_exact _ _ _).mp explicit_allowed_accepts

theorem allowed_evaluates : eval Env.nil allowed = .pure (5 : Nat) := rfl

theorem allowed_returns_from_checker :
    ∃ value, eval Env.nil allowed = .pure value ∧ ValidValue (VTy.atom : VTy 0 Nat .atom) value :=
  closed_empty_row_returns allowed .atom explicit_allowed_accepts

end Examples
end Yulang.MultiOperationIncomingInference
