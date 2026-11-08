import Yulang.CommonArgumentEffectCast
import Yulang.CommonCoreStrictRuntime

/-!
# Request-tree meaning of explicit argument-effect conversion

The empty input row is the resolved kernel's value-only interface after forcing,
not the meaning of an omitted source input row. No source omission elaboration
is defined or proved. The resolved historical operational core receives suspended arguments. The
adapter below uses only its existing bind/pure operations. It equals ordinary
strict application, including all requests and continuations, so no extra
runtime mechanism is proposed. This is not whole-source cast insertion.
-/
namespace Yulang.ArgumentEffectCastRuntime
open Directed OperationalTyping

/-- Shape-resolved form of the kernel value-only-arrow adapter judgment. It
keeps standard `VLe` unchanged and records no value-level success premise. -/
inductive ResolvedCast : VTy n Key (.arrow a b) → VTy n Key (.arrow a b) → Prop where
  | lift (input : VTy n Key a) (output : VTy n Key b) (body incoming : Row n Key) :
      ResolvedCast (.arrow input [] output body)
        (.arrow input incoming output (body ++ incoming))

/-- The interpretation of explicit argument-effect conversion in the existing
computation-argument semantic carrier. -/
def forceValue (function : Value n Key Atom (.arrow a b)) : Value n Key Atom (.arrow a b) :=
  fun argument => argument.bind (fun value => function (.pure value))

/-- Soundness, every shape and every incoming/body row: a kernel value-only function's
converted value accepts effectful arguments and retains all incoming effects. -/
theorem converted_valid (input : VTy n Key a) (output : VTy n Key b)
    (body incoming : Row n Key) (function : Value n Key Atom (.arrow a b))
    (valid : ValidValue (.arrow input [] output body) function) :
    ValidValue (.arrow input incoming output (body ++ incoming)) (forceValue function) := by
  intro argument bounded returned
  have joined := bind_bounds_returns incoming body (ValidValue input) (ValidValue output)
    argument (fun value => function (.pure value)) bounded returned
    (fun value good => valid (.pure value) trivial good)
  exact ⟨Computation.bounded_mono (by
    intro occurrence member
    simpa only [List.mem_append, or_comm] using member) joined.1, joined.2⟩

/-- Soundness for every derivation of the independent resolved conversion.
Source/target shapes and rows are not fixed examples. -/
theorem resolved_cast_sound {source target : VTy n Key (.arrow a b)}
    (converted : ResolvedCast source target)
    (function : Value n Key Atom (.arrow a b)) (valid : ValidValue source function) :
    ValidValue target (forceValue function) := by
  cases converted with
  | lift input output body incoming =>
      exact converted_valid input output body incoming function valid

/-- Auxiliary: the cast never changes a pure-argument call. -/
theorem pure_call (function : Value n Key Atom (.arrow a b)) (value : Value n Key Atom a) :
    forceValue function (.pure value) = function (.pure value) := rfl

/-- Auxiliary: repeated explicit argument forcing does not duplicate effects. -/
theorem force_idempotent (function : Value n Key Atom (.arrow a b)) :
    forceValue (forceValue function) = forceValue function := rfl

/-- Operational preservation: evaluation of the actual common strict lowering
is exactly historical application of the interpreted converted function value.
The operands, environment, shapes and full request trees are arbitrary. -/
theorem strict_application_agrees [DecidableEq Key]
    (function : Expr n Key Atom Γ (.arrow a b)) (argument : Expr n Key Atom Γ a)
    (runtime : Env (Tree n Key Atom) Γ) :
    OperationalTyping.eval runtime (CommonCoreStrictRuntime.forceApplication function argument) =
      (OperationalTyping.eval runtime function).bind
        (fun value => forceValue value (OperationalTyping.eval runtime argument)) := by
  exact CommonCoreStrictRuntime.eval_forceApplication function argument runtime

private theorem valueOrder_refl (type : VTy n Key s) : VLe type type := by
  induction type with
  | atom => trivial
  | pair a b iha ihb => exact ⟨iha, ihb⟩
  | arrow a ea b eb iha ihb => exact ⟨iha, (fun _ member => member), ihb, (fun _ member => member)⟩

/-- Operational preservation at the actual resolved strict application checker:
the output row includes the function, argument and body effects exactly once
syntactically. Row inclusion may identify duplicate occurrences semantically. -/
theorem checker_retains_incoming [DecidableEq Key]
    (function : Expr n Key Atom Γ (.arrow a b)) (argument : Expr n Key Atom Γ a)
    (types : Env (CTy n Key) Γ) (input : VTy n Key a) (output : VTy n Key b)
    (body incoming functionRow : Row n Key)
    (functionInferred : OperationalTyping.infer types function =
      some ⟨.arrow input [] output body, functionRow⟩)
    (argumentInferred : OperationalTyping.infer types argument = some ⟨input, incoming⟩) :
    OperationalTyping.infer types (CommonCoreStrictRuntime.forceApplication function argument) =
      some ⟨output, functionRow ++ (incoming ++ body)⟩ := by
  apply CommonCoreStrictRuntime.infer_forceApplication function argument types
    ⟨input, []⟩ ⟨output, body⟩ functionRow ⟨input, incoming⟩
    functionInferred argumentInferred
  exact ⟨valueOrder_refl _, fun _ member => member⟩

/-- Soundness for arbitrary higher-order consumers: once a consumer expects the
converted arrow, the explicit cast is a valid pure argument to it. This is a
resolved semantic boundary, not completeness of source expected-type insertion. -/
theorem higher_order_consumer_valid (input : VTy n Key a) (output : VTy n Key b)
    (body incoming consumerRow : Row n Key) (answer : VTy n Key c)
    (function : Value n Key Atom (.arrow a b))
    (consumer : Value n Key Atom (.arrow (.arrow a b) c))
    (functionValid : ValidValue (.arrow input [] output body) function)
    (consumerValid : ValidValue
      (.arrow (.arrow input incoming output (body ++ incoming)) [] answer consumerRow) consumer) :
    Valid (⟨answer, consumerRow⟩ : CTy n Key c) (consumer (.pure (forceValue function))) :=
  consumerValid (.pure (forceValue function)) trivial
    (converted_valid input output body incoming function functionValid)

end Yulang.ArgumentEffectCastRuntime
