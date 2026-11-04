import Yulang.Effects

/-!
# Type-directed transport of stored callbacks

`Computation.mapRequests` protects requests that are already in a computation
tree; it does not reach a closure returned as a pure value. This module gives
an explicit type-directed boundary wrapper for finite shapes. Products model
resolved record fields, sums model resolved variants, and lists may contain
callbacks. At an arrow, arguments cross in the opposite direction; results
and their requests cross in the original direction.

`guard_arrow_noncapture` is quantified over every function, input, and inner
handler: the guarded call cannot invoke that handler's operation arms. The
data projection and membership lemmas show that extracting a stored callback
does not discard its wrapper. Protection uses the default `allowNone` policy.

Scope: finite type shapes (not recursive types), well-founded computations,
and the given boundary operation. There is no source elaboration theorem,
operation-signature type-safety theorem, or selective-annotation inference.
Operation payloads remain an opaque carrier; only the typed value shapes are
traversed here; an `atom` is opaque too. `releaseValue` is the opposite-direction wrapper, not an
unconditional inverse: a compiler must still justify scope ownership and
freshness when inserting a release. Existing barrier multiplicities remain
intact. In particular, an erase-style release does not record negative debt;
guard after release need not cancel on a fresh request. The wrapper's safety
theorem is not a semantics-preserving translation theorem for arbitrary
mixed-provenance higher-order arguments. Sources: spec/05-effects.md §5.4,
spec/07-display.md §7.3.
-/

namespace Yulang.HigherOrder

open Effects

inductive Shape where
  | atom
  | product (left right : Shape)
  | sum (left right : Shape)
  | list (element : Shape)
  | arrow (domain codomain : Shape)
  deriving DecidableEq, Repr

/-- The finite type shape determines where latent computations can be stored. -/
@[reducible] def Value (Key Payload Response Atom : Type u) : Shape → Type u
  | .atom => Atom
  | .product left right => Value Key Payload Response Atom left ×
      Value Key Payload Response Atom right
  | .sum left right => Sum (Value Key Payload Response Atom left)
      (Value Key Payload Response Atom right)
  | .list element => List (Value Key Payload Response Atom element)
  | .arrow domain codomain => Value Key Payload Response Atom domain →
      Computation Key Payload Response (Value Key Payload Response Atom codomain)

inductive Direction where
  | guard
  | release
  deriving DecidableEq, Repr

def Direction.opposite : Direction → Direction
  | .guard => .release
  | .release => .guard

@[simp] theorem Direction.opposite_opposite (direction : Direction) :
    direction.opposite.opposite = direction := by cases direction <;> rfl

def requestTransport (scope : Nat) : Direction → Occurrence Key → Occurrence Key
  | .guard => protectOccurrence scope allowNone
  | .release => releaseOccurrence scope

/-- Mapping a pure result introduces no requests and does not execute callbacks. -/
def mapValues (f : First → Second)
    (computation : Computation Key Payload Response First) :
    Computation Key Payload Response Second :=
  computation.bind (fun value => .pure (f value))

variable {Key Payload Response Atom : Type u}

/-- Contravariant transport on arrow arguments; covariant transport everywhere
else. Recursive calls are on strict subshapes, including under `List.map`. -/
def transport (scope : Nat) : (shape : Shape) → Direction →
    Value Key Payload Response Atom shape → Value Key Payload Response Atom shape
  | .atom, _, value => value
  | .product left right, direction, value =>
      (transport scope left direction value.1, transport scope right direction value.2)
  | .sum left _, direction, .inl value => .inl (transport scope left direction value)
  | .sum _ right, direction, .inr value => .inr (transport scope right direction value)
  | .list element, direction, values => values.map (transport scope element direction)
  | .arrow domain codomain, direction, function => fun argument =>
      (mapValues (transport scope codomain direction)
        (function (transport scope domain direction.opposite argument))).mapRequests
          (requestTransport scope direction)

def guardValue (scope : Nat) (shape : Shape)
    (value : Value Key Payload Response Atom shape) : Value Key Payload Response Atom shape :=
  transport scope shape .guard value

def releaseValue (scope : Nat) (shape : Shape)
    (value : Value Key Payload Response Atom shape) : Value Key Payload Response Atom shape :=
  transport scope shape .release value

theorem guard_arrow (scope : Nat) (domain codomain : Shape)
    (function : Value Key Payload Response Atom (.arrow domain codomain))
    (argument : Value Key Payload Response Atom domain) :
    guardValue scope (.arrow domain codomain) function argument =
      (mapValues (guardValue scope codomain)
        (function (releaseValue scope domain argument))).mapRequests
          (protectOccurrence scope allowNone) := rfl

theorem release_arrow (scope : Nat) (domain codomain : Shape)
    (function : Value Key Payload Response Atom (.arrow domain codomain))
    (argument : Value Key Payload Response Atom domain) :
    releaseValue scope (.arrow domain codomain) function argument =
      (mapValues (releaseValue scope codomain)
        (function (guardValue scope domain argument))).mapRequests
          (releaseOccurrence scope) := rfl

/-- No operation arm of the inner handler can receive a guarded call's requests.
This includes requests emitted after any number of resumptions. -/
theorem guard_arrow_noncapture [DecidableEq Key]
    (scope : Nat) (domain codomain : Shape)
    (function : Value Key Payload Response Atom (.arrow domain codomain))
    (argument : Value Key Payload Response Atom domain)
    (handled : List Key)
    (onReturn : Value Key Payload Response Atom codomain →
      Computation Key Payload Response Result)
    (onOperation : Occurrence Key → Payload →
      (Response → Computation Key Payload Response (Value Key Payload Response Atom codomain)) →
        Computation Key Payload Response Result) :
    Computation.shallowHandle handled onReturn onOperation
      (guardValue scope (.arrow domain codomain) function argument) =
        (guardValue scope (.arrow domain codomain) function argument).bind onReturn := by
  exact Computation.default_boundary_operational_noncapture handled scope onReturn onOperation
    (mapValues (guardValue scope codomain) (function (releaseValue scope domain argument)))

/-- Taking a resolved record/product field preserves the guard on its stored value. -/
theorem guard_product_fst (scope : Nat) (left right : Shape)
    (value : Value Key Payload Response Atom (.product left right)) :
    (guardValue scope (.product left right) value).1 = guardValue scope left value.1 := rfl

theorem guard_product_snd (scope : Nat) (left right : Shape)
    (value : Value Key Payload Response Atom (.product left right)) :
    (guardValue scope (.product left right) value).2 = guardValue scope right value.2 := rfl

/-- A resolved variant keeps the boundary wrapper on its payload. -/
theorem guard_sum_inl (scope : Nat) (left right : Shape)
    (value : Value Key Payload Response Atom left) :
    guardValue scope (.sum left right) (.inl value) =
      Sum.inl (guardValue scope left value) := rfl

theorem guard_sum_inr (scope : Nat) (left right : Shape)
    (value : Value Key Payload Response Atom right) :
    guardValue scope (.sum left right) (.inr value) =
      Sum.inr (guardValue scope right value) := rfl

/-- Every callback obtained from a transported list has been transported too. -/
theorem mem_guard_list (scope : Nat) (element : Shape)
    (values : Value Key Payload Response Atom (.list element))
    (value : Value Key Payload Response Atom element) :
    value ∈ guardValue scope (.list element) values ↔
      ∃ original ∈ values, guardValue scope element original = value := by
  exact List.mem_map

theorem guard_list_length (scope : Nat) (element : Shape)
    (values : Value Key Payload Response Atom (.list element)) :
    (guardValue scope (.list element) values).length = values.length := by
  exact List.length_map _

/-- The list theorem gives noncapture for any extracted function, not just a
fixed index or a closed regression example. -/
theorem list_callback_noncapture [DecidableEq Key]
    (scope : Nat) (domain codomain : Shape)
    (functions : Value Key Payload Response Atom (.list (.arrow domain codomain)))
    (function : Value Key Payload Response Atom (.arrow domain codomain))
    (member : function ∈ guardValue scope (.list (.arrow domain codomain)) functions)
    (argument : Value Key Payload Response Atom domain)
    (handled : List Key)
    (onReturn : Value Key Payload Response Atom codomain →
      Computation Key Payload Response Result)
    (onOperation : Occurrence Key → Payload →
      (Response → Computation Key Payload Response (Value Key Payload Response Atom codomain)) →
        Computation Key Payload Response Result) :
    Computation.shallowHandle handled onReturn onOperation (function argument) =
      (function argument).bind onReturn := by
  obtain ⟨original, _, rfl⟩ := (mem_guard_list scope (.arrow domain codomain) functions function).mp member
  exact guard_arrow_noncapture scope domain codomain original argument handled onReturn onOperation

namespace Examples

abbrev Callback := Value Nat Nat Unit Nat (.arrow .atom .atom)
abbrev Program := Computation Nat Nat Unit Nat

def callback : Callback := fun _ => .request ⟨0, []⟩ 7 (fun _ => .pure 11)

def handle (computation : Program) : Program :=
  computation.shallowHandle [0] .pure (fun _ payload _ => .pure payload)

def stored : Computation Nat Nat Unit Callback := .pure callback

/-- Traversing only the pure computation's requests does not reach its closure. -/
def shallowProtection : Program :=
  handle ((stored.mapRequests (protectOccurrence 5 allowNone)).bind (fun f => f 0))

theorem shallowProtection_captures_callback : shallowProtection = .pure 7 := rfl

/-- Traverse the value's shape before the consumer extracts and calls the closure. -/
def typedProtection : Program :=
  handle ((mapValues (guardValue 5 (.arrow .atom .atom)) stored).bind (fun f => f 0))

theorem typedProtection_preserves_request :
    typedProtection = .request ⟨0, [5]⟩ 7 (fun _ => .pure 11) := rfl

/-- The request is preserved for the outer scope, rather than discarded. -/
theorem typedProtection_reaches_outer_handler :
    handle (typedProtection.mapRequests (releaseOccurrence 5)) = .pure 7 := rfl

theorem value_wrapping_changes_capture : typedProtection ≠ shallowProtection := by
  rw [typedProtection_preserves_request, shallowProtection_captures_callback]
  intro impossible
  cases impossible

def storedInRecord : Value Nat Nat Unit Nat (.product .atom (.arrow .atom .atom)) :=
  (23, callback)

theorem record_callback_is_guarded :
    handle ((guardValue 5 (.product .atom (.arrow .atom .atom)) storedInRecord).2 0) =
      .request ⟨0, [5]⟩ 7 (fun _ => .pure 11) := rfl

def storedInList : Value Nat Nat Unit Nat (.list (.arrow .atom .atom)) := [callback]

theorem list_stores_guarded_callback :
    guardValue 5 (.list (.arrow .atom .atom)) storedInList =
      [guardValue 5 (.arrow .atom .atom) callback] := rfl

/-- Repeated boundary activations remain distinct layers. -/
theorem repeated_guard_keeps_both_layers :
    guardValue 5 (.arrow .atom .atom)
      (guardValue 5 (.arrow .atom .atom) callback) 0 =
        .request ⟨0, [5, 5]⟩ 7 (fun _ => .pure 11) := rfl

theorem release_removes_one_layer :
    releaseValue 5 (.arrow .atom .atom)
      (guardValue 5 (.arrow .atom .atom)
        (guardValue 5 (.arrow .atom .atom) callback)) 0 =
          .request ⟨0, [5]⟩ 7 (fun _ => .pure 11) := rfl

/-- Release carries no negative debt. Even though arrow arguments reverse
direction, a source elaborator cannot infer arbitrary roundtrip cancellation. -/
theorem guard_after_release_of_fresh_callback :
    guardValue 5 (.arrow .atom .atom)
      (releaseValue 5 (.arrow .atom .atom) callback) 0 =
        .request ⟨0, [5]⟩ 7 (fun _ => .pure 11) := rfl

theorem fresh_roundtrip_is_not_symmetric :
    guardValue 5 (.arrow .atom .atom)
      (releaseValue 5 (.arrow .atom .atom) callback) 0 ≠ callback 0 := by
  rw [guard_after_release_of_fresh_callback]
  intro impossible
  cases impossible

end Examples

#print axioms guard_arrow_noncapture
#print axioms mem_guard_list
#print axioms list_callback_noncapture
#print axioms Examples.value_wrapping_changes_capture
#print axioms Examples.release_removes_one_layer
#print axioms Examples.fresh_roundtrip_is_not_symmetric

end Yulang.HigherOrder
