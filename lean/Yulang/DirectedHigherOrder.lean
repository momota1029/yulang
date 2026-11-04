import Yulang.Directed
import Yulang.HigherOrder

/-!
# Invertible transport of higher-order values

The erase-based experiment in `Yulang.HigherOrder` proves noncapture but exposes
an asymmetric roundtrip: releasing a fresh request loses the negative debt.
This module uses `Directed`'s signed, per-scope weights instead. Both transport
roundtrips are identities, including at arrows, whose argument direction is
reversed. The same permission mask is used for the paired shifts.

Noncapture is a separate property with an explicit zero-origin premise. A
positive shift can cancel an existing negative weight, so guarding arbitrary
signed requests is not uniformly noncapturing. The mixed-origin callback
example below uses that cancellation to restore a local callback's visibility
after shielding it inside an incoming higher-order function.

The shapes are finite and resolved: products, sums, lists, atoms and arrows.
Atoms and operation payloads remain opaque. These are value-transport theorems,
not a source elaboration, recursive-type, dependent operation-signature, or
whole-language preservation/progress theorem. Source insertion of boundary
transports and the origin invariant still require their own proof.
-/

namespace Yulang.DirectedHigherOrder

open Directed

abbrev Shape := HigherOrder.Shape
abbrev Direction := HigherOrder.Direction

@[reducible] def Value (n : Nat) (Key Payload Response Atom : Type u) : Shape → Type u
  | .atom => Atom
  | .product left right => Value n Key Payload Response Atom left ×
      Value n Key Payload Response Atom right
  | .sum left right => Sum (Value n Key Payload Response Atom left)
      (Value n Key Payload Response Atom right)
  | .list element => List (Value n Key Payload Response Atom element)
  | .arrow domain codomain => Value n Key Payload Response Atom domain →
      Computation n Key Payload Response (Value n Key Payload Response Atom codomain)

def denyAll : Key → Bool := fun _ => false

def requestTransport (scope : Fin n) (permission : Key → Bool) :
    Direction → Occurrence n Key → Occurrence n Key
  | .guard => Directed.protect scope permission
  | .release => Directed.release scope permission

theorem requestTransport_opposite (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (occurrence : Occurrence n Key) :
    requestTransport scope permission direction.opposite
      (requestTransport scope permission direction occurrence) = occurrence := by
  cases direction with
  | guard => exact Directed.release_protect scope permission occurrence
  | release => exact Directed.protect_release scope permission occurrence

/-- Transform requests and returned values without executing a returned closure. -/
def mapBoth (onRequest : Occurrence n Key → Occurrence n Key) (onValue : First → Second) :
    Computation n Key Payload Response First → Computation n Key Payload Response Second
  | .pure value => .pure (onValue value)
  | .request occurrence payload resume =>
      .request (onRequest occurrence) payload (fun response =>
        mapBoth onRequest onValue (resume response))

theorem mapBoth_comp (firstRequest secondRequest : Occurrence n Key → Occurrence n Key)
    (firstValue : First → Second) (secondValue : Second → Third)
    (computation : Computation n Key Payload Response First) :
    mapBoth secondRequest secondValue (mapBoth firstRequest firstValue computation) =
      mapBoth (fun occurrence => secondRequest (firstRequest occurrence))
        (fun value => secondValue (firstValue value)) computation := by
  induction computation with
  | pure value => rfl
  | request occurrence payload resume ih =>
      simp only [mapBoth]
      exact congrArg (Computation.request (secondRequest (firstRequest occurrence)) payload)
        (funext ih)

theorem mapBoth_identity (computation : Computation n Key Payload Response First) :
    mapBoth id id computation = computation := by
  induction computation with
  | pure value => rfl
  | request occurrence payload resume ih =>
      simp only [mapBoth, id_eq]
      exact congrArg (Computation.request occurrence payload) (funext ih)

theorem mapBoth_inverse (firstRequest secondRequest : Occurrence n Key → Occurrence n Key)
    (firstValue : First → Second) (secondValue : Second → First)
    (requestInverse : ∀ occurrence, secondRequest (firstRequest occurrence) = occurrence)
    (valueInverse : ∀ value, secondValue (firstValue value) = value)
    (computation : Computation n Key Payload Response First) :
    mapBoth secondRequest secondValue (mapBoth firstRequest firstValue computation) =
      computation := by
  rw [mapBoth_comp]
  have hr : (fun occurrence => secondRequest (firstRequest occurrence)) = id :=
    funext requestInverse
  have hv : (fun value => secondValue (firstValue value)) = id := funext valueInverse
  rw [hr, hv]
  exact mapBoth_identity computation

variable {Key Payload Response Atom : Type u}

/-- Both directions use the same permission mask; arrow arguments reverse the
direction, while the request tree and returned values preserve it. -/
def transport (scope : Fin n) (permission : Key → Bool) : (shape : Shape) → Direction →
    Value n Key Payload Response Atom shape → Value n Key Payload Response Atom shape
  | .atom, _, value => value
  | .product left right, direction, value =>
      (transport scope permission left direction value.1,
        transport scope permission right direction value.2)
  | .sum left _, direction, .inl value =>
      .inl (transport scope permission left direction value)
  | .sum _ right, direction, .inr value =>
      .inr (transport scope permission right direction value)
  | .list element, direction, values =>
      values.map (transport scope permission element direction)
  | .arrow domain codomain, direction, function => fun argument =>
      mapBoth (requestTransport scope permission direction)
        (transport scope permission codomain direction)
        (function (transport scope permission domain direction.opposite argument))

def guardValue (scope : Fin n) (permission : Key → Bool) (shape : Shape)
    (value : Value n Key Payload Response Atom shape) : Value n Key Payload Response Atom shape :=
  transport scope permission shape .guard value

def releaseValue (scope : Fin n) (permission : Key → Bool) (shape : Shape)
    (value : Value n Key Payload Response Atom shape) : Value n Key Payload Response Atom shape :=
  transport scope permission shape .release value

/-- Two-sided inverse, uniformly over all finite shapes and all values. No
freshness, bound on weights, or computation fuel appears in this theorem. -/
theorem transport_opposite (scope : Fin n) (permission : Key → Bool) (shape : Shape) :
    ∀ (direction : Direction) (value : Value n Key Payload Response Atom shape),
      transport scope permission shape direction.opposite
        (transport scope permission shape direction value) = value := by
  induction shape with
  | atom => intro direction value; rfl
  | product left right ihLeft ihRight =>
      intro direction value
      exact Prod.ext (ihLeft direction value.1) (ihRight direction value.2)
  | sum left right ihLeft ihRight =>
      intro direction value
      cases value with
      | inl value => exact congrArg Sum.inl (ihLeft direction value)
      | inr value => exact congrArg Sum.inr (ihRight direction value)
  | list element ih =>
      intro direction values
      simp only [transport, List.map_map]
      apply List.map_id''
      exact ih direction
  | arrow domain codomain ihDomain ihCodomain =>
      intro direction function
      funext argument
      simp only [transport, HigherOrder.Direction.opposite_opposite]
      rw [ihDomain direction argument]
      exact mapBoth_inverse
        (requestTransport scope permission direction)
        (requestTransport scope permission direction.opposite)
        (transport scope permission codomain direction)
        (transport scope permission codomain direction.opposite)
        (requestTransport_opposite scope permission direction)
        (ihCodomain direction) (function argument)

theorem release_guard (scope : Fin n) (permission : Key → Bool) (shape : Shape)
    (value : Value n Key Payload Response Atom shape) :
    releaseValue scope permission shape (guardValue scope permission shape value) = value :=
  transport_opposite scope permission shape .guard value

theorem guard_release (scope : Fin n) (permission : Key → Bool) (shape : Shape)
    (value : Value n Key Payload Response Atom shape) :
    guardValue scope permission shape (releaseValue scope permission shape value) = value :=
  transport_opposite scope permission shape .release value

/-- Guarding zero-origin requests prevents capture; negative-origin requests
are deliberately outside this premise because their debt can cancel the shift. -/
theorem guarded_map_noncapture [DecidableEq Key]
    (scope : Fin n) (onValue : First → Second)
    (computation : Computation n Key Payload Response First)
    (origin : Computation.ZeroAt scope computation)
    (handled : List Key)
    (onReturn : Second → Computation n Key Payload Response Result)
    (onOperation : Occurrence n Key → Payload →
      (Response → Computation n Key Payload Response Second) →
        Computation n Key Payload Response Result) :
    Computation.shallowHandle handled onReturn onOperation
      (mapBoth (Directed.protect scope denyAll) onValue computation) =
        (mapBoth (Directed.protect scope denyAll) onValue computation).bind onReturn := by
  induction computation with
  | pure value => rfl
  | request occurrence payload resume ih =>
      change occurrence.weights scope = 0 ∧
        (∀ response, Computation.ZeroAt scope (resume response)) at origin
      obtain ⟨here, later⟩ := origin
      have blocked := Directed.protected_not_capturable handled scope denyAll occurrence rfl here
      simp only [mapBoth, Computation.shallowHandle, blocked, ↓reduceIte, Computation.bind]
      exact congrArg (Computation.request (Directed.protect scope denyAll occurrence) payload)
        (funext (fun response => ih response (later response)))

theorem guard_arrow_noncapture [DecidableEq Key]
    (scope : Fin n) (domain codomain : Shape)
    (function : Value n Key Payload Response Atom (.arrow domain codomain))
    (argument : Value n Key Payload Response Atom domain)
    (origin : Computation.ZeroAt scope
      (function (releaseValue scope denyAll domain argument)))
    (handled : List Key)
    (onReturn : Value n Key Payload Response Atom codomain →
      Computation n Key Payload Response Result)
    (onOperation : Occurrence n Key → Payload →
      (Response → Computation n Key Payload Response (Value n Key Payload Response Atom codomain)) →
        Computation n Key Payload Response Result) :
    Computation.shallowHandle handled onReturn onOperation
      (guardValue scope denyAll (.arrow domain codomain) function argument) =
        (guardValue scope denyAll (.arrow domain codomain) function argument).bind onReturn :=
  guarded_map_noncapture scope (guardValue scope denyAll codomain)
    (function (releaseValue scope denyAll domain argument)) origin handled onReturn onOperation

theorem guard_product_snd (scope : Fin n) (permission : Key → Bool) (left right : Shape)
    (value : Value n Key Payload Response Atom (.product left right)) :
    (guardValue scope permission (.product left right) value).2 =
      guardValue scope permission right value.2 := rfl

theorem mem_guard_list (scope : Fin n) (permission : Key → Bool) (element : Shape)
    (values : Value n Key Payload Response Atom (.list element))
    (value : Value n Key Payload Response Atom element) :
    value ∈ guardValue scope permission (.list element) values ↔
      ∃ original ∈ values, guardValue scope permission element original = value :=
  List.mem_map

namespace Examples

def boundary : Fin 1 := 0
abbrev Callback := Value 1 Nat Nat Unit Nat (.arrow .atom .atom)
abbrev Invoker := Value 1 Nat Nat Unit Nat (.arrow (.arrow .atom .atom) .atom)
abbrev Program := Computation 1 Nat Nat Unit Nat

def visible : Occurrence 1 Nat := ⟨0, fun _ => 0⟩

def callback : Callback := fun _ => .request visible 7 (fun _ => .pure 11)

def innerHandler (computation : Program) : Program :=
  computation.shallowHandle [0] .pure (fun _ _ _ => .pure 99)

def outerHandler (computation : Program) : Program :=
  computation.shallowHandle [0] .pure (fun _ payload _ => .pure payload)

def invoker : Invoker := fun f => innerHandler (f 0)

/-- The untransported higher-order function intercepts the local callback. -/
theorem untransported_invoker_captures : outerHandler (invoker callback) = .pure 99 := by
  rfl

/-- Contravariant -1 shields the local callback inside invoker, then outgoing
+1 restores its visibility to the local outer handler. -/
theorem contravariant_debt_preserves_local_callback :
    outerHandler
      (guardValue boundary denyAll (.arrow (.arrow .atom .atom) .atom) invoker callback) =
        .pure 7 := by
  rfl

/-- The fresh-request asymmetry of the erase-based model is absent here. -/
theorem fresh_callback_roundtrip :
    guardValue boundary denyAll (.arrow .atom .atom)
      (releaseValue boundary denyAll (.arrow .atom .atom) callback) = callback :=
  guard_release boundary denyAll (.arrow .atom .atom) callback

theorem list_roundtrip :
    releaseValue boundary denyAll (.list (.arrow .atom .atom))
      (guardValue boundary denyAll (.list (.arrow .atom .atom)) [callback]) = [callback] :=
  release_guard boundary denyAll (.list (.arrow .atom .atom)) [callback]

end Examples

#print axioms transport_opposite
#print axioms release_guard
#print axioms guard_release
#print axioms guarded_map_noncapture
#print axioms guard_arrow_noncapture
#print axioms Examples.contravariant_debt_preserves_local_callback

end Yulang.DirectedHigherOrder
