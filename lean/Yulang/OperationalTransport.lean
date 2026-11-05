import Yulang.DirectedHigherOrder
import Yulang.OperationalTyping

/-!
# Higher-order boundary transport of the actual operational values

These wrappers act on `OperationalTyping.Value` and `OperationalTyping.Tree`.
In particular, a function receives a suspended computation, whose requests and
returned value are both transported in the opposite direction before the call.
The result is transported in the original direction. Products recurse into their
stored values, so a returned callback is wrapped without being executed.

The signed request action is the existing one from `DirectedHigherOrder`, with
the same boundary and permission mask in each inverse pair. Both roundtrips hold
for every finite resolved shape and every runtime value or request tree, without
freshness, an origin condition, a weight bound, or a computation fuel bound.

No syntax or evaluator is changed here. These are explicit runtime wrappers for
the already resolved fragment. Their insertion by source elaboration and the
separate origin condition needed for noncapture are not asserted by inversion.
-/

namespace Yulang.OperationalTransport

open Directed
open OperationalTyping (Shape Value Tree AllReturns)
open DirectedHigherOrder (mapBoth)

abbrev Direction := HigherOrder.Direction

def request (scope : Fin n) (permission : Key → Bool) (direction : Direction) :
    Occurrence n Key → Occurrence n Key :=
  DirectedHigherOrder.requestTransport scope permission direction

@[simp] theorem request_opposite (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (occurrence : Occurrence n Key) :
    request scope permission direction.opposite
      (request scope permission direction occurrence) = occurrence :=
  DirectedHigherOrder.requestTransport_opposite scope permission direction occurrence

/-- Function inputs are computations, so the contravariant wrapper transforms
both their immediate requests and any values they eventually return. -/
def value (scope : Fin n) (permission : Key → Bool) : (shape : Shape) → Direction →
    Value n Key Atom shape → Value n Key Atom shape
  | .atom, _, atom => atom
  | .pair left right, direction, pair =>
      (value scope permission left direction pair.1,
        value scope permission right direction pair.2)
  | .arrow domain codomain, direction, function => fun argument =>
      mapBoth (request scope permission direction)
        (value scope permission codomain direction)
        (function (mapBoth (request scope permission direction.opposite)
          (value scope permission domain direction.opposite) argument))

/-- Transport immediate effects and latent values together. -/
def tree (scope : Fin n) (permission : Key → Bool) (shape : Shape) (direction : Direction)
    (computation : Tree n Key Atom shape) : Tree n Key Atom shape :=
  mapBoth (request scope permission direction) (value scope permission shape direction) computation

@[simp] theorem value_atom (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (atom : Atom) :
    value scope permission .atom direction atom = atom := rfl

@[simp] theorem value_pair (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (left : Value n Key Atom a) (right : Value n Key Atom b) :
    value scope permission (.pair a b) direction (left, right) =
      (value scope permission a direction left, value scope permission b direction right) := rfl

theorem value_arrow (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (function : Value n Key Atom (.arrow a b))
    (argument : Tree n Key Atom a) :
    value scope permission (.arrow a b) direction function argument =
      tree scope permission b direction
        (function (tree scope permission a direction.opposite argument)) := rfl

@[simp] theorem tree_pure (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (returned : Value n Key Atom shape) :
    tree scope permission shape direction (.pure returned) =
      .pure (value scope permission shape direction returned) := rfl

@[simp] theorem tree_request (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (occurrence : Occurrence n Key) (payload : Atom)
    (resume : Atom → Tree n Key Atom shape) :
    tree scope permission shape direction (.request occurrence payload resume) =
      .request (request scope permission direction occurrence) payload
        (fun response => tree scope permission shape direction (resume response)) := rfl

/-- The actual computation-argument closures have two-sided inverse wrappers. -/
@[simp] theorem value_opposite (scope : Fin n) (permission : Key → Bool) (shape : Shape) :
    ∀ (direction : Direction) (original : Value n Key Atom shape),
      value scope permission shape direction.opposite
        (value scope permission shape direction original) = original := by
  induction shape with
  | atom => intro direction original; rfl
  | pair left right ihLeft ihRight =>
      intro direction original
      exact Prod.ext (ihLeft direction original.1) (ihRight direction original.2)
  | arrow domain codomain ihDomain ihCodomain =>
      intro direction function
      funext argument
      simp only [value, HigherOrder.Direction.opposite_opposite]
      have argumentInverse := DirectedHigherOrder.mapBoth_inverse
        (request scope permission direction)
        (request scope permission direction.opposite)
        (value scope permission domain direction)
        (value scope permission domain direction.opposite)
        (request_opposite scope permission direction) (ihDomain direction) argument
      rw [argumentInverse]
      exact DirectedHigherOrder.mapBoth_inverse
        (request scope permission direction)
        (request scope permission direction.opposite)
        (value scope permission codomain direction)
        (value scope permission codomain direction.opposite)
        (request_opposite scope permission direction) (ihCodomain direction) (function argument)

@[simp] theorem tree_opposite (scope : Fin n) (permission : Key → Bool)
    (shape : Shape) (direction : Direction) (computation : Tree n Key Atom shape) :
    tree scope permission shape direction.opposite
      (tree scope permission shape direction computation) = computation :=
  DirectedHigherOrder.mapBoth_inverse _ _ _ _ (request_opposite scope permission direction)
    (value_opposite scope permission shape direction) computation

/-- A wrapped function applied to an equally wrapped computation is exactly
the wrapped original call. The argument need not be a pure value. -/
theorem value_apply_tree (scope : Fin n) (permission : Key → Bool)
    (direction : Direction) (function : Value n Key Atom (.arrow a b))
    (argument : Tree n Key Atom a) :
    value scope permission (.arrow a b) direction function
      (tree scope permission a direction argument) =
        tree scope permission b direction (function argument) := by
  rw [value_arrow, tree_opposite]

/-- Request predicates are affected only by the request action; latent value
wrapping does not execute a returned callback. -/
theorem allRequests_mapBoth (onRequest : Occurrence n Key → Occurrence n Key)
    (onValue : A → B) (predicate : Occurrence n Key → Prop)
    (computation : Computation n Key Payload Response A) :
    Computation.AllRequests predicate (mapBoth onRequest onValue computation) ↔
      Computation.AllRequests (fun occurrence => predicate (onRequest occurrence)) computation := by
  induction computation with
  | pure returned => rfl
  | request occurrence payload resume ih =>
      simp only [mapBoth, Computation.AllRequests, ih]

theorem allReturns_mapBoth (onRequest : Occurrence n Key → Occurrence n Key)
    (onValue : A → B) (predicate : B → Prop)
    (computation : Computation n Key Payload Response A) :
    AllReturns predicate (mapBoth onRequest onValue computation) ↔
      AllReturns (fun returned => predicate (onValue returned)) computation := by
  induction computation with
  | pure returned => rfl
  | request occurrence payload resume ih =>
      simp only [mapBoth, AllReturns, ih]

/-- General sequencing law before choosing a type-shaped value action. -/
theorem mapBoth_bind (onRequest : Occurrence n Key → Occurrence n Key)
    (onValue : B → C) (computation : Computation n Key Payload Response A)
    (next : A → Computation n Key Payload Response B) :
    mapBoth onRequest onValue (computation.bind next) =
      (Computation.mapRequests onRequest computation).bind
        (fun returned => mapBoth onRequest onValue (next returned)) := by
  induction computation with
  | pure returned => rfl
  | request occurrence payload resume ih =>
      simp only [Computation.bind, Computation.mapRequests, mapBoth]
      exact congrArg (Computation.request (onRequest occurrence) payload) (funext ih)

/-- Conjugating sequencing converts the intermediate value back before passing
it to the original continuation, including when that value is a closure. -/
theorem tree_bind (scope : Fin n) (permission : Key → Bool) (direction : Direction)
    (computation : Tree n Key Atom a) (next : Value n Key Atom a → Tree n Key Atom b) :
    tree scope permission b direction (computation.bind next) =
      (tree scope permission a direction computation).bind
        (fun returned => tree scope permission b direction
          (next (value scope permission a direction.opposite returned))) := by
  induction computation with
  | pure returned =>
      simp only [Computation.bind, tree_pure, value_opposite]
  | request occurrence payload resume ih =>
      simp only [Computation.bind, tree_request]
      exact congrArg (Computation.request (request scope permission direction occurrence) payload)
        (funext ih)

end Yulang.OperationalTransport
