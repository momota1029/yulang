import Yulang.Directed

/-!
# Operational effect bounds for signed occurrences

`Computation.BoundedBy` requires every request in a computation and all of its
continuations to occur in a finite signed row. The shallow-handler theorem uses
the actual `Directed.Capturable` predicate: every boundary coordinate must be
zero. Its operation-arm premise retains the original input row on resumptions;
arm effects are added after subtraction.

These are conditional bounds for the signed computation kernel. The action and
arms must supply their bounds; this file does not prove source evaluation or
preservation, resolve operation signatures, or traverse latent values or payloads.
Request-map transport preserves bounds for arbitrary signed weights. Unlike a
noncapture theorem, it needs no zero-origin premise.
-/

namespace Yulang.Directed.Computation

/-- Potential requests include every response branch of every continuation. -/
def BoundedBy (row : Row n Key)
    (computation : Computation n Key Payload Response Value) : Prop :=
  AllRequests (fun occurrence => occurrence ∈ row) computation

@[simp] theorem bounded_pure (row : Row n Key) (value : Value) :
    BoundedBy row (Computation.pure value : Computation n Key Payload Response Value) :=
  True.intro

theorem bounded_request_iff (row : Row n Key) (occurrence : Occurrence n Key)
    (payload : Payload) (resume : Response → Computation n Key Payload Response Value) :
    BoundedBy row (.request occurrence payload resume) ↔
      occurrence ∈ row ∧ ∀ response, BoundedBy row (resume response) := Iff.rfl

theorem allRequests_mono (left right : Occurrence n Key → Prop)
    (implies : ∀ occurrence, left occurrence → right occurrence)
    (computation : Computation n Key Payload Response Value)
    (bound : AllRequests left computation) : AllRequests right computation := by
  induction computation with
  | pure _ => trivial
  | request occurrence payload resume ih =>
    exact ⟨implies occurrence bound.1, fun response => ih response (bound.2 response)⟩

theorem bounded_mono {left right : Row n Key}
    (subset : ∀ occurrence, occurrence ∈ left → occurrence ∈ right)
    {computation : Computation n Key Payload Response Value}
    (bound : BoundedBy left computation) : BoundedBy right computation :=
  allRequests_mono _ _ subset computation bound

theorem mapRequests_bounded (transform : Occurrence n Key → Occurrence n Other)
    (row : Row n Key) (computation : Computation n Key Payload Response Value)
    (bound : BoundedBy row computation) :
    BoundedBy (row.map transform) (mapRequests transform computation) := by
  apply (allRequests_map transform (fun occurrence => occurrence ∈ row.map transform)
    computation).mpr
  exact allRequests_mono _ _
    (fun occurrence member => List.mem_map.mpr ⟨occurrence, member, rfl⟩) computation bound

/-- Signed protection transports a bound exactly, even when it cancels debt. -/
theorem protect_bounded_iff (scope : Fin n) (permission : Permission Key)
    (row : Row n Key) (computation : Computation n Key Payload Response Value) :
    BoundedBy (row.map (Directed.protect scope permission))
      (mapRequests (Directed.protect scope permission) computation) ↔
        BoundedBy row computation := by
  constructor
  · intro bound
    have restored := mapRequests_bounded (Directed.release scope permission) _ _ bound
    simpa only [Directed.protect_row_release, release_protect] using restored
  · exact mapRequests_bounded _ _ _

/-- Matching signed release has the same exact bound-transport property. -/
theorem release_bounded_iff (scope : Fin n) (permission : Permission Key)
    (row : Row n Key) (computation : Computation n Key Payload Response Value) :
    BoundedBy (row.map (Directed.release scope permission))
      (mapRequests (Directed.release scope permission) computation) ↔
        BoundedBy row computation := by
  constructor
  · intro bound
    have restored := mapRequests_bounded (Directed.protect scope permission) _ _ bound
    simpa only [Directed.release_row_protect, protect_release] using restored
  · exact mapRequests_bounded _ _ _

private theorem mem_residual_iff [DecidableEq Key]
    (handled : List Key) (row : Row n Key) (occurrence : Occurrence n Key) :
    occurrence ∈ residual handled row ↔
      occurrence ∈ row ∧ ¬ Capturable handled occurrence := by
  simp [residual]

/--
Compositional operational bound for a signed shallow handler. The operation arm
receives the original continuation, bounded by `input`, not by its residual.
Requests emitted by either arm belong to `armEffects` outside subtraction.
-/
theorem shallowHandle_bounded [DecidableEq Key]
    (handled : List Key) (input armEffects : Row n Key)
    (onReturn : Value → Computation n Key Payload Response Result)
    (onOperation : Occurrence n Key → Payload →
      (Response → Computation n Key Payload Response Value) →
        Computation n Key Payload Response Result)
    (returnBound : ∀ value, BoundedBy armEffects (onReturn value))
    (operationBound : ∀ occurrence payload resume,
      Capturable handled occurrence →
      (∀ response, BoundedBy input (resume response)) →
        BoundedBy armEffects (onOperation occurrence payload resume))
    (computation : Computation n Key Payload Response Value)
    (inputBound : BoundedBy input computation) :
    BoundedBy (residual handled input ++ armEffects)
      (shallowHandle handled onReturn onOperation computation) := by
  induction computation with
  | pure value =>
    exact bounded_mono (fun _ member => List.mem_append.mpr (Or.inr member)) (returnBound value)
  | request occurrence payload resume ih =>
    rcases (bounded_request_iff input occurrence payload resume).mp inputBound with ⟨head, rest⟩
    by_cases captured : Capturable handled occurrence
    · simp only [shallowHandle, captured, ↓reduceIte]
      exact bounded_mono (fun _ member => List.mem_append.mpr (Or.inr member))
        (operationBound occurrence payload resume captured rest)
    · simp only [shallowHandle, captured, ↓reduceIte]
      apply (bounded_request_iff _ _ _ _).mpr
      exact ⟨List.mem_append.mpr (Or.inl ((mem_residual_iff _ _ _).mpr ⟨head, captured⟩)),
        fun response => ih response (rest response)⟩

namespace BoundExamples

private def scope : Fin 1 := ⟨0, by decide⟩
private abbrev Tree := Computation 1 Nat Unit Unit Unit

/-- A handler for key 0 forwards a request with negative boundary debt. -/
theorem negative_debt_is_forwarded :
    shallowHandle [0] (fun _ : Unit => (Computation.pure () : Tree))
      (fun _ _ _ => Computation.pure ())
      (.request (Directed.release scope allowNone (raw 0)) () (fun _ => .pure ())) =
        (.request (Directed.release scope allowNone (raw 0)) () (fun _ => .pure ()) : Tree) := by
  rfl

/-- A matching operation emitted by its own arm remains an outgoing request. -/
theorem reemitted_request_is_not_handled :
    shallowHandle [0] (fun _ : Unit => (Computation.pure () : Tree))
      (fun _ _ _ => .request (raw 0) () (fun _ => .pure ()))
      (.request (raw 0) () (fun _ => .pure ())) =
        (.request (raw 0) () (fun _ => .pure ()) : Tree) := by
  rfl

end BoundExamples
end Yulang.Directed.Computation
