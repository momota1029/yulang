import Yulang.DirectedBounds

/-!
# Fresh boundary allocation for signed effect occurrences

The entrypoint `liftTree` allocates one independent zero-weight coordinate.
`fresh_noncapture` proves that protecting it prevents capture by every inner
handler, while `liftTree_recover` recovers the complete original tree.

A boundary interface can be embedded into a larger one without changing any
existing signed weight. Unused target coordinates are initialized to zero.
The embedding preserves and reflects capture, commutes with residuals and
transport at existing scopes, and extends to every well-founded computation
tree. Thus allocating a fresh coordinate supplies the zero-origin premise of
`Directed.Computation.default_zero_boundary_noncapture`; the original tree may
contain arbitrary positive and negative weights at its existing coordinates.

The finite inverse lookup is executable. These are elaboration building blocks,
not a source elaborator or a proof that every source call allocates a fresh
scope. Returned values, payloads, and response carriers remain opaque here;
latent functions require their own type-directed treatment.
-/

namespace Yulang.FreshBoundaries

open Directed

/-- Find the old coordinate represented by a new one. Injectivity is required
by the preservation theorems, not by this terminating finite lookup. -/
def locate (embedding : Fin n → Fin m) (coordinate : Fin m) : Option (Fin n) :=
  (List.finRange n).find? (fun old => decide (embedding old = coordinate))

theorem locate_sound (embedding : Fin n → Fin m) (coordinate : Fin m) (old : Fin n)
    (found : locate embedding coordinate = some old) : embedding old = coordinate := by
  have selected : decide (embedding old = coordinate) = true :=
    List.find?_some (p := fun candidate => decide (embedding candidate = coordinate)) found
  exact of_decide_eq_true selected

theorem locate_none_iff (embedding : Fin n → Fin m) (coordinate : Fin m) :
    locate embedding coordinate = none ↔ ∀ old, embedding old ≠ coordinate := by
  simp [locate, List.find?_eq_none, List.mem_finRange]

theorem locate_image (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (old : Fin n) : locate embedding (embedding old) = some old := by
  cases found : locate embedding (embedding old) with
  | none => exact False.elim ((locate_none_iff embedding _).mp found old rfl)
  | some actual =>
      have equal : actual = old := injective (locate_sound embedding _ actual found)
      subst actual
      rfl

/-- Extend signed weights by zero outside the image of a coordinate map. -/
def reindex (embedding : Fin n → Fin m) (occurrence : Occurrence n Key) : Occurrence m Key :=
  { key := occurrence.key
    weights := fun coordinate =>
      match locate embedding coordinate with
      | none => 0
      | some old => occurrence.weights old }

@[simp] theorem reindex_key (embedding : Fin n → Fin m) (occurrence : Occurrence n Key) :
    (reindex embedding occurrence).key = occurrence.key := rfl

theorem reindex_image (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (occurrence : Occurrence n Key) (old : Fin n) :
    (reindex embedding occurrence).weights (embedding old) = occurrence.weights old := by
  simp [reindex, locate_image embedding injective]

theorem reindex_outside (embedding : Fin n → Fin m) (occurrence : Occurrence n Key)
    (coordinate : Fin m) (fresh : ∀ old, embedding old ≠ coordinate) :
    (reindex embedding occurrence).weights coordinate = 0 := by
  simp [reindex, (locate_none_iff embedding coordinate).mpr fresh]

/-- Restriction is a left inverse on embedded occurrences. It is not permission
to erase extra coordinates of an arbitrary target occurrence. -/
def restrict (embedding : Fin n → Fin m) (occurrence : Occurrence m Key) : Occurrence n Key :=
  ⟨occurrence.key, fun old => occurrence.weights (embedding old)⟩

theorem restrict_reindex (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (occurrence : Occurrence n Key) : restrict embedding (reindex embedding occurrence) = occurrence := by
  apply Occurrence.ext
  · rfl
  exact reindex_image embedding injective occurrence

theorem reindex_injective (embedding : Fin n → Fin m) (injective : Function.Injective embedding) :
    Function.Injective (reindex embedding (Key := Key)) := by
  intro left right equal
  have restored := congrArg (restrict embedding) equal
  simpa only [restrict_reindex embedding injective] using restored

theorem reindex_zero_iff (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (occurrence : Occurrence n Key) :
    (∀ coordinate, (reindex embedding occurrence).weights coordinate = 0) ↔
      ∀ old, occurrence.weights old = 0 := by
  constructor
  · intro zero old
    simpa only [reindex_image embedding injective] using zero (embedding old)
  · intro zero coordinate
    cases found : locate embedding coordinate with
    | none => simp [reindex, found]
    | some old => simp [reindex, found, zero old]

theorem capturable_reindex_iff (embedding : Fin n → Fin m)
    (injective : Function.Injective embedding) (handled : List Key) (occurrence : Occurrence n Key) :
    Capturable handled (reindex embedding occurrence) ↔ Capturable handled occurrence := by
  simp only [Capturable, reindex_key, reindex_zero_iff embedding injective]

theorem reindex_shift (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (scope : Fin n) (permission : Permission Key) (delta : Int) (occurrence : Occurrence n Key) :
    reindex embedding (shift scope permission delta occurrence) =
      shift (embedding scope) permission delta (reindex embedding occurrence) := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  cases found : locate embedding coordinate with
  | none =>
      have outside := (locate_none_iff embedding coordinate).mp found
      have different : coordinate ≠ embedding scope := fun equal => outside scope equal.symm
      simp [reindex, found, shift, different]
  | some old =>
      have equal := locate_sound embedding coordinate old found
      subst coordinate
      have same : (embedding old = embedding scope) ↔ old = scope :=
        ⟨fun equal => injective equal, fun equal => congrArg embedding equal⟩
      simp only [reindex_image embedding injective, shift, reindex_key, same]

theorem reindex_protect (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (scope : Fin n) (permission : Permission Key) (occurrence : Occurrence n Key) :
    reindex embedding (protect scope permission occurrence) =
      protect (embedding scope) permission (reindex embedding occurrence) :=
  reindex_shift embedding injective scope permission 1 occurrence

theorem reindex_release (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (scope : Fin n) (permission : Permission Key) (occurrence : Occurrence n Key) :
    reindex embedding (release scope permission occurrence) =
      release (embedding scope) permission (reindex embedding occurrence) :=
  reindex_shift embedding injective scope permission (-1) occurrence

theorem residual_reindex [DecidableEq Key] (embedding : Fin n → Fin m)
    (injective : Function.Injective embedding) (handled : List Key) (row : Row n Key) :
    residual handled (row.map (reindex embedding)) =
      (residual handled row).map (reindex embedding) := by
  simp only [residual, List.filter_map, Function.comp_def,
    capturable_reindex_iff embedding injective]

/-- Map requests between possibly different boundary interfaces. -/
def mapRequests (transform : Occurrence n Key → Occurrence m Other)
    (computation : Computation n Key Payload Response Value) :
    Computation m Other Payload Response Value :=
  match computation with
  | .pure value => .pure value
  | .request occurrence payload resume =>
      .request (transform occurrence) payload (fun response => mapRequests transform (resume response))

theorem mapRequests_identity (computation : Computation n Key Payload Response Value) :
    mapRequests id computation = computation := by
  induction computation with
  | pure _ => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request occurrence payload) (funext ih)

theorem mapRequests_comp (first : Occurrence n Key → Occurrence m Middle)
    (second : Occurrence m Middle → Occurrence k Other)
    (computation : Computation n Key Payload Response Value) :
    mapRequests second (mapRequests first computation) =
      mapRequests (second ∘ first) computation := by
  induction computation with
  | pure _ => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request (second (first occurrence)) payload) (funext ih)

theorem mapRequests_same (transform : Occurrence n Key → Occurrence n Other)
    (computation : Computation n Key Payload Response Value) :
    mapRequests transform computation = Computation.mapRequests transform computation := by
  induction computation with
  | pure _ => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request (transform occurrence) payload) (funext ih)

theorem mapRequests_bind (transform : Occurrence n Key → Occurrence m Other)
    (computation : Computation n Key Payload Response Value)
    (next : Value → Computation n Key Payload Response Result) :
    mapRequests transform (computation.bind next) =
      (mapRequests transform computation).bind (fun value => mapRequests transform (next value)) := by
  induction computation with
  | pure _ => rfl
  | request occurrence payload resume ih =>
      exact congrArg (Computation.request (transform occurrence) payload) (funext ih)

theorem allRequests_map (transform : Occurrence n Key → Occurrence m Other)
    (predicate : Occurrence m Other → Prop) (computation : Computation n Key Payload Response Value) :
    Computation.AllRequests predicate (mapRequests transform computation) ↔
      Computation.AllRequests (predicate ∘ transform) computation := by
  induction computation with
  | pure _ => rfl
  | request occurrence payload resume ih =>
      simp only [mapRequests, Computation.AllRequests, Function.comp_def, ih]

theorem mapRequests_inverse (first : Occurrence n Key → Occurrence m Other)
    (second : Occurrence m Other → Occurrence n Key)
    (inverse : ∀ occurrence, second (first occurrence) = occurrence)
    (computation : Computation n Key Payload Response Value) :
    mapRequests second (mapRequests first computation) = computation := by
  rw [mapRequests_comp]
  have identity : second ∘ first = id := funext inverse
  rw [identity, mapRequests_identity]

def reindexTree (embedding : Fin n → Fin m)
    (computation : Computation n Key Payload Response Value) :
    Computation m Key Payload Response Value := mapRequests (reindex embedding) computation

theorem reindexTree_recover (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (computation : Computation n Key Payload Response Value) :
    mapRequests (restrict embedding) (reindexTree embedding computation) = computation :=
  mapRequests_inverse _ _ (restrict_reindex embedding injective) computation

theorem reindexTree_zeroAt (embedding : Fin n → Fin m) (coordinate : Fin m)
    (fresh : ∀ old, embedding old ≠ coordinate)
    (computation : Computation n Key Payload Response Value) :
    Computation.ZeroAt coordinate (reindexTree embedding computation) := by
  induction computation with
  | pure _ => trivial
  | request occurrence payload resume ih =>
      exact ⟨reindex_outside embedding occurrence coordinate fresh, ih⟩

theorem reindexTree_bounded_iff (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (row : Row n Key) (computation : Computation n Key Payload Response Value) :
    Computation.BoundedBy (row.map (reindex embedding)) (reindexTree embedding computation) ↔
      Computation.BoundedBy row computation := by
  change Computation.AllRequests _ (mapRequests (reindex embedding) computation) ↔ _
  rw [allRequests_map]
  have predicate : (fun occurrence : Occurrence m Key => occurrence ∈ row.map (reindex embedding)) ∘
      reindex embedding = (fun occurrence => occurrence ∈ row) := by
    funext occurrence
    apply propext
    simp only [Function.comp_def, List.mem_map]
    constructor
    · rintro ⟨original, member, equal⟩
      exact (reindex_injective embedding injective equal) ▸ member
    · intro member
      exact ⟨occurrence, member, rfl⟩
  rw [predicate]
  rfl

theorem reindexTree_shift (embedding : Fin n → Fin m) (injective : Function.Injective embedding)
    (scope : Fin n) (permission : Permission Key) (delta : Int)
    (computation : Computation n Key Payload Response Value) :
    reindexTree embedding (Computation.mapRequests (shift scope permission delta) computation) =
      Computation.mapRequests (shift (embedding scope) permission delta)
        (reindexTree embedding computation) := by
  change mapRequests (reindex embedding) (Computation.mapRequests _ computation) =
    Computation.mapRequests _ (mapRequests (reindex embedding) computation)
  rw [← mapRequests_same, ← mapRequests_same, mapRequests_comp, mapRequests_comp]
  apply congrArg (fun transform => mapRequests transform computation)
  funext occurrence
  exact reindex_shift embedding injective scope permission delta occurrence

/-- Renaming all request occurrences and both arms preserves the actual shallow
handler. Restriction is used only on the image of the embedding, including the
unhandled continuation passed to an operation arm. -/
theorem reindexTree_shallowHandle [DecidableEq Key] (embedding : Fin n → Fin m)
    (injective : Function.Injective embedding) (handled : List Key)
    (onReturn : Value → Computation n Key Payload Response Result)
    (onOperation : Occurrence n Key → Payload →
      (Response → Computation n Key Payload Response Value) →
        Computation n Key Payload Response Result)
    (computation : Computation n Key Payload Response Value) :
    reindexTree embedding (Computation.shallowHandle handled onReturn onOperation computation) =
      Computation.shallowHandle handled (fun value => reindexTree embedding (onReturn value))
        (fun occurrence payload resume => reindexTree embedding
          (onOperation (restrict embedding occurrence) payload
            (fun response => mapRequests (restrict embedding) (resume response))))
        (reindexTree embedding computation) := by
  induction computation with
  | pure _ => rfl
  | request occurrence payload resume ih =>
      by_cases captured : Capturable handled occurrence
      · simp only [reindexTree, mapRequests, Computation.shallowHandle,
          capturable_reindex_iff embedding injective, captured, ↓reduceIte,
          restrict_reindex embedding injective]
        have restored : (fun response => mapRequests (restrict embedding)
            (mapRequests (reindex embedding) (resume response))) = resume :=
          funext (fun response => reindexTree_recover embedding injective (resume response))
        rw [restored]
      · simp only [reindexTree, mapRequests, Computation.shallowHandle,
          capturable_reindex_iff embedding injective, captured, ↓reduceIte]
        exact congrArg (Computation.request (reindex embedding occurrence) payload) (funext ih)

/-! ## One new coordinate, without discarding any old signed weight -/

def fresh : Fin (n + 1) := 0

theorem succ_injective : Function.Injective (@Fin.succ n) := by
  intro left right equal
  simpa using equal

def liftOccurrence (occurrence : Occurrence n Key) : Occurrence (n + 1) Key :=
  reindex Fin.succ occurrence

@[simp] theorem liftOccurrence_key (occurrence : Occurrence n Key) :
    (liftOccurrence occurrence).key = occurrence.key := rfl

@[simp] theorem liftOccurrence_old (occurrence : Occurrence n Key) (coordinate : Fin n) :
    (liftOccurrence occurrence).weights coordinate.succ = occurrence.weights coordinate :=
  reindex_image Fin.succ succ_injective occurrence coordinate

@[simp] theorem liftOccurrence_fresh (occurrence : Occurrence n Key) :
    (liftOccurrence occurrence).weights fresh = 0 :=
  reindex_outside Fin.succ occurrence fresh Fin.succ_ne_zero

theorem liftOccurrence_capture_iff (handled : List Key) (occurrence : Occurrence n Key) :
    Capturable handled (liftOccurrence occurrence) ↔ Capturable handled occurrence :=
  capturable_reindex_iff Fin.succ succ_injective handled occurrence

/-- Selective permission at a fresh scope reveals exactly the already-visible
occurrences whose keys it permits. Existing positive or negative barriers stay. -/
theorem fresh_protect_capture_iff (handled : List Key) (permission : Permission Key)
    (occurrence : Occurrence n Key) :
    Capturable handled (protect fresh permission (liftOccurrence occurrence)) ↔
      Capturable handled occurrence ∧ permission occurrence.key = true := by
  cases permitted : permission occurrence.key with
  | false =>
      have blocked : ¬ Capturable handled (protect fresh permission (liftOccurrence occurrence)) :=
        protected_not_capturable handled fresh permission (liftOccurrence occurrence)
          permitted (liftOccurrence_fresh occurrence)
      simp [blocked]
  | true =>
      have unchanged : protect fresh permission (liftOccurrence occurrence) = liftOccurrence occurrence := by
        apply Occurrence.ext
        · rfl
        intro coordinate
        simp [protect, shift, permitted]
      simp only [unchanged, liftOccurrence_capture_iff, and_true]

theorem fresh_release_capture_iff (handled : List Key) (permission : Permission Key)
    (occurrence : Occurrence n Key) :
    Capturable handled (release fresh permission (liftOccurrence occurrence)) ↔
      Capturable handled occurrence ∧ permission occurrence.key = true := by
  cases permitted : permission occurrence.key with
  | false =>
      have blocked : ¬ Capturable handled (release fresh permission (liftOccurrence occurrence)) :=
        negative_debt_not_capturable handled fresh permission (liftOccurrence occurrence)
          permitted (liftOccurrence_fresh occurrence)
      simp [blocked]
  | true =>
      have unchanged : release fresh permission (liftOccurrence occurrence) = liftOccurrence occurrence := by
        apply Occurrence.ext
        · rfl
        intro coordinate
        simp [release, shift, permitted]
      simp only [unchanged, liftOccurrence_capture_iff, and_true]

theorem fresh_protect_old (permission : Permission Key) (occurrence : Occurrence n Key)
    (coordinate : Fin n) :
    (protect fresh permission (liftOccurrence occurrence)).weights coordinate.succ =
      occurrence.weights coordinate := by
  rw [protect, shift_other fresh coordinate.succ (Fin.succ_ne_zero coordinate)]
  exact liftOccurrence_old occurrence coordinate

theorem fresh_release_old (permission : Permission Key) (occurrence : Occurrence n Key)
    (coordinate : Fin n) :
    (release fresh permission (liftOccurrence occurrence)).weights coordinate.succ =
      occurrence.weights coordinate := by
  rw [release, shift_other fresh coordinate.succ (Fin.succ_ne_zero coordinate)]
  exact liftOccurrence_old occurrence coordinate

theorem fresh_protect_residual [DecidableEq Key] (handled : List Key) (permission : Permission Key)
    (row : Row n Key) :
    residual handled (row.map (fun occurrence => protect fresh permission (liftOccurrence occurrence))) =
      (residual (handled.filter permission) row).map
        (fun occurrence => protect fresh permission (liftOccurrence occurrence)) := by
  have capture (occurrence : Occurrence n Key) :
      Capturable handled (protect fresh permission (liftOccurrence occurrence)) ↔
        Capturable (handled.filter permission) occurrence := by
    rw [fresh_protect_capture_iff]
    simp only [Capturable, List.mem_filter]
    exact ⟨fun ⟨⟨member, zero⟩, allowed⟩ => ⟨⟨member, allowed⟩, zero⟩,
      fun ⟨⟨member, allowed⟩, zero⟩ => ⟨⟨member, zero⟩, allowed⟩⟩
  simp only [residual, List.filter_map, Function.comp_def, capture]

def liftTree (computation : Computation n Key Payload Response Value) :
    Computation (n + 1) Key Payload Response Value := reindexTree Fin.succ computation

/-- This premise is constructed by allocation, even for an incoming tree with
negative debts at every old coordinate. -/
theorem liftTree_zeroAt (computation : Computation n Key Payload Response Value) :
    Computation.ZeroAt fresh (liftTree computation) :=
  reindexTree_zeroAt Fin.succ fresh Fin.succ_ne_zero computation

theorem liftTree_recover (computation : Computation n Key Payload Response Value) :
    mapRequests (restrict Fin.succ) (liftTree computation) = computation :=
  reindexTree_recover Fin.succ succ_injective computation

/-- Allocating a fresh coordinate makes default protection noncapturing for
every original signed tree. No zero-origin hypothesis is imposed on that tree. -/
theorem fresh_noncapture [DecidableEq Key] (handled : List Key)
    (onReturn : Value → Computation (n + 1) Key Payload Response Result)
    (onOperation : Occurrence (n + 1) Key → Payload →
      (Response → Computation (n + 1) Key Payload Response Value) →
        Computation (n + 1) Key Payload Response Result)
    (computation : Computation n Key Payload Response Value) :
    Computation.shallowHandle handled onReturn onOperation
      (Computation.mapRequests (protect fresh allowNone) (liftTree computation)) =
        (Computation.mapRequests (protect fresh allowNone) (liftTree computation)).bind onReturn :=
  Computation.default_zero_boundary_noncapture handled fresh onReturn onOperation
    (liftTree computation) (liftTree_zeroAt computation)

/-- Matching release restores the lifted tree, including every old debt. -/
theorem fresh_roundtrip (permission : Permission Key)
    (computation : Computation n Key Payload Response Value) :
    Computation.mapRequests (release fresh permission)
      (Computation.mapRequests (protect fresh permission) (liftTree computation)) = liftTree computation :=
  Computation.release_protect fresh permission (liftTree computation)

namespace Examples

def oldScope : Fin 1 := 0
def oldDebt : Occurrence 1 Nat := release oldScope allowNone (raw 0)
abbrev OldTree := Computation 1 Nat Nat Unit Nat
abbrev NewTree := Computation 2 Nat Nat Unit Nat

def incoming : OldTree := .request oldDebt 7 (fun _ => .pure 11)

theorem incoming_negative_weight : oldDebt.weights oldScope = -1 := rfl

theorem reusing_old_coordinate_would_capture :
    Capturable [0] (protect oldScope allowNone oldDebt) := by
  rw [oldDebt, Directed.protect_release]
  simp [Capturable, raw]

theorem fresh_guard_keeps_old_negative_weight :
    (protect fresh allowNone (liftOccurrence oldDebt)).weights oldScope.succ = -1 := by
  rw [fresh_protect_old]
  exact incoming_negative_weight

theorem fresh_guard_adds_an_independent_weight :
    (protect fresh allowNone (liftOccurrence oldDebt)).weights fresh = 1 := by
  rw [protect, shift_same _ _ _ _ rfl, liftOccurrence_fresh]
  rfl

theorem fresh_guard_blocks_arbitrary_handler :
    Computation.shallowHandle [0] (fun value => (.pure value : NewTree))
      (fun _ _ _ => .pure 99)
      (Computation.mapRequests (protect fresh allowNone) (liftTree incoming)) =
        .request (protect fresh allowNone (liftOccurrence oldDebt)) 7 (fun _ => .pure 11) :=
  fresh_noncapture [0] _ _ incoming

theorem release_does_not_erase_old_debt :
    (release fresh allowNone (protect fresh allowNone (liftOccurrence oldDebt))).weights
      oldScope.succ = -1 := by
  rw [Directed.release_protect, liftOccurrence_old]
  exact incoming_negative_weight

end Examples

end Yulang.FreshBoundaries
