import Yulang.Effects

/-!
# Signed occurrence transport

An erase-only release cannot cancel a boundary in both variance directions.
This refinement records an integer balance per declared boundary coordinate.
Both positive protection and negative release debt prevent capture; visibility
requires every coordinate to be zero. Matching transport uses the same scope
and permission mask, and has a two-sided inverse.

`n` is an arbitrary finite interface of boundary names. Activation counts are
unbounded integers. This is not a construction of all dynamic source scopes or
a source-language elaboration theorem. In particular, adding one does not
protect an arbitrary signed input: incoming debt -1 would cancel. Noncapture
theorems state their zero-origin premise explicitly.
-/

namespace Yulang.Directed

structure Occurrence (n : Nat) (Key : Type u) where
  key : Key
  weights : Fin n → Int

theorem Occurrence.ext {a b : Occurrence n Key} (keys : a.key = b.key)
    (weights : ∀ coordinate, a.weights coordinate = b.weights coordinate) : a = b := by
  cases a
  cases b
  cases keys
  have equal := funext weights
  cases equal
  rfl

instance [DecidableEq Key] : DecidableEq (Occurrence n Key) := fun a b =>
  if keys : a.key = b.key then
    if weights : ∀ coordinate, a.weights coordinate = b.weights coordinate then
      isTrue (Occurrence.ext keys weights)
    else isFalse (fun equal => weights (fun coordinate =>
      congrFun (congrArg Occurrence.weights equal) coordinate))
  else isFalse (fun equal => keys (congrArg Occurrence.key equal))

abbrev Row (n : Nat) (Key : Type u) := List (Occurrence n Key)
abbrev Permission (Key : Type u) := Key → Bool

def allowNone : Permission Key := fun _ => false
def allowAll : Permission Key := fun _ => true

def raw (key : Key) : Occurrence n Key := ⟨key, fun _ => 0⟩

/-- A denied family moves by delta at precisely this boundary coordinate. -/
def shift (scope : Fin n) (permission : Permission Key) (delta : Int)
    (occurrence : Occurrence n Key) : Occurrence n Key :=
  { key := occurrence.key
    weights := fun coordinate =>
      if coordinate = scope ∧ permission occurrence.key = false then
        occurrence.weights coordinate + delta
      else occurrence.weights coordinate }

def protect (scope : Fin n) (permission : Permission Key) (occurrence : Occurrence n Key) :
    Occurrence n Key := shift scope permission 1 occurrence

/-- Release is the matching signed mask action, not unconditional barrier erasure. -/
def release (scope : Fin n) (permission : Permission Key) (occurrence : Occurrence n Key) :
    Occurrence n Key := shift scope permission (-1) occurrence

def Capturable (handled : List Key) (occurrence : Occurrence n Key) : Prop :=
  occurrence.key ∈ handled ∧ ∀ coordinate, occurrence.weights coordinate = 0

instance [DecidableEq Key] (handled : List Key) (occurrence : Occurrence n Key) :
    Decidable (Capturable handled occurrence) := inferInstanceAs
      (Decidable (occurrence.key ∈ handled ∧ ∀ coordinate, occurrence.weights coordinate = 0))

def residual [DecidableEq Key] (handled : List Key) (row : Row n Key) : Row n Key :=
  row.filter (fun occurrence => !decide (Capturable handled occurrence))

@[simp] theorem shift_key (scope : Fin n) (permission : Permission Key) (delta : Int)
    (occurrence : Occurrence n Key) : (shift scope permission delta occurrence).key = occurrence.key := rfl

@[simp] theorem protect_key (scope : Fin n) (permission : Permission Key)
    (occurrence : Occurrence n Key) : (protect scope permission occurrence).key = occurrence.key := rfl

@[simp] theorem release_key (scope : Fin n) (permission : Permission Key)
    (occurrence : Occurrence n Key) : (release scope permission occurrence).key = occurrence.key := rfl

theorem shift_same (scope : Fin n) (permission : Permission Key) (delta : Int)
    (occurrence : Occurrence n Key) (denied : permission occurrence.key = false) :
    (shift scope permission delta occurrence).weights scope = occurrence.weights scope + delta := by
  simp [shift, denied]

theorem shift_other (scope other : Fin n) (different : other ≠ scope)
    (permission : Permission Key) (delta : Int) (occurrence : Occurrence n Key) :
    (shift scope permission delta occurrence).weights other = occurrence.weights other := by
  simp [shift, different]

@[simp] theorem shift_zero (scope : Fin n) (permission : Permission Key)
    (occurrence : Occurrence n Key) : shift scope permission 0 occurrence = occurrence := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  simp [shift]

theorem shift_add (scope : Fin n) (permission : Permission Key) (first second : Int)
    (occurrence : Occurrence n Key) :
    shift scope permission second (shift scope permission first occurrence) =
      shift scope permission (first + second) occurrence := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  by_cases hs : coordinate = scope <;> cases hp : permission occurrence.key <;>
    simp [shift, hs, hp] <;> omega

@[simp] theorem release_protect (scope : Fin n) (permission : Permission Key)
    (occurrence : Occurrence n Key) :
    release scope permission (protect scope permission occurrence) = occurrence := by
  exact (shift_add scope permission 1 (-1) occurrence).trans (shift_zero scope permission occurrence)

@[simp] theorem protect_release (scope : Fin n) (permission : Permission Key)
    (occurrence : Occurrence n Key) :
    protect scope permission (release scope permission occurrence) = occurrence := by
  exact (shift_add scope permission (-1) 1 occurrence).trans (shift_zero scope permission occurrence)

theorem shifts_commute (left right : Fin n) (leftPermission rightPermission : Permission Key)
    (first second : Int) (occurrence : Occurrence n Key) :
    shift left leftPermission first (shift right rightPermission second occurrence) =
      shift right rightPermission second (shift left leftPermission first occurrence) := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  by_cases hl : coordinate = left <;> by_cases hr : coordinate = right <;>
    cases hp : leftPermission occurrence.key <;> cases hq : rightPermission occurrence.key <;>
      simp [shift, hl, hr, hp, hq] <;> omega

theorem glob_has_no_transport (scope : Fin n) (delta : Int) (occurrence : Occurrence n Key) :
    shift scope allowAll delta occurrence = occurrence := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  simp [shift, allowAll]

theorem nonzero_not_capturable (handled : List Key) (occurrence : Occurrence n Key)
    (scope : Fin n) (nonzero : occurrence.weights scope ≠ 0) :
    ¬ Capturable handled occurrence := fun capture => nonzero (capture.2 scope)

theorem protected_not_capturable (handled : List Key) (scope : Fin n)
    (permission : Permission Key) (occurrence : Occurrence n Key)
    (denied : permission occurrence.key = false) (origin : occurrence.weights scope = 0) :
    ¬ Capturable handled (protect scope permission occurrence) := by
  apply nonzero_not_capturable handled _ scope
  simp [protect, shift, denied, origin]

theorem negative_debt_not_capturable (handled : List Key) (scope : Fin n)
    (permission : Permission Key) (occurrence : Occurrence n Key)
    (denied : permission occurrence.key = false) (origin : occurrence.weights scope = 0) :
    ¬ Capturable handled (release scope permission occurrence) := by
  apply nonzero_not_capturable handled _ scope
  simp [release, shift, denied, origin]

/-- Counts are not clamped to a Boolean protection marker. -/
theorem repeated_protection (scope : Fin n) (key : Key) :
    (protect scope allowNone (protect scope allowNone (raw key))).weights scope = 2 := by
  simp [protect, shift, allowNone, raw]

theorem protect_row_release (scope : Fin n) (permission : Permission Key) (row : Row n Key) :
    (row.map (protect scope permission)).map (release scope permission) = row := by
  simp [List.map_map, Function.comp_def]

theorem release_row_protect (scope : Fin n) (permission : Permission Key) (row : Row n Key) :
    (row.map (release scope permission)).map (protect scope permission) = row := by
  simp [List.map_map, Function.comp_def]

theorem transport_does_not_inject_keys (scope : Fin n) (permission : Permission Key)
    (delta : Int) (row : Row n Key) :
    (row.map (shift scope permission delta)).map Occurrence.key = row.map Occurrence.key := by
  simp [List.map_map, Function.comp_def]

/-! ## The nonnegative barrier-list model embeds by multiplicity -/

def ofBarriers (key : Key) (barriers : List (Fin n)) : Occurrence n Key :=
  ⟨key, fun coordinate => (barriers.count coordinate : Int)⟩

theorem ofBarriers_zero_iff (key : Key) (barriers : List (Fin n)) :
    (∀ coordinate, (ofBarriers key barriers).weights coordinate = 0) ↔ barriers = [] := by
  cases barriers with
  | nil => simp [ofBarriers]
  | cons first rest =>
    constructor
    · intro h
      have impossible := h first
      simp only [ofBarriers, List.count_cons_self] at impossible
      omega
    · intro impossible
      cases impossible

theorem ofBarriers_capture_iff (handled : List Key) (key : Key) (barriers : List (Fin n)) :
    Capturable handled (ofBarriers key barriers) ↔ key ∈ handled ∧ barriers = [] := by
  exact and_congr Iff.rfl (ofBarriers_zero_iff key barriers)

/-- Agreement with the original model after embedding bounded scope names as Nat. -/
theorem legacy_capture_agrees (handled : List Key) (key : Key) (barriers : List (Fin n)) :
    Capturable handled (ofBarriers key barriers) ↔
      Effects.Capturable handled ⟨key, barriers.map Fin.val⟩ := by
  rw [ofBarriers_capture_iff]
  simp [Effects.Capturable]

theorem protect_ofBarriers (scope : Fin n) (permission : Permission Key)
    (key : Key) (barriers : List (Fin n)) :
    protect scope permission (ofBarriers key barriers) =
      ofBarriers key (if permission key then barriers else scope :: barriers) := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  cases hp : permission key <;> by_cases hs : coordinate = scope
  · subst coordinate
    simp [protect, shift, ofBarriers, hp, Int.natCast_add]
  · have hne : scope ≠ coordinate := Ne.symm hs
    simp [protect, shift, ofBarriers, hp, hs, List.count_cons_of_ne hne]
  · simp [protect, shift, ofBarriers, hp]
  · simp [protect, shift, ofBarriers, hp]

/-- Erase agrees with signed release only when a matching denied layer exists. -/
theorem release_ofBarriers (scope : Fin n) (permission : Permission Key)
    (key : Key) (barriers : List (Fin n))
    (denied : permission key = false) (present : scope ∈ barriers) :
    release scope permission (ofBarriers key barriers) = ofBarriers key (barriers.erase scope) := by
  apply Occurrence.ext
  · rfl
  intro coordinate
  by_cases hs : coordinate = scope
  · subst coordinate
    have positive : 0 < barriers.count scope := List.count_pos_iff.mpr present
    simp only [release, shift, ofBarriers, denied, and_self, ↓reduceIte, List.count_erase_self]
    omega
  · simp [release, shift, ofBarriers, denied, hs, List.count_erase_of_ne hs]

theorem absent_release_creates_debt (scope : Fin n) (key : Key) (barriers : List (Fin n))
    (absent : scope ∉ barriers) :
    (release scope allowNone (ofBarriers key barriers)).weights scope = -1 := by
  simp [release, shift, ofBarriers, allowNone, List.count_eq_zero_of_not_mem absent]

/-! ## Well-founded computation transport and shallow handlers -/

inductive Computation (n : Nat) (Key : Type u) (Payload : Type v) (Response : Type w)
    (Value : Type z) where
  | pure (value : Value)
  | request (occurrence : Occurrence n Key) (payload : Payload)
      (resume : Response → Computation n Key Payload Response Value)

namespace Computation

def bind (computation : Computation n Key Payload Response Value)
    (next : Value → Computation n Key Payload Response Result) :
    Computation n Key Payload Response Result :=
  match computation with
  | .pure value => next value
  | .request occurrence payload resume =>
      .request occurrence payload (fun response => bind (resume response) next)

def mapRequests (transform : Occurrence n Key → Occurrence n Other)
    (computation : Computation n Key Payload Response Value) :
    Computation n Other Payload Response Value :=
  match computation with
  | .pure value => .pure value
  | .request occurrence payload resume =>
      .request (transform occurrence) payload
        (fun response => mapRequests transform (resume response))

theorem mapRequests_id (computation : Computation n Key Payload Response Value) :
    mapRequests id computation = computation := by
  induction computation with
  | pure value => rfl
  | request occurrence payload resume ih =>
    exact congrArg (Computation.request occurrence payload) (funext ih)

theorem mapRequests_comp (first : Occurrence n Key → Occurrence n Middle)
    (second : Occurrence n Middle → Occurrence n Other)
    (computation : Computation n Key Payload Response Value) :
    mapRequests second (mapRequests first computation) =
      mapRequests (second ∘ first) computation := by
  induction computation with
  | pure value => rfl
  | request occurrence payload resume ih =>
    exact congrArg (Computation.request (second (first occurrence)) payload) (funext ih)

theorem mapRequests_inverse (first : Occurrence n Key → Occurrence n Other)
    (second : Occurrence n Other → Occurrence n Key)
    (inverse : ∀ occurrence, second (first occurrence) = occurrence)
    (computation : Computation n Key Payload Response Value) :
    mapRequests second (mapRequests first computation) = computation := by
  rw [mapRequests_comp]
  have identity : second ∘ first = id := funext inverse
  rw [identity, mapRequests_id]

theorem release_protect (scope : Fin n) (permission : Permission Key)
    (computation : Computation n Key Payload Response Value) :
    mapRequests (Directed.release scope permission)
      (mapRequests (Directed.protect scope permission) computation) = computation :=
  mapRequests_inverse _ _ (Directed.release_protect scope permission) computation

theorem protect_release (scope : Fin n) (permission : Permission Key)
    (computation : Computation n Key Payload Response Value) :
    mapRequests (Directed.protect scope permission)
      (mapRequests (Directed.release scope permission) computation) = computation :=
  mapRequests_inverse _ _ (Directed.protect_release scope permission) computation

def shallowHandle [DecidableEq Key] (handled : List Key)
    (onReturn : Value → Computation n Key Payload Response Result)
    (onOperation : Occurrence n Key → Payload →
      (Response → Computation n Key Payload Response Value) →
        Computation n Key Payload Response Result)
    (computation : Computation n Key Payload Response Value) :
    Computation n Key Payload Response Result :=
  match computation with
  | .pure value => onReturn value
  | .request occurrence payload resume =>
      if Capturable handled occurrence then onOperation occurrence payload resume
      else .request occurrence payload
        (fun response => shallowHandle handled onReturn onOperation (resume response))

def AllRequests (predicate : Occurrence n Key → Prop) :
    Computation n Key Payload Response Value → Prop
  | .pure _ => True
  | .request occurrence _ resume => predicate occurrence ∧
      ∀ response, AllRequests predicate (resume response)

def ZeroAt (scope : Fin n) (computation : Computation n Key Payload Response Value) : Prop :=
  AllRequests (fun occurrence => occurrence.weights scope = 0) computation

theorem allRequests_map (transform : Occurrence n Key → Occurrence n Other)
    (predicate : Occurrence n Other → Prop) (computation : Computation n Key Payload Response Value) :
    AllRequests predicate (mapRequests transform computation) ↔
      AllRequests (predicate ∘ transform) computation := by
  induction computation with
  | pure value => rfl
  | request occurrence payload resume ih =>
    simp only [mapRequests, AllRequests, Function.comp_def, ih]

theorem noncapture_of_uncapturable [DecidableEq Key]
    (handled : List Key)
    (onReturn : Value → Computation n Key Payload Response Result)
    (onOperation : Occurrence n Key → Payload →
      (Response → Computation n Key Payload Response Value) →
        Computation n Key Payload Response Result)
    (computation : Computation n Key Payload Response Value)
    (uncapturable : AllRequests (fun occurrence => ¬ Capturable handled occurrence) computation) :
    shallowHandle handled onReturn onOperation computation = bind computation onReturn := by
  induction computation with
  | pure value => rfl
  | request occurrence payload resume ih =>
    simp only [AllRequests] at uncapturable
    simp only [shallowHandle, uncapturable.1, ↓reduceIte, bind]
    exact congrArg (Computation.request occurrence payload)
      (funext (fun response => ih response (uncapturable.2 response)))

/-- Zero origin is essential: an incoming -1 debt would cancel the new guard. -/
theorem default_zero_boundary_noncapture [DecidableEq Key]
    (handled : List Key) (scope : Fin n)
    (onReturn : Value → Computation n Key Payload Response Result)
    (onOperation : Occurrence n Key → Payload →
      (Response → Computation n Key Payload Response Value) →
        Computation n Key Payload Response Result)
    (computation : Computation n Key Payload Response Value)
    (origin : ZeroAt scope computation) :
    shallowHandle handled onReturn onOperation
      (mapRequests (protect scope allowNone) computation) =
        bind (mapRequests (protect scope allowNone) computation) onReturn := by
  induction computation with
  | pure value => rfl
  | request occurrence payload resume ih =>
    rcases origin with ⟨headZero, restZero⟩
    simp only [mapRequests, shallowHandle,
      protected_not_capturable handled scope allowNone occurrence rfl headZero,
      ↓reduceIte, bind]
    exact congrArg (Computation.request (protect scope allowNone occurrence) payload)
      (funext (fun response => ih response (restZero response)))

theorem shallow_resume_is_original [DecidableEq Key] (handled : List Key)
    (occurrence : Occurrence n Key) (payload : Payload)
    (resume : Response → Computation n Key Payload Response Value)
    (visible : Capturable handled occurrence) (response : Response) :
    shallowHandle handled Computation.pure
      (fun _ _ continuation => continuation response)
      (.request occurrence payload resume) = resume response := by
  simp [shallowHandle, visible]

end Computation

namespace Examples

def scope : Fin 1 := ⟨0, by decide⟩

theorem release_before_protect_cancels :
    protect scope allowNone (release scope allowNone (raw 0)) = raw 0 :=
  protect_release scope allowNone (raw 0)

theorem negative_debt_blocks :
    ¬ Capturable [0] (release scope allowNone (raw 0)) :=
  negative_debt_not_capturable [0] scope allowNone (raw 0) rfl rfl

/-- This counterexample forbids a blanket noncapture claim for signed inputs. -/
theorem incoming_debt_cancels_guard :
    Capturable [0] (protect scope allowNone (release scope allowNone (raw 0))) := by
  rw [protect_release]
  simp [Capturable, raw]

theorem double_guard_is_not_single :
    protect scope allowNone (protect scope allowNone (raw 0)) ≠
      protect scope allowNone (raw 0) := by
  intro equality
  have values := congrArg (fun occurrence => occurrence.weights scope) equality
  simp [protect, shift, allowNone, raw] at values

end Examples
end Yulang.Directed
