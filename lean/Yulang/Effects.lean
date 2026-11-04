import Std

/-!
# Scoped effect rows and shallow handlers

This kernel formalizes occurrence-local visibility, rather than the retired
directed-weight solver. `Key` is an exact request identity, including any type
arguments and, for individual-operation handling, the operation identifier.
A row is a finite list representation with extensional membership;
barrier lists retain repeated activations and `release` removes one occurrence.

The symbolic-row and computation theorems hold for every row substitution and
every well-founded computation tree. They do not assert correctness of a Yulang
parser, elaborator, subtype solver, or runtime implementation.

Sources: `spec/05-effects.md` §§5.3–5.5, `spec/07-display.md` §7.3;
`yulang2-oracle:web/docs/ja/reference/type-theory.md` (behavioral provenance).
-/

namespace Yulang.Effects

/-- Family identity retains its act/family parameters; equality does not erase them.
Operation-local polymorphic variables belong to signature checking, not this key. -/
structure EffectKey (Family : Type u) (Argument : Type v) where
  family : Family
  arguments : List Argument
  deriving DecidableEq, Repr

/--
Use operation identity when a handler covers individual operations. `arguments`
contains act/family parameters, not operation-local polymorphic variables. Erasing an
entire family from a displayed row requires complete operation coverage (and
visibility); otherwise its residual family must remain. This kernel makes no
claim about a source-language coverage checker.
-/
structure OperationKey (Family : Type u) (Operation : Type v) (Argument : Type w) where
  family : Family
  operation : Operation
  arguments : List Argument
  deriving DecidableEq, Repr

def OperationKey.toEffectKey (key : OperationKey Family Operation Argument) :
    EffectKey Family Argument := ⟨key.family, key.arguments⟩

/-- Barriers belong to this occurrence, not to a globally mutable row variable. -/
structure Occurrence (Key : Type u) where
  key : Key
  barriers : List Nat := []
  deriving DecidableEq, Repr

abbrev Row (Key : Type u) := List (Occurrence Key)
abbrev Permission (Key : Type u) := Key → Bool

def allowNone : Permission Key := fun _ => false
def allowAll : Permission Key := fun _ => true

/-- A permission grants no ability to remove barriers belonging to other scopes. -/
def protectOccurrence (scope : Nat) (permission : Permission Key)
    (occurrence : Occurrence Key) : Occurrence Key :=
  { key := occurrence.key
    barriers := if permission occurrence.key then occurrence.barriers
      else scope :: occurrence.barriers }

/-- Remove one matching activation, preserving repeated and unrelated barriers. -/
def releaseOccurrence (scope : Nat) (occurrence : Occurrence Key) : Occurrence Key :=
  { key := occurrence.key, barriers := occurrence.barriers.erase scope }

def protect (scope : Nat) (permission : Permission Key) (row : Row Key) : Row Key :=
  row.map (protectOccurrence scope permission)

def release (scope : Nat) (row : Row Key) : Row Key :=
  row.map (releaseOccurrence scope)

def Fresh (scope : Nat) (row : Row Key) : Prop :=
  ∀ occurrence ∈ row, scope ∉ occurrence.barriers

/-- Matching the exact key is necessary; a protected occurrence is never captured. -/
def Capturable (handled : List Key) (occurrence : Occurrence Key) : Prop :=
  occurrence.key ∈ handled ∧ occurrence.barriers = []

instance [DecidableEq Key] (handled : List Key) (occurrence : Occurrence Key) :
    Decidable (Capturable handled occurrence) := inferInstanceAs
      (Decidable (occurrence.key ∈ handled ∧ occurrence.barriers = []))

def captured [DecidableEq Key] (handled : List Key) (row : Row Key) : Row Key :=
  row.filter (fun occurrence => decide (Capturable handled occurrence))

def residual [DecidableEq Key] (handled : List Key) (row : Row Key) : Row Key :=
  row.filter (fun occurrence => !decide (Capturable handled occurrence))

def RowSubset (left right : Row Key) : Prop :=
  ∀ occurrence ∈ left, occurrence ∈ right

def RowEquiv (left right : Row Key) : Prop :=
  ∀ occurrence, occurrence ∈ left ↔ occurrence ∈ right

@[simp] theorem protectOccurrence_key (scope : Nat) (permission : Permission Key)
    (occurrence : Occurrence Key) :
    (protectOccurrence scope permission occurrence).key = occurrence.key := rfl

@[simp] theorem releaseOccurrence_key (scope : Nat) (occurrence : Occurrence Key) :
    (releaseOccurrence scope occurrence).key = occurrence.key := rfl

@[simp] theorem protect_all (scope : Nat) (row : Row Key) :
    protect scope allowAll row = row := by
  apply List.map_id''
  intro occurrence
  cases occurrence
  rfl

theorem not_capturable_of_barrier (handled : List Key) (occurrence : Occurrence Key)
    (scope : Nat) (blocked : scope ∈ occurrence.barriers) :
    ¬ Capturable handled occurrence := by
  intro h
  simp [h.2] at blocked

theorem protected_not_capturable (handled : List Key) (scope : Nat)
    (permission : Permission Key) (occurrence : Occurrence Key)
    (denied : permission occurrence.key = false) :
    ¬ Capturable handled (protectOccurrence scope permission occurrence) := by
  simp [Capturable, protectOccurrence, denied]

/-- All-family permission does not unprotect an occurrence already guarded outside. -/
theorem glob_preserves_outer_barrier (outer inner : Nat) (occurrence : Occurrence Key)
    (blocked : outer ∈ occurrence.barriers) :
    outer ∈ (protectOccurrence inner allowAll occurrence).barriers := by
  simpa [protectOccurrence, allowAll] using blocked

/-- Releasing one scope cannot remove a different scope's protection. -/
theorem release_preserves_other (removed other : Nat) (different : other ≠ removed)
    (occurrence : Occurrence Key) :
    other ∈ (releaseOccurrence removed occurrence).barriers ↔
      other ∈ occurrence.barriers := by
  exact List.mem_erase_of_ne different

/-- A new denied layer is removed exactly once, even without a freshness premise. -/
theorem release_protect_denied (scope : Nat) (permission : Permission Key)
    (occurrence : Occurrence Key) (denied : permission occurrence.key = false) :
    releaseOccurrence scope (protectOccurrence scope permission occurrence) = occurrence := by
  cases occurrence
  simp_all [releaseOccurrence, protectOccurrence]

/-- Freshness matters for permitted keys: release must not remove an older layer. -/
theorem release_protect_fresh (scope : Nat) (permission : Permission Key)
    (occurrence : Occurrence Key) (fresh : scope ∉ occurrence.barriers) :
    releaseOccurrence scope (protectOccurrence scope permission occurrence) = occurrence := by
  cases occurrence with
  | mk key barriers =>
    cases h : permission key <;>
      simp_all [releaseOccurrence, protectOccurrence, List.erase_of_not_mem]

theorem release_protect_row (scope : Nat) (permission : Permission Key)
    (row : Row Key) (fresh : Fresh scope row) :
    release scope (protect scope permission row) = row := by
  induction row with
  | nil => rfl
  | cons occurrence row ih =>
    have hf : scope ∉ occurrence.barriers := fresh occurrence (by simp)
    have hr : Fresh scope row := fun o ho => fresh o (by simp [ho])
    simp only [protect, release, List.map_cons]
    rw [release_protect_fresh scope permission occurrence hf]
    exact congrArg (List.cons occurrence) (ih hr)

theorem release_repeated_scope (scope : Nat) (key : Key) :
    releaseOccurrence scope ({ key := key, barriers := [scope, scope] } : Occurrence Key) =
      { key := key, barriers := [scope] } := by
  simp [releaseOccurrence]

@[simp] theorem mem_captured [DecidableEq Key] (handled : List Key) (row : Row Key)
    (occurrence : Occurrence Key) :
    occurrence ∈ captured handled row ↔
      occurrence ∈ row ∧ Capturable handled occurrence := by
  simp [captured]

@[simp] theorem mem_residual [DecidableEq Key] (handled : List Key) (row : Row Key)
    (occurrence : Occurrence Key) :
    occurrence ∈ residual handled row ↔
      occurrence ∈ row ∧ ¬ Capturable handled occurrence := by
  simp [residual]

theorem capture_partition [DecidableEq Key] (handled : List Key) (row : Row Key) :
    RowEquiv (captured handled row ++ residual handled row) row := by
  intro occurrence
  simp only [List.mem_append, mem_captured, mem_residual]
  constructor
  · intro h
    exact h.elim And.left And.left
  · intro h
    by_cases hc : Capturable handled occurrence
    · exact Or.inl ⟨h, hc⟩
    · exact Or.inr ⟨h, hc⟩

theorem capture_residual_disjoint [DecidableEq Key] (handled : List Key) (row : Row Key)
    (occurrence : Occurrence Key) :
    ¬ (occurrence ∈ captured handled row ∧ occurrence ∈ residual handled row) := by
  simp only [mem_captured, mem_residual]
  intro h
  exact h.2.2 h.1.2

/-- The computed residual is the least row preserving every uncapturable occurrence. -/
theorem residual_least [DecidableEq Key] (handled : List Key) (row candidate : Row Key)
    (preserves : ∀ occurrence ∈ row,
      ¬ Capturable handled occurrence → occurrence ∈ candidate) :
    RowSubset (residual handled row) candidate := by
  intro occurrence h
  rcases (mem_residual handled row occurrence).mp h with ⟨hr, hn⟩
  exact preserves occurrence hr hn

/-- An unhandled operation witnesses that its family is still in the residual. -/
theorem unhandled_operation_retains_family
    [DecidableEq Family] [DecidableEq Operation] [DecidableEq Argument]
    (handled : List (OperationKey Family Operation Argument))
    (row : Row (OperationKey Family Operation Argument))
    (occurrence : Occurrence (OperationKey Family Operation Argument))
    (member : occurrence ∈ row) (unhandled : occurrence.key ∉ handled) :
    occurrence.key.toEffectKey ∈
      (residual handled row).map (fun o => o.key.toEffectKey) := by
  apply List.mem_map.mpr
  refine ⟨occurrence, (mem_residual handled row occurrence).mpr ⟨member, ?_⟩, rfl⟩
  intro capturable
  exact unhandled capturable.1

/-- This is quantified over the actual row, not merely its currently known head. -/
theorem default_boundary_noncapture [DecidableEq Key] (handled : List Key)
    (scope : Nat) (row : Row Key) :
    residual handled (protect scope allowNone row) = protect scope allowNone row := by
  apply List.filter_eq_self.mpr
  intro occurrence h
  rcases List.mem_map.mp h with ⟨original, _, rfl⟩
  simp [protected_not_capturable handled scope allowNone original rfl]

@[simp] theorem residual_append [DecidableEq Key] (handled : List Key)
    (left right : Row Key) :
    residual handled (left ++ right) = residual handled left ++ residual handled right := by
  simp [residual]

/-- A concrete head may be consumed while the same key in a protected tail survives. -/
theorem visible_head_protected_tail [DecidableEq Key] (key : Key)
    (scope : Nat) (tail : Row Key) :
    residual [key] ({ key := key } :: protect scope allowNone tail) =
      protect scope allowNone tail := by
  have visible : Capturable [key] ({ key := key } : Occurrence Key) := by
    simp [Capturable]
  have step : residual [key] ({ key := key } :: protect scope allowNone tail) =
      residual [key] (protect scope allowNone tail) := by
    simp [residual, visible]
  rw [step]
  exact default_boundary_noncapture [key] scope tail

/-! ## Symbolic rows

Variables are opaque until substitution. Protection and release stay on their
occurrences and act on the entire substituted row. `RowExpr` is core syntax,
not permission for users to write inferred `'e?` or variant residuals.
-/

inductive RowExpr (Variable : Type u) (Key : Type v) where
  | empty
  | head (key : Key)
  | var (name : Variable)
  | union (left right : RowExpr Variable Key)
  | protect (scope : Nat) (permission : Permission Key) (row : RowExpr Variable Key)
  | release (scope : Nat) (row : RowExpr Variable Key)
  | residual (handled : List Key) (row : RowExpr Variable Key)

namespace RowExpr

def eval [DecidableEq Key] (environment : Variable → Row Key) : RowExpr Variable Key → Row Key
  | .empty => []
  | .head key => [{ key := key }]
  | .var name => environment name
  | .union left right => eval environment left ++ eval environment right
  | .protect scope permission row => Effects.protect scope permission (eval environment row)
  | .release scope row => Effects.release scope (eval environment row)
  | .residual handled row => Effects.residual handled (eval environment row)

def subst (substitution : Variable → RowExpr Other Key) :
    RowExpr Variable Key → RowExpr Other Key
  | .empty => .empty
  | .head key => .head key
  | .var name => substitution name
  | .union left right => .union (subst substitution left) (subst substitution right)
  | .protect scope permission row => .protect scope permission (subst substitution row)
  | .release scope row => .release scope (subst substitution row)
  | .residual handled row => .residual handled (subst substitution row)

theorem eval_subst [DecidableEq Key] (substitution : Variable → RowExpr Other Key)
    (environment : Other → Row Key) (row : RowExpr Variable Key) :
    eval environment (subst substitution row) =
      eval (fun name => eval environment (substitution name)) row := by
  induction row <;> simp_all [subst, eval]

theorem substituted_tail_noncapture [DecidableEq Key]
    (environment : Variable → Row Key) (name : Variable)
    (handled : List Key) (scope : Nat) :
    eval environment (.residual handled (.protect scope allowNone (.var name))) =
      eval environment (.protect scope allowNone (.var name)) :=
  default_boundary_noncapture handled scope (environment name)

end RowExpr

/-! ## Operational kernel

Well-founded computation trees retain operations, payloads and reusable continuations.
`Response` is an abstract common response carrier; this is an effect-hygiene
kernel, not a proof of operation-signature type safety. `shallowHandle` passes
the original continuation to a selected arm, without installing itself again.
-/

inductive Computation (Key : Type u) (Payload : Type v) (Response : Type w)
    (Value : Type z) where
  | pure (value : Value)
  | request (occurrence : Occurrence Key) (payload : Payload)
      (resume : Response → Computation Key Payload Response Value)

namespace Computation

def bind (computation : Computation Key Payload Response Value)
    (next : Value → Computation Key Payload Response Result) :
    Computation Key Payload Response Result :=
  match computation with
  | .pure value => next value
  | .request occurrence payload resume =>
      .request occurrence payload (fun response => bind (resume response) next)

def mapRequests (transform : Occurrence Key → Occurrence Other)
    (computation : Computation Key Payload Response Value) :
    Computation Other Payload Response Value :=
  match computation with
  | .pure value => .pure value
  | .request occurrence payload resume =>
      .request (transform occurrence) payload
        (fun response => mapRequests transform (resume response))

def shallowHandle [DecidableEq Key] (handled : List Key)
    (onReturn : Value → Computation Key Payload Response Result)
    (onOperation : Occurrence Key → Payload →
      (Response → Computation Key Payload Response Value) →
        Computation Key Payload Response Result)
    (computation : Computation Key Payload Response Value) :
    Computation Key Payload Response Result :=
  match computation with
  | .pure value => onReturn value
  | .request occurrence payload resume =>
      if Capturable handled occurrence then onOperation occurrence payload resume
      else .request occurrence payload
        (fun response => shallowHandle handled onReturn onOperation (resume response))

/-- A denied callback never invokes an internal operation arm, at any depth. -/
theorem default_boundary_operational_noncapture [DecidableEq Key]
    (handled : List Key) (scope : Nat)
    (onReturn : Value → Computation Key Payload Response Result)
    (onOperation : Occurrence Key → Payload →
      (Response → Computation Key Payload Response Value) →
        Computation Key Payload Response Result)
    (computation : Computation Key Payload Response Value) :
    shallowHandle handled onReturn onOperation
      (mapRequests (protectOccurrence scope allowNone) computation) =
        bind (mapRequests (protectOccurrence scope allowNone) computation) onReturn := by
  induction computation with
  | pure value => rfl
  | request occurrence payload resume ih =>
    simp only [mapRequests, shallowHandle,
      protected_not_capturable handled scope allowNone occurrence rfl, ↓reduceIte, bind]
    exact congrArg (Computation.request
      (protectOccurrence scope allowNone occurrence) payload) (funext ih)

/-- The selected shallow arm receives the unwrapped continuation exactly. -/
theorem shallow_resume_is_original [DecidableEq Key] (handled : List Key)
    (occurrence : Occurrence Key) (payload : Payload)
    (resume : Response → Computation Key Payload Response Value)
    (visible : Capturable handled occurrence) (response : Response) :
    shallowHandle handled Computation.pure
      (fun _ _ continuation => continuation response)
      (.request occurrence payload resume) = resume response := by
  simp [shallowHandle, visible]

/-- Potential requests include requests in every continuation, without executing it. -/
inductive Emits : Computation Key Payload Response Value → Occurrence Key → Prop where
  | now (occurrence : Occurrence Key) (payload : Payload)
      (resume : Response → Computation Key Payload Response Value) :
      Emits (.request occurrence payload resume) occurrence
  | later (occurrence : Occurrence Key) (payload : Payload)
      (resume : Response → Computation Key Payload Response Value)
      (response : Response) (later : Occurrence Key) :
      Emits (resume response) later → Emits (.request occurrence payload resume) later

def BoundedBy (row : Row Key) (computation : Computation Key Payload Response Value) : Prop :=
  ∀ occurrence, Emits computation occurrence → occurrence ∈ row

@[simp] theorem bounded_pure (row : Row Key) (value : Value) :
    BoundedBy row (Computation.pure value : Computation Key Payload Response Value) := by
  intro occurrence h
  cases h

theorem bounded_request_iff (row : Row Key) (occurrence : Occurrence Key)
    (payload : Payload) (resume : Response → Computation Key Payload Response Value) :
    BoundedBy row (.request occurrence payload resume) ↔
      occurrence ∈ row ∧ ∀ response, BoundedBy row (resume response) := by
  constructor
  · intro h
    exact ⟨h occurrence (.now occurrence payload resume), fun response later hl =>
      h later (.later occurrence payload resume response later hl)⟩
  · rintro ⟨ho, hr⟩ later hl
    cases hl with
    | now => exact ho
    | later _ _ _ response _ h => exact hr response _ h

theorem bounded_mono {left right : Row Key} (subset : RowSubset left right)
    {computation : Computation Key Payload Response Value}
    (bounded : BoundedBy left computation) : BoundedBy right computation :=
  fun occurrence h => subset occurrence (bounded occurrence h)

theorem mapRequests_bounded (transform : Occurrence Key → Occurrence Other)
    (row : Row Key) (computation : Computation Key Payload Response Value)
    (bounded : BoundedBy row computation) :
    BoundedBy (row.map transform) (mapRequests transform computation) := by
  induction computation with
  | pure value => exact bounded_pure _ _
  | request occurrence payload resume ih =>
    rcases (bounded_request_iff row occurrence payload resume).mp bounded with ⟨ho, hr⟩
    apply (bounded_request_iff _ _ _ _).mpr
    exact ⟨List.mem_map.mpr ⟨occurrence, ho, rfl⟩, fun response => ih response (hr response)⟩

/--
Compositional operational effect soundness for a shallow handler. Arm checking
must retain the original row on resumptions. Arm effects are added after
subtraction, so the handler cannot silently handle its own arm's effects.
-/
theorem shallowHandle_bounded [DecidableEq Key]
    (handled : List Key) (input armEffects : Row Key)
    (onReturn : Value → Computation Key Payload Response Result)
    (onOperation : Occurrence Key → Payload →
      (Response → Computation Key Payload Response Value) →
        Computation Key Payload Response Result)
    (returnBound : ∀ value, BoundedBy armEffects (onReturn value))
    (operationBound : ∀ occurrence payload resume,
      Capturable handled occurrence →
      (∀ response, BoundedBy input (resume response)) →
        BoundedBy armEffects (onOperation occurrence payload resume))
    (computation : Computation Key Payload Response Value)
    (inputBound : BoundedBy input computation) :
    BoundedBy (residual handled input ++ armEffects)
      (shallowHandle handled onReturn onOperation computation) := by
  induction computation with
  | pure value =>
    exact bounded_mono (fun o ho => List.mem_append.mpr (Or.inr ho)) (returnBound value)
  | request occurrence payload resume ih =>
    rcases (bounded_request_iff input occurrence payload resume).mp inputBound with ⟨ho, hr⟩
    by_cases hc : Capturable handled occurrence
    · simp only [shallowHandle, hc, ↓reduceIte]
      exact bounded_mono (fun o ho => List.mem_append.mpr (Or.inr ho))
        (operationBound occurrence payload resume hc hr)
    · simp only [shallowHandle, hc, ↓reduceIte]
      apply (bounded_request_iff _ _ _ _).mpr
      exact ⟨List.mem_append.mpr (Or.inl ((mem_residual _ _ _).mpr ⟨ho, hc⟩)),
        fun response => ih response (hr response)⟩

end Computation
end Yulang.Effects
