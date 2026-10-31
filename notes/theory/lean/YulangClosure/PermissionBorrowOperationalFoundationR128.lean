import Std

/-!
R128 candidate local operational semantics. This module has no project imports.
ModuleKey and SourceNodeKey are abstract identity domains, not display spelling.
Locations and allocation identities are distinct. The trace covers the interval
of live shared borrows: there is no release or use-after-release transition.
This is not a Rust memory model or a source/native simulation.
-/
namespace YulangClosure.PermissionBorrowOperationalFoundationR128

structure Family (ModuleKey SourceNodeKey : Type) where
  module : ModuleKey
  declaration : SourceNodeKey
  deriving DecidableEq

structure Record (ModuleKey SourceNodeKey : Type) where
  allocation : Nat
  owner : Nat
  state : Nat
  batch : Nat
  registration : Nat
  concrete : List (Family ModuleKey SourceNodeKey)

structure Token (n : Nat) where
  location : Fin n
  allocation : Nat
  deriving DecidableEq

/-- A finite heap with n addressable slots. None represents an absent record. -/
structure State (ModuleKey SourceNodeKey : Type) (n : Nat) where
  heap : Fin n → Option (Record ModuleKey SourceNodeKey)
  borrows : List (Token n)

variable {ModuleKey SourceNodeKey : Type} {n : Nat}

/-- Every mutation, including deletion/replacement, requires an unborrowed slot.
Further shared borrows are permitted; all existing borrows remain live. -/
inductive Step : State ModuleKey SourceNodeKey n → State ModuleKey SourceNodeKey n → Prop
  | idle (s) : Step s s
  | borrow (s : State ModuleKey SourceNodeKey n) (t : Token n) (r : Record ModuleKey SourceNodeKey)
      (read : s.heap t.location = some r) (identity : r.allocation = t.allocation) :
      Step s ⟨s.heap, t :: s.borrows⟩
  | write (s : State ModuleKey SourceNodeKey n) (target : Fin n) (value : Option (Record ModuleKey SourceNodeKey))
      (free : ∀ t ∈ s.borrows, t.location ≠ target) :
      Step s ⟨fun q => if q = target then value else s.heap q, s.borrows⟩

inductive Trace : State ModuleKey SourceNodeKey n → State ModuleKey SourceNodeKey n → Prop
  | refl (s) : Trace s s
  | next {s u v} : Trace s u → Step u v → Trace s v

theorem step_preserves (t : Token n) {s u : State ModuleKey SourceNodeKey n}
    (live : t ∈ s.borrows) (step : Step s u) :
    t ∈ u.borrows ∧ u.heap t.location = s.heap t.location := by
  cases step with
  | idle => exact ⟨live, rfl⟩
  | borrow other r read identity => exact ⟨List.mem_cons_of_mem other live, rfl⟩
  | write target value free =>
    exact ⟨live, by simp only [free t live, ↓reduceIte]⟩

theorem trace_preserves (t : Token n) {s u : State ModuleKey SourceNodeKey n}
    (live : t ∈ s.borrows) (trace : Trace s u) :
    t ∈ u.borrows ∧ u.heap t.location = s.heap t.location := by
  induction trace with
  | refl => exact ⟨live, rfl⟩
  | next path step ih =>
    have one := step_preserves t ih.1 step
    exact ⟨one.1, one.2.trans ih.2⟩

variable [DecidableEq ModuleKey] [DecidableEq SourceNodeKey]

def orderedSearch : List (Family ModuleKey SourceNodeKey) → Family ModuleKey SourceNodeKey → Option Nat
  | [], _ => none
  | a :: xs, f => if a = f then some 0 else
      (orderedSearch xs f).map Nat.succ

def FirstAt (xs : List (Family ModuleKey SourceNodeKey)) (f : Family ModuleKey SourceNodeKey) (k : Nat) : Prop :=
  xs[k]? = some f ∧ ∀ j, j < k → xs[j]? ≠ some f

theorem search_first (xs : List (Family ModuleKey SourceNodeKey)) (f : Family ModuleKey SourceNodeKey) (k : Nat)
    (searched : orderedSearch xs f = some k) : FirstAt xs f k := by
  induction xs generalizing k with
  | nil => simp [orderedSearch] at searched
  | cons a xs ih =>
    by_cases same : a = f
    · have index : 0 = k := by simpa [orderedSearch, same] using searched
      subst k
      exact ⟨by simp [same], by intro j lt; omega⟩
    · cases tail : orderedSearch xs f with
      | none => simp [orderedSearch, same, tail] at searched
      | some i =>
        have index : Nat.succ i = k := by
          simpa [orderedSearch, same, tail] using searched
        subst k
        have first := ih i tail
        refine ⟨by simpa using first.1, ?_⟩
        intro j lt
        cases j with
        | zero => simpa using same
        | succ j =>
          simpa using first.2 j (Nat.lt_of_succ_lt_succ lt)

omit [DecidableEq ModuleKey] [DecidableEq SourceNodeKey] in
theorem indexed_member (xs : List (Family ModuleKey SourceNodeKey)) (k : Nat) (f : Family ModuleKey SourceNodeKey)
    (read : xs[k]? = some f) : f ∈ xs := by
  induction xs generalizing k with
  | nil => simp at read
  | cons a xs ih =>
    cases k with
    | zero =>
      have same : a = f := by simpa using read
      subst a
      simp
    | succ k => exact List.mem_cons_of_mem a (ih k (by simpa using read))

structure Captured (ModuleKey SourceNodeKey : Type) (n : Nat) where
  token : Token n
  family : Family ModuleKey SourceNodeKey
  member : Option Nat

/-- Search reads the actual heap record; the returned token records its slot
and allocation, while the optional member preserves the source field shape. -/
def capture (s : State ModuleKey SourceNodeKey n) (loc : Fin n) (f : Family ModuleKey SourceNodeKey) :
    Option (Captured ModuleKey SourceNodeKey n) := do
  let r ← s.heap loc
  let k ← orderedSearch r.concrete f
  pure ⟨⟨loc, r.allocation⟩, f, some k⟩

def capturedState (s : State ModuleKey SourceNodeKey n) (c : Captured ModuleKey SourceNodeKey n) : State ModuleKey SourceNodeKey n :=
  ⟨s.heap, c.token :: s.borrows⟩

structure Request (ModuleKey SourceNodeKey : Type) (n : Nat) where
  token : Token n
  family : Family ModuleKey SourceNodeKey
  member : Option Nat

/-- Actual field copy, rather than a law postulated for an opaque transport. -/
def copyRequest (c : Captured ModuleKey SourceNodeKey n) : Request ModuleKey SourceNodeKey n :=
  ⟨c.token, c.family, c.member⟩

def copyAgain (q : Request ModuleKey SourceNodeKey n) : Request ModuleKey SourceNodeKey n :=
  ⟨q.token, q.family, q.member⟩

/-- Local indexed consumer. Selection's location must be the captured location;
the allocation guard is separate. It reads the selected heap record itself.
Other native/source guards and registration-keyed selection are outside this
fragment: selected is the already selected location. -/
def consume (s : State ModuleKey SourceNodeKey n) (selected : Fin n) (q : Request ModuleKey SourceNodeKey n) :
    Option (Record ModuleKey SourceNodeKey) := do
  if selected = q.token.location then
    let r ← s.heap selected
    if r.allocation = q.token.allocation then
      let f ← q.member.bind (fun k => r.concrete[k]?)
      if f = q.family then some r else none
    else none
  else none

theorem consumer_exact_member (s : State ModuleKey SourceNodeKey n) (selected : Fin n)
    (q : Request ModuleKey SourceNodeKey n) (r : Record ModuleKey SourceNodeKey) (ok : consume s selected q = some r) :
    selected = q.token.location ∧ s.heap q.token.location = some r ∧
    r.allocation = q.token.allocation ∧ q.family ∈ r.concrete := by
  by_cases loc : selected = q.token.location
  · subst selected
    cases found : s.heap q.token.location with
    | none => simp [consume, found] at ok
    | some actual =>
      by_cases identity : actual.allocation = q.token.allocation
      · cases m : q.member with
        | none => simp [consume, found, m] at ok
        | some k =>
          cases read : actual.concrete[k]? with
          | none => simp [consume, found, identity, m, read] at ok
          | some f =>
            by_cases equal : f = q.family
            · have same : actual = r := by
                simpa [consume, found, identity, m, read, equal] using ok
              subst actual
              exact ⟨rfl, rfl, identity,
                indexed_member r.concrete k q.family (equal ▸ read)⟩
            · simp [consume, found, identity, m, read, equal] at ok
      · simp [consume, found, identity] at ok
  · simp [consume, loc] at ok

theorem capture_exact (s : State ModuleKey SourceNodeKey n) (loc : Fin n) (f : Family ModuleKey SourceNodeKey)
    (c : Captured ModuleKey SourceNodeKey n) (ok : capture s loc f = some c) :
    ∃ r k, s.heap loc = some r ∧ c.token = ⟨loc, r.allocation⟩ ∧
      c.family = f ∧ c.member = some k ∧ FirstAt r.concrete f k := by
  cases found : s.heap loc with
  | none => simp [capture, found] at ok
  | some r =>
    cases searched : orderedSearch r.concrete f with
    | none => simp [capture, found, searched] at ok
    | some k =>
      have same : (⟨⟨loc, r.allocation⟩, f, some k⟩ : Captured ModuleKey SourceNodeKey n) = c := by
        simpa [capture, found, searched] using ok
      subst c
      exact ⟨r, k, rfl, rfl, rfl, rfl, search_first r.concrete f k searched⟩

/-- Capture, ongoing shared-borrow transitions and two concrete copies preserve
both the first matching position and a successful read of the original record. -/
theorem captured_trace_copy (s : State ModuleKey SourceNodeKey n) (loc : Fin n) (f : Family ModuleKey SourceNodeKey)
    (c : Captured ModuleKey SourceNodeKey n) (ok : capture s loc f = some c)
    (u : State ModuleKey SourceNodeKey n) (trace : Trace (capturedState s c) u) :
    ∃ r k, s.heap loc = some r ∧ u.heap loc = some r ∧
      (copyAgain (copyRequest c)).member = some k ∧
      FirstAt r.concrete f k ∧
      consume u loc (copyAgain (copyRequest c)) = some r := by
  obtain ⟨r, k, found, token, family, member, first⟩ := capture_exact s loc f c ok
  have stable := trace_preserves c.token
    (s := capturedState s c) (by simp [capturedState]) trace
  have location : c.token.location = loc := congrArg Token.location token
  have allocation : c.token.allocation = r.allocation := congrArg Token.allocation token
  have retained : u.heap loc = some r := by
    simpa [capturedState, location, found] using stable.2
  exact ⟨r, k, found, retained, member, first, by
    simp [consume, copyAgain, copyRequest, location, allocation, retained,
      member, family, first.1]⟩

/-- The conclusion also refers to the original pre-trace record, not just an
arbitrary equal-looking current list. -/
theorem captured_consumer_original_member (s : State ModuleKey SourceNodeKey n) (loc : Fin n)
    (f : Family ModuleKey SourceNodeKey) (c : Captured ModuleKey SourceNodeKey n) (ok : capture s loc f = some c)
    (u : State ModuleKey SourceNodeKey n) (trace : Trace (capturedState s c) u)
    (selected : Fin n) (r : Record ModuleKey SourceNodeKey)
    (success : consume u selected (copyRequest c) = some r) :
    s.heap loc = some r ∧ f ∈ r.concrete := by
  obtain ⟨original, k, found, retained, copied, first, consumed⟩ :=
    captured_trace_copy s loc f c ok u trace
  obtain ⟨origin, j, before, token, family, member, isFirst⟩ := capture_exact s loc f c ok
  have exactRead := consumer_exact_member u selected (copyRequest c) r success
  have location : c.token.location = loc := congrArg Token.location token
  have same : original = r := Option.some.inj (retained.symm.trans (by
    simpa [copyRequest, location] using exactRead.2.1))
  subst original
  exact ⟨found, by simpa [copyRequest, family] using exactRead.2.2.2⟩

def nine : Family Nat Nat := ⟨0, 9⟩
def duplicateRecord : Record Nat Nat := ⟨12, 3, 4, 5, 7, [nine, nine]⟩
def duplicateState : State Nat Nat 1 := ⟨fun _ => some duplicateRecord, []⟩
def localRequest (k : Nat) : Request Nat Nat 1 := ⟨⟨0, 12⟩, nine, some k⟩

theorem duplicate_discriminator :
    capture duplicateState 0 nine = some ⟨⟨0, 12⟩, nine, some 0⟩ ∧
    consume duplicateState 0 (localRequest 0) = some duplicateRecord ∧
    consume duplicateState 0 (localRequest 1) = some duplicateRecord ∧
    ¬ FirstAt duplicateRecord.concrete nine 1 := by
  refine ⟨by rfl, by rfl, by rfl, ?_⟩
  intro first
  exact first.2 0 (by decide) (by decide)

theorem unequal_module_same_declaration :
    (⟨0, 9⟩ : Family Nat Nat) ≠ ⟨1, 9⟩ ∧
    orderedSearch [⟨0, 9⟩, ⟨1, 9⟩] (⟨1, 9⟩ : Family Nat Nat) = some 1 := by decide

end YulangClosure.PermissionBorrowOperationalFoundationR128

#check @YulangClosure.PermissionBorrowOperationalFoundationR128.step_preserves
#print axioms YulangClosure.PermissionBorrowOperationalFoundationR128.step_preserves
#check @YulangClosure.PermissionBorrowOperationalFoundationR128.trace_preserves
#print axioms YulangClosure.PermissionBorrowOperationalFoundationR128.trace_preserves
#check @YulangClosure.PermissionBorrowOperationalFoundationR128.search_first
#print axioms YulangClosure.PermissionBorrowOperationalFoundationR128.search_first
#check @YulangClosure.PermissionBorrowOperationalFoundationR128.indexed_member
#print axioms YulangClosure.PermissionBorrowOperationalFoundationR128.indexed_member
#check @YulangClosure.PermissionBorrowOperationalFoundationR128.consumer_exact_member
#print axioms YulangClosure.PermissionBorrowOperationalFoundationR128.consumer_exact_member
#check @YulangClosure.PermissionBorrowOperationalFoundationR128.capture_exact
#print axioms YulangClosure.PermissionBorrowOperationalFoundationR128.capture_exact
#check @YulangClosure.PermissionBorrowOperationalFoundationR128.captured_trace_copy
#print axioms YulangClosure.PermissionBorrowOperationalFoundationR128.captured_trace_copy
#check @YulangClosure.PermissionBorrowOperationalFoundationR128.captured_consumer_original_member
#print axioms YulangClosure.PermissionBorrowOperationalFoundationR128.captured_consumer_original_member
#check @YulangClosure.PermissionBorrowOperationalFoundationR128.duplicate_discriminator
#print axioms YulangClosure.PermissionBorrowOperationalFoundationR128.duplicate_discriminator

#check @YulangClosure.PermissionBorrowOperationalFoundationR128.unequal_module_same_declaration
#print axioms YulangClosure.PermissionBorrowOperationalFoundationR128.unequal_module_same_declaration
