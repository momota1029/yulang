import Std

/-! Shared operation/restoration journals.  A successful checked event list
constructs one table and its actual reverse undo records. Cancellation restores
all checkpoint owners simultaneously, discards new owners, and retains a ghost
birth clock so that reused numeric IDs cannot authenticate cancelled children.
This is the native mutable-owner projection, not a Rust execution semantics or
a semantic completion predicate. Frame/worklist readback remains separate. -/

namespace YulangClosure.NativeExecutionHistory

structure Address where
  lane : Nat
  index : Nat
  deriving DecidableEq, Repr

structure Cell (α : Type) where
  birth : Nat
  value : α
  deriving DecidableEq, Repr

abbrev Table (α : Type) := Address → Option (Cell α)

def put (table : Table α) (key : Address) (value : Option (Cell α)) : Table α :=
  fun other => if other = key then value else table other

@[simp] theorem put_same (table : Table α) (key : Address) (value : Option (Cell α)) :
    put table key value key = value := by simp [put]

theorem put_other (table : Table α) (key other : Address) (value : Option (Cell α))
    (different : other ≠ key) : put table key value other = table other := by
  simp [put, different]

theorem put_restore (table : Table α) (key : Address) (value : Option (Cell α)) :
    put (put table key value) key (table key) = table := by
  funext other
  by_cases h : other = key <;> simp [put, h]

theorem put_self (table : Table α) (key : Address) : put table key (table key) = table := by
  funext other
  by_cases h : other = key <;> simp [put, h]

structure Undo (α : Type) where
  key : Address
  before : Option (Cell α)

def unwind (table : Table α) : List (Undo α) → Table α
  | [] => table
  | item :: rest => unwind (put table item.key item.before) rest

theorem unwind_key_congr {left right : Table α} (key : Address)
    (same : left key = right key) (undo : List (Undo α)) :
    unwind left undo key = unwind right undo key := by
  induction undo generalizing left right with
  | nil => exact same
  | cons item rest ih =>
      apply ih
      by_cases h : key = item.key <;> simp [put, h, same]

theorem unwind_covered {left right : Table α} (key : Address) (undo : List (Undo α))
    (covered : ∃ item ∈ undo, item.key = key) :
    unwind left undo key = unwind right undo key := by
  induction undo generalizing left right with
  | nil => simp at covered
  | cons item rest ih =>
      change unwind (put left item.key item.before) rest key =
        unwind (put right item.key item.before) rest key
      by_cases same : item.key = key
      · apply unwind_key_congr
        simp [put, same]
      · apply ih
        obtain ⟨entry, member, key_eq⟩ := covered
        rcases List.mem_cons.mp member with head | tail
        · subst entry; exact False.elim (same key_eq)
        · exact ⟨entry, tail, key_eq⟩

theorem unwind_prepared_put (table : Table α) (key : Address) (value : Option (Cell α))
    (undo : List (Undo α)) (covered : ∃ item ∈ undo, item.key = key) :
    unwind (put table key value) undo = unwind table undo := by
  funext other
  by_cases same : other = key
  · subst other; exact unwind_covered key undo covered
  · exact unwind_key_congr other (by simp [put, same]) undo

def Below (frontier : Nat) (left right : Table α) : Prop :=
  ∀ key, key.index < frontier → left key = right key

theorem unwind_below {frontier : Nat} {left right : Table α}
    (same : Below frontier left right) (undo : List (Undo α)) :
    Below frontier (unwind left undo) (unwind right undo) := by
  induction undo generalizing left right with
  | nil => exact same
  | cons item rest ih =>
      apply ih
      intro key bound
      by_cases h : key = item.key
      · simp [put, h]
      · simp only [put, ite_eq_right h]
        exact same key bound

def restrict (frontier : Nat) (table : Table α) : Table α :=
  fun key => if key.index < frontier then table key else none

structure State (α : Type) where
  next : Nat
  clock : Nat
  table : Table α
  undo : List (Undo α)

def empty : State α := ⟨0, 0, fun _ => none, []⟩

def allocate (s : State α) (lane : Nat) (value : α) : State α :=
  { s with
    next := s.next + 1
    clock := s.clock + 1
    table := put s.table ⟨lane, s.next⟩ (some ⟨s.clock, value⟩) }

def update (s : State α) (key : Address) (before : Cell α) (value : α) : State α :=
  { s with
    table := put s.table key (some { before with value := value })
    undo := ⟨key, s.table key⟩ :: s.undo }

/-- Preflight can record several old tuples before any acknowledgement mutates
them. A later mutation consumes this route's protection, not a new snapshot. -/
def prepare (s : State α) (key : Address) : State α :=
  { s with undo := ⟨key, s.table key⟩ :: s.undo }

def mutate (s : State α) (key : Address) (before : Cell α) (value : α) : State α :=
  { s with table := put s.table key (some { before with value := value }) }

def hasPreparation (s : State α) (key : Address) : Bool :=
  s.undo.any (fun entry => decide (entry.key = key))

theorem hasPreparation_iff (s : State α) (key : Address) :
    hasPreparation s key = true ↔ ∃ entry ∈ s.undo, entry.key = key := by
  simp [hasPreparation]

/-- Each route starts with its own journal suffix. Earlier journal storage is
outside this projection and is retained by the native checkpoint. -/
def begin (s : State α) : State α := { s with undo := [] }

def commit (s : State α) : State α := { s with undo := [] }

def cancel (saved current : State α) : State α :=
  { next := saved.next, clock := current.clock,
    table := restrict saved.next (unwind current.table current.undo), undo := [] }

inductive Event (α : Type) where
  | allocate (lane : Nat) (value : α)
  | update (key : Address) (value : α)
  | prepare (key : Address)
  | mutate (key : Address) (value : α)

/-- The checker reads the actual old cell; the caller supplies no old snapshot. -/
def step (s : State α) : Event α → Option (State α)
  | .allocate lane value =>
      match s.table ⟨lane, s.next⟩ with
      | none => some (allocate s lane value)
      | some _ => none
  | .update key value =>
      match s.table key with
      | none => none
      | some before => some (update s key before value)
  | .prepare key =>
      match s.table key with
      | none => none
      | some _ => some (prepare s key)
  | .mutate key value =>
      match s.table key with
      | none => none
      | some before => if hasPreparation s key then some (mutate s key before value) else none

def run (s : State α) : List (Event α) → Option (State α)
  | [] => some s
  | event :: rest => (step s event).bind (fun next => run next rest)

inductive Step : State α → Event α → State α → Prop
  | allocate (s : State α) (lane : Nat) (value : α)
      (fresh : s.table ⟨lane, s.next⟩ = none) :
      Step s (.allocate lane value) (allocate s lane value)
  | update (s : State α) (key : Address) (before : Cell α) (value : α)
      (actual : s.table key = some before) :
      Step s (.update key value) (update s key before value)
  | prepare (s : State α) (key : Address) (before : Cell α)
      (actual : s.table key = some before) : Step s (.prepare key) (prepare s key)
  | mutate (s : State α) (key : Address) (before : Cell α) (value : α)
      (actual : s.table key = some before) (covered : hasPreparation s key = true) :
      Step s (.mutate key value) (mutate s key before value)

inductive Exec : State α → List (Event α) → State α → Prop
  | nil (s : State α) : Exec s [] s
  | cons {s t u : State α} {event : Event α} {rest : List (Event α)} :
      Step s event t → Exec t rest u → Exec s (event :: rest) u

theorem checked_step {s t : State α} {event : Event α}
    (checked : step s event = some t) : Step s event t := by
  cases event with
  | allocate lane value =>
      cases h : s.table ⟨lane, s.next⟩ with
      | none =>
          simp [step, h] at checked
          subst t
          exact .allocate s lane value h
      | some before => simp [step, h] at checked
  | update key value =>
      cases h : s.table key with
      | none => simp [step, h] at checked
      | some before =>
          simp [step, h] at checked
          subst t
          exact .update s key before value h
  | prepare key =>
      cases h : s.table key with
      | none => simp [step, h] at checked
      | some before =>
          simp [step, h] at checked
          subst t
          exact .prepare s key before h
  | mutate key value =>
      cases h : s.table key with
      | none => simp [step, h] at checked
      | some before =>
          by_cases covered : hasPreparation s key = true
          · simp [step, h, covered] at checked
            subst t
            exact .mutate s key before value h covered
          · simp [step, h, covered] at checked

theorem checked_run {s t : State α} {events : List (Event α)}
    (checked : run s events = some t) : Exec s events t := by
  induction events generalizing s with
  | nil => simp [run] at checked; subst t; exact .nil s
  | cons event rest ih =>
      cases h : step s event with
      | none => simp [run, h] at checked
      | some next =>
          apply Exec.cons (checked_step h)
          exact ih (by simpa [run, h] using checked)

structure WellFormed (s : State α) : Prop where
  bounded : ∀ key cell, s.table key = some cell → key.index < s.next
  stamped : ∀ key cell, s.table key = some cell → cell.birth < s.clock

theorem empty_wellFormed : WellFormed (empty : State α) := by
  constructor <;> intro key cell h <;> simp [empty] at h

theorem begin_wellFormed {s : State α} (h : WellFormed s) : WellFormed (begin s) :=
  ⟨h.bounded, h.stamped⟩

theorem commit_wellFormed {s : State α} (h : WellFormed s) : WellFormed (commit s) :=
  ⟨h.bounded, h.stamped⟩

theorem step_monotone {s t : State α} {event : Event α} (h : Step s event t) :
    s.next ≤ t.next ∧ s.clock ≤ t.clock := by
  cases h <;> simp [allocate, update, prepare, mutate]

theorem exec_monotone {s t : State α} {events : List (Event α)} (h : Exec s events t) :
    s.next ≤ t.next ∧ s.clock ≤ t.clock := by
  induction h with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons first rest ih =>
      have h := step_monotone first
      exact ⟨Nat.le_trans h.1 ih.1, Nat.le_trans h.2 ih.2⟩

theorem step_wellFormed {s t : State α} {event : Event α}
    (well : WellFormed s) (h : Step s event t) : WellFormed t := by
  cases h with
  | allocate lane value fresh =>
      constructor
      · intro key cell found
        by_cases same : key = ⟨lane, s.next⟩
        · subst key; simp [allocate]
        · have old : s.table key = some cell := by simpa [allocate, put, same] using found
          have := well.bounded key cell old
          simp only [allocate]
          omega
      · intro key cell found
        by_cases same : key = ⟨lane, s.next⟩
        · subst key
          have eq : (⟨s.clock, value⟩ : Cell α) = cell := by simpa [allocate] using found
          subst cell
          simp [allocate]
        · have old : s.table key = some cell := by simpa [allocate, put, same] using found
          have := well.stamped key cell old
          simp only [allocate]
          omega
  | update target before value actual =>
      constructor
      · intro key cell found
        by_cases same : key = target
        · subst key; exact well.bounded target before actual
        · exact well.bounded key cell (by simpa [update, put, same] using found)
      · intro key cell found
        by_cases same : key = target
        · subst key
          have eq : ({ before with value := value } : Cell α) = cell := by
            simpa [update] using found
          subst cell
          exact well.stamped target before actual
        · exact well.stamped key cell (by simpa [update, put, same] using found)
  | prepare key before actual => exact ⟨well.bounded, well.stamped⟩
  | mutate target before value actual covered =>
      constructor
      · intro key cell found
        by_cases same : key = target
        · subst key; exact well.bounded target before actual
        · exact well.bounded key cell (by simpa [mutate, put, same] using found)
      · intro key cell found
        by_cases same : key = target
        · subst key
          have eq : ({ before with value := value } : Cell α) = cell := by
            simpa [mutate] using found
          subst cell
          exact well.stamped target before actual
        · exact well.stamped key cell (by simpa [mutate, put, same] using found)

theorem exec_wellFormed {s t : State α} {events : List (Event α)}
    (well : WellFormed s) (h : Exec s events t) : WellFormed t := by
  induction h with
  | nil => exact well
  | cons first rest ih => exact ih (step_wellFormed well first)

/-- An unjournaled new allocation is invisible below the checkpoint frontier,
even when arbitrary owner updates are already recorded in the shared journal. -/
theorem allocation_unwind_below (s : State α) (lane : Nat) (value : α)
    {frontier : Nat} (old : frontier ≤ s.next) :
    Below frontier (unwind (allocate s lane value).table (allocate s lane value).undo)
      (unwind s.table s.undo) := by
  apply unwind_below
  intro key bound
  have different : key ≠ (⟨lane, s.next⟩ : Address) := by
    intro same
    have idx := congrArg Address.index same
    simp only at idx
    omega
  simp [allocate, put, different]

theorem update_unwind (s : State α) (key : Address) (before : Cell α) (value : α) :
    unwind (update s key before value).table (update s key before value).undo =
      unwind s.table s.undo := by
  simp only [update, unwind]
  rw [put_restore]

theorem prepare_unwind (s : State α) (key : Address) :
    unwind (prepare s key).table (prepare s key).undo = unwind s.table s.undo := by
  simp only [prepare, unwind, put_self]

theorem mutate_unwind (s : State α) (key : Address) (before : Cell α) (value : α)
    (covered : hasPreparation s key = true) :
    unwind (mutate s key before value).table (mutate s key before value).undo =
      unwind s.table s.undo :=
  unwind_prepared_put s.table key _ s.undo ((hasPreparation_iff s key).mp covered)

theorem exec_unwind_below {s t : State α} {events : List (Event α)}
    (h : Exec s events t) :
    Below s.next (unwind t.table t.undo) (unwind s.table s.undo) := by
  induction h with
  | nil => intro key _; rfl
  | @cons s mid t event rest first tail ih =>
      intro key bound
      have m := (step_monotone first).1
      have hm : key.index < mid.next := Nat.lt_of_lt_of_le bound m
      rw [ih key hm]
      cases first with
      | allocate lane value fresh => exact allocation_unwind_below s lane value (Nat.le_refl _) key bound
      | update target before value actual => rw [update_unwind]
      | prepare key before actual => rw [prepare_unwind]
      | mutate key before value actual covered => rw [mutate_unwind s key before value covered]

/-- A single checked chronological event list restores every old owner at once. -/
theorem cancel_table_exact {saved current : State α} {events : List (Event α)}
    (well : WellFormed saved) (history : Exec (begin saved) events current) :
    (cancel saved current).table = saved.table := by
  funext key
  by_cases old : key.index < saved.next
  · have h := exec_unwind_below history key old
    simpa [cancel, restrict, old, begin, unwind] using h
  · have absent : saved.table key = none := by
      cases h : saved.table key with
      | none => rfl
      | some cell => exact False.elim (old (well.bounded key cell h))
    simp [cancel, restrict, old, absent]

theorem checked_cancel_exact {saved current : State α} {events : List (Event α)}
    (well : WellFormed saved) (checked : run (begin saved) events = some current) :
    (cancel saved current).table = saved.table ∧
    (cancel saved current).next = saved.next ∧
    (cancel saved current).clock = current.clock := by
  exact ⟨cancel_table_exact well (checked_run checked), rfl, rfl⟩

theorem cancel_wellFormed {saved current : State α} {events : List (Event α)}
    (well : WellFormed saved) (history : Exec (begin saved) events current) :
    WellFormed (cancel saved current) := by
  have table := cancel_table_exact well history
  have time : saved.clock ≤ current.clock := (exec_monotone history).2
  constructor
  · intro key cell found
    rw [table] at found
    exact well.bounded key cell found
  · intro key cell found
    rw [table] at found
    exact Nat.lt_of_lt_of_le (well.stamped key cell found) time

inductive Route : State α → State α → Prop
  | commit {saved current : State α} {events : List (Event α)} :
      Exec (begin saved) events current → Route saved (commit current)
  | cancel {saved current : State α} {events : List (Event α)} :
      Exec (begin saved) events current → Route saved (cancel saved current)

inductive History : State α → Prop
  | empty : History empty
  | route {s t : State α} : History s → Route s t → History t

theorem history_wellFormed {s : State α} (history : History s) : WellFormed s := by
  induction history with
  | empty => exact empty_wellFormed
  | route earlier route ih =>
      cases route with
      | commit h => exact commit_wellFormed (exec_wellFormed (begin_wellFormed ih) h)
      | cancel h => exact cancel_wellFormed ih h

theorem route_clock_monotone {s t : State α} (route : Route s t) : s.clock ≤ t.clock := by
  cases route with
  | commit h => exact (exec_monotone h).2
  | cancel h => exact (exec_monotone h).2

theorem fresh_at_frontier {s : State α} (well : WellFormed s) (lane : Nat) :
    s.table ⟨lane, s.next⟩ = none := by
  cases h : s.table ⟨lane, s.next⟩ with
  | none => rfl
  | some cell => have := well.bounded _ cell h; simp at this

theorem allocation_checked {s : State α} (well : WellFormed s) (lane : Nat) (value : α) :
    step s (.allocate lane value) = some (allocate s lane value) := by
  simp [step, fresh_at_frontier well lane]

/-- The ghost birth is not the rewound native numeric operation ID. -/
theorem cancelled_allocation_not_reused {saved current : State α} {lane : Nat} {value : α}
    {events : List (Event α)}
    (tail : Exec (allocate (begin saved) lane value) events current) :
    (cancel saved current).next = saved.next ∧
    saved.clock < (cancel saved current).clock ∧
    (allocate (begin (cancel saved current)) lane value).table ⟨lane, saved.next⟩ =
      some ⟨current.clock, value⟩ := by
  have m := (exec_monotone tail).2
  constructor
  · rfl
  constructor
  · simp only [allocate, begin] at m
    change saved.clock < current.clock
    omega
  · simp [allocate, begin, cancel]

theorem current_birth_precedes_retry {saved current : State α} {key : Address} {cell : Cell α}
    {events : List (Event α)} (well : WellFormed saved)
    (history : Exec (begin saved) events current) (found : saved.table key = some cell) :
    cell.birth < (cancel saved current).clock := by
  exact Nat.lt_of_lt_of_le (well.stamped key cell found) (exec_monotone history).2

theorem cancelled_history_preserves_joint_predicate {saved current : State α}
    {events : List (Event α)} (well : WellFormed saved)
    (history : Exec (begin saved) events current) (P : Table α → Prop) :
    P (cancel saved current).table ↔ P saved.table := by
  rw [cancel_table_exact well history]

theorem unwind_filter_selected (keep : Address → Bool) (key : Address)
    (selected : keep key = true) (undo : List (Undo α)) (table : Table α) :
    unwind table (undo.filter (fun entry => keep entry.key)) key = unwind table undo key := by
  induction undo generalizing table with
  | nil => rfl
  | cons item rest ih =>
      by_cases chosen : keep item.key = true
      · simpa [List.filter_cons, chosen, unwind] using ih (put table item.key item.before)
      · have different : key ≠ item.key := by
          intro same
          subst key
          exact chosen selected
        simp only [List.filter_cons, chosen, Bool.false_eq_true, ↓reduceIte, unwind]
        rw [ih]
        exact unwind_key_congr key (by simp [put, different]) rest

theorem unwind_filter_unselected (keep : Address → Bool) (key : Address)
    (unselected : keep key = false) (undo : List (Undo α)) (table : Table α) :
    unwind table (undo.filter (fun entry => keep entry.key)) key = table key := by
  induction undo generalizing table with
  | nil => rfl
  | cons item rest ih =>
      by_cases chosen : keep item.key = true
      · have different : key ≠ item.key := by
          intro same
          subst key
          simp [chosen] at unselected
        simp only [List.filter_cons, chosen, ↓reduceIte, unwind]
        rw [ih]
        simp [put, different]
      · simpa [List.filter_cons, chosen] using ih table

/-- Native rollback drains restoration and replay undo vectors separately.
Partitioning one chronological undo list by owner lane yields the same table. -/
theorem partitioned_unwind (keep : Address → Bool) (undo : List (Undo α)) (table : Table α) :
    unwind (unwind table (undo.filter (fun entry => keep entry.key)))
      (undo.filter (fun entry => !(keep entry.key))) = unwind table undo := by
  funext key
  cases selected : keep key with
  | false =>
      rw [unwind_filter_selected (fun address => !(keep address)) key (by simp [selected])]
      apply unwind_key_congr
      exact unwind_filter_unselected keep key selected undo table
  | true =>
      rw [unwind_filter_unselected (fun address => !(keep address)) key (by simp [selected])]
      exact unwind_filter_selected keep key selected undo table

theorem partitioned_cancel_exact {saved current : State α} {events : List (Event α)}
    (well : WellFormed saved) (history : Exec (begin saved) events current)
    (restorationLane : Address → Bool) :
    restrict saved.next
      (unwind (unwind current.table (current.undo.filter (fun entry => restorationLane entry.key)))
        (current.undo.filter (fun entry => !(restorationLane entry.key)))) = saved.table := by
  rw [partitioned_unwind]
  exact cancel_table_exact well history

structure Transaction (α : Type) where
  events : List (Event α)
  accepted : Bool

def executeRoute (saved : State α) (transaction : Transaction α) : Option (State α) := do
  let current ← run (begin saved) transaction.events
  return if transaction.accepted then commit current else cancel saved current

def executeHistory (saved : State α) : List (Transaction α) → Option (State α)
  | [] => some saved
  | transaction :: rest => (executeRoute saved transaction).bind (fun next => executeHistory next rest)

theorem checked_route {saved final : State α} {transaction : Transaction α}
    (checked : executeRoute saved transaction = some final) : Route saved final := by
  cases h : run (begin saved) transaction.events with
  | none => simp [executeRoute, h] at checked
  | some current =>
      cases accepted : transaction.accepted with
      | false =>
          simp [executeRoute, h, accepted] at checked
          subst final
          exact .cancel (checked_run h)
      | true =>
          simp [executeRoute, h, accepted] at checked
          subst final
          exact .commit (checked_run h)

theorem checked_history_from {saved final : State α} {transactions : List (Transaction α)}
    (prior : History saved) (checked : executeHistory saved transactions = some final) :
    History final := by
  induction transactions generalizing saved with
  | nil => simp [executeHistory] at checked; subst final; exact prior
  | cons transaction rest ih =>
      cases h : executeRoute saved transaction with
      | none => simp [executeHistory, h] at checked
      | some next =>
          exact ih (.route prior (checked_route h)) (by simpa [executeHistory, h] using checked)

/-- All old-owner bounds and birth separation follow from this computed history,
not independently supplied certificates for favorable final snapshots. -/
theorem checked_history {final : State α} {transactions : List (Transaction α)}
    (checked : executeHistory empty transactions = some final) :
    History final ∧ WellFormed final := by
  have h := checked_history_from .empty checked
  exact ⟨h, history_wellFormed h⟩

theorem history_cancel_joint {saved current : State α} {events : List (Event α)}
    (prior : History saved) (checked : run (begin saved) events = some current) :
    History (cancel saved current) ∧ (cancel saved current).table = saved.table :=
  ⟨.route prior (.cancel (checked_run checked)),
    cancel_table_exact (history_wellFormed prior) (checked_run checked)⟩

namespace Witness

def original : State Nat := commit (allocate (allocate (begin empty) 0 10) 1 20)

def attempted : State Nat :=
  update
    (update
      (update
        (allocate (update (begin original) ⟨0, 0⟩ ⟨0, 10⟩ 11) 0 30)
        ⟨1, 1⟩ ⟨1, 20⟩ 21)
      ⟨0, 0⟩ ⟨0, 11⟩ 12)
    ⟨0, 2⟩ ⟨2, 30⟩ 31

def finished : State Nat := commit (allocate (begin (cancel original attempted)) 0 40)

def transactions : List (Transaction Nat) := [
  ⟨[.allocate 0 10, .allocate 1 20], true⟩,
  ⟨[.update ⟨0, 0⟩ 11, .allocate 0 30, .update ⟨1, 1⟩ 21,
     .update ⟨0, 0⟩ 12, .update ⟨0, 2⟩ 31], false⟩,
  ⟨[.allocate 0 40], true⟩]

theorem interleaved_history_computes : executeHistory empty transactions = some finished := rfl

theorem interleaved_history_valid : History finished ∧ WellFormed finished :=
  checked_history interleaved_history_computes

theorem both_old_owners_restored :
    finished.table ⟨0, 0⟩ = some ⟨0, 10⟩ ∧ finished.table ⟨1, 1⟩ = some ⟨1, 20⟩ := by
  constructor <;> rfl

theorem cancelled_slot_reused_with_new_birth :
    attempted.table ⟨0, 2⟩ = some ⟨2, 31⟩ ∧
    finished.table ⟨0, 2⟩ = some ⟨3, 40⟩ ∧ finished.clock = 4 := by
  exact ⟨rfl, rfl, rfl⟩

def preflightAttempt : State Nat :=
  mutate (mutate (prepare (prepare (begin original) ⟨0, 0⟩) ⟨0, 0⟩)
    ⟨0, 0⟩ ⟨0, 10⟩ 11) ⟨0, 0⟩ ⟨0, 11⟩ 12

theorem preflight_computes :
    run (begin original) [.prepare ⟨0, 0⟩, .prepare ⟨0, 0⟩,
      .mutate ⟨0, 0⟩ 11, .mutate ⟨0, 0⟩ 12] = some preflightAttempt := rfl

theorem preflight_shared_snapshots_restore :
    (cancel original preflightAttempt).table = original.table := by
  have originalWell : WellFormed original :=
    (checked_history (transactions := [⟨[.allocate 0 10, .allocate 1 20], true⟩]) rfl).2
  exact (checked_cancel_exact originalWell preflight_computes).1

theorem commit_requires_new_preflight (key : Address) :
    hasPreparation (begin (commit preflightAttempt)) key = false := rfl

end Witness

end YulangClosure.NativeExecutionHistory
