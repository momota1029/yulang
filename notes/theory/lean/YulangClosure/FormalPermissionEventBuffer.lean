import YulangClosure.FormalPermissionArenaEvents

/-! R17: a six-slot Option array and its separate length. The partial Appends
relation represents only executions whose push assertions succeed. Absence of
such an execution is not a recoverable constructor error. Actual Rust execution,
snapshot authenticity, and exclusion of interleaved writers remain external.
The structural writers in intern_structure are not assigned an event bound. -/
namespace YulangClosure.FormalPermissionEventBuffer
open FormalPermissionArenaEvents FormalPermissionTermCallControl
open FormalPermissionHelperFrames
noncomputable section

structure Buffer (α : Type) where
  snapshots : Array (Option α)
  len : Nat
  fixedSize : snapshots.size = 6

def empty {α : Type} : Buffer α := ⟨Array.replicate 6 none, 0, by simp⟩

/-- Exact ordered occupied prefix, with every unused slot empty. -/
structure Layout {α : Type} (b : Buffer α) (xs : List α) : Prop where
  len_eq : b.len = xs.length
  bounded : xs.length ≤ 6
  slots_eq : b.snapshots.toList = xs.map some ++ List.replicate (6 - xs.length) none

/-- Under the assertion, setIfInBounds is an actual write at len. -/
def push {α : Type} (b : Buffer α) (x : α) (_free : b.len < 6) : Buffer α :=
  ⟨b.snapshots.setIfInBounds b.len (some x), b.len + 1, by simpa using b.fixedSize⟩

theorem empty_layout (α : Type) : Layout (empty : Buffer α) [] := by
  constructor <;> simp [empty]

private theorem set_padding {α : Type} (xs : List α) (n : Nat) (x : α) :
    (xs.map some ++ none :: List.replicate n none).set xs.length (some x) =
      (xs ++ [x]).map some ++ List.replicate n none := by
  induction xs with
  | nil => simp
  | cons a xs ih => simpa using congrArg (List.cons (some a)) ih

theorem push_layout {α : Type} (b : Buffer α) (xs : List α) (x : α)
    (layout : Layout b xs) (free : b.len < 6) :
    Layout (push b x free) (xs ++ [x]) := by
  have lt : xs.length < 6 := by rw [← layout.len_eq]; exact free
  have pad : 6 - xs.length = (6 - (xs.length + 1)) + 1 := by omega
  constructor
  · simp [push, layout.len_eq]
  · simp only [List.length_append, List.length_singleton]; omega
  · change (b.snapshots.setIfInBounds b.len (some x)).toList = _
    rw [Array.toList_setIfInBounds, layout.slots_eq, layout.len_eq, pad,
      List.replicate_succ]
    simpa using set_padding xs (6 - (xs.length + 1)) x

theorem push_writes_next {α : Type} (b : Buffer α) (x : α) (free : b.len < 6) :
    (push b x free).snapshots[b.len]? = some (some x) := by
  have lt : b.len < b.snapshots.size := by rw [b.fixedSize]; exact free
  exact Array.getElem?_setIfInBounds_self_of_lt lt

/-- Replace the entire structure, retaining the old array independently. -/
def take {α : Type} (b : Buffer α) : Buffer α × Buffer α := (b, empty)

def flatten {α : Type} (b : Buffer α) : List α := b.snapshots.toList.filterMap id

private theorem flatten_occupied {α : Type} (xs : List α) (n : Nat) :
    (xs.map some ++ List.replicate n none).filterMap id = xs := by
  induction xs with
  | nil => simp
  | cons a xs ih => simpa using congrArg (List.cons a) ih

theorem flatten_exact {α : Type} (b : Buffer α) (xs : List α)
    (layout : Layout b xs) : flatten b = xs := by
  unfold flatten
  rw [layout.slots_eq]
  exact flatten_occupied xs (6 - xs.length)

theorem take_exact_reset {α : Type} (b : Buffer α) :
    (take b).1 = b ∧ (take b).2 = empty ∧
    (take b).2.len = 0 ∧
    (take b).2.snapshots.toList = List.replicate 6 none := by
  simp [take, empty]

def takeEvents {α : Type} (b : Buffer α) : List α × Buffer α :=
  (flatten (take b).1, (take b).2)

theorem take_events_exact {α : Type} (b : Buffer α) (xs : List α)
    (layout : Layout b xs) : takeEvents b = (xs, empty) := by
  change (flatten b, empty) = (xs, empty)
  rw [flatten_exact b xs layout]

/-- A finite normal sequence of bounded pushes, preserving arbitrary prefixes. -/
inductive Appends {α : Type} : Buffer α → List α → Buffer α → Prop where
  | nil (b : Buffer α) : Appends b [] b
  | cons (b : Buffer α) (x : α) (xs : List α) (last : Buffer α)
      (free : b.len < 6) (rest : Appends (push b x free) xs last) :
      Appends b (x :: xs) last

theorem appends_layout {α : Type} (b last : Buffer α) (xs : List α)
    (execution : Appends b xs last) (old : List α) (layout : Layout b old) :
    Layout last (old ++ xs) := by
  induction execution generalizing old with
  | nil b => simpa using layout
  | cons b x xs last free rest ih =>
      have next := ih (old ++ [x]) (push_layout b old x layout free)
      simpa [List.append_assoc] using next

theorem appends_exists {α : Type} (b : Buffer α) (old xs : List α)
    (layout : Layout b old) (fits : old.length + xs.length ≤ 6) :
    ∃ last, Appends b xs last := by
  induction xs generalizing b old with
  | nil => exact ⟨b, .nil b⟩
  | cons x xs ih =>
      have free : b.len < 6 := by
        rw [layout.len_eq]
        simp only [List.length_cons] at fits
        omega
      have nextLayout := push_layout b old x layout free
      have nextFits : (old ++ [x]).length + xs.length ≤ 6 := by
        simp only [List.length_append, List.length_singleton]
        simp only [List.length_cons] at fits
        omega
      obtain ⟨last, h⟩ := ih (push b x free) (old ++ [x]) nextLayout nextFits
      exact ⟨last, .cons b x xs last free h⟩

theorem appended_empty_fits (i : Input) : Fits [] i := by
  simpa [Fits] using appended_bound i

/-- R16's bound is used only at the selected empty entry. -/
theorem selected_empty_execution (i : Input) :
    ∃ last : Buffer EventOutcome,
      Appends empty ((appended i).map Event.observation) last ∧
      Layout last ((appended i).map Event.observation) := by
  have bound : ([] : List EventOutcome).length +
      ((appended i).map Event.observation).length ≤ 6 := by
    simpa using appended_bound i
  obtain ⟨last, execution⟩ := appends_exists empty []
    ((appended i).map Event.observation) (empty_layout EventOutcome) bound
  exact ⟨last, execution, by
    simpa using appends_layout empty last _ execution [] (empty_layout EventOutcome)⟩

/-- Continue after a normally returned constructor (whose Result may be Err).
The buffer is taken before inherited sampling and result mapping. Those calls
have no Buffer parameter and cannot append to it; this is the selected source
path's no-direct-mutation condition, not a claim about arbitrary callbacks. -/
def finish (b : Buffer EventOutcome) (constructor : ConstructorOutcome)
    (accounting : Bool) (errorMap : Nat → Nat) (s : HelperState) :
    (Except Nat Nat × HelperState) × Buffer EventOutcome :=
  let drained := takeEvents b
  ((controlResult errorMap constructor drained.1 accounting,
    controlState constructor drained.1 accounting s), drained.2)

theorem finish_exact (b : Buffer EventOutcome) (xs : List EventOutcome)
    (layout : Layout b xs) (constructor : ConstructorOutcome)
    (accounting : Bool) (errorMap : Nat → Nat) (s : HelperState) :
    finish b constructor accounting errorMap s =
      ((controlResult errorMap constructor xs accounting,
        controlState constructor xs accounting s), empty) := by
  unfold finish
  rw [take_events_exact b xs layout]

theorem finish_empty (b : Buffer EventOutcome) (constructor : ConstructorOutcome)
    (accounting : Bool) (errorMap : Nat → Nat) (s : HelperState) :
    (finish b constructor accounting errorMap s).2 = empty := rfl

theorem finish_constructor_error (b : Buffer EventOutcome) (xs : List EventOutcome)
    (layout : Layout b xs) (constructor : ConstructorOutcome)
    (accounting : Bool) (errorMap : Nat → Nat) (s : HelperState) (error : Nat)
    (failed : constructor.result = .error error) (samplesOk : AllSamplesOk xs) :
    (finish b constructor accounting errorMap s).1.1 = .error (errorMap error) ∧
    (finish b constructor accounting errorMap s).2 = empty := by
  rw [finish_exact b xs layout constructor accounting errorMap s]
  exact ⟨constructor_error_preserved errorMap constructor xs accounting error failed samplesOk, rfl⟩

theorem finish_sampler_error (b : Buffer EventOutcome) (before after : List EventOutcome)
    (event : EventOutcome) (layout : Layout b (before ++ event :: after))
    (constructor : ConstructorOutcome) (errorMap : Nat → Nat) (s : HelperState)
    (error : Nat) (samplesOk : AllSamplesOk before) (failed : event.result = .error error) :
    (finish b constructor true errorMap s).1.1 = .error error ∧
    (finish b constructor true errorMap s).2 = empty := by
  rw [finish_exact b (before ++ event :: after) layout constructor true errorMap s]
  exact ⟨sample_error_precedence errorMap constructor before after event error samplesOk failed, rfl⟩

/-- Arbitrary valid old prefixes are retained in order; Fits is indispensable. -/
theorem selected_prefix_finish (b last : Buffer EventOutcome) (old : List EventOutcome)
    (i : Input) (layout : Layout b old)
    (execution : Appends b ((appended i).map Event.observation) last)
    (constructor : ConstructorOutcome) (accounting : Bool)
    (errorMap : Nat → Nat) (s : HelperState) :
    finish last constructor accounting errorMap s =
      ((controlResult errorMap constructor (events old i) accounting,
        controlState constructor (events old i) accounting s), empty) := by
  exact finish_exact last (events old i)
    (appends_layout b last _ execution old layout) constructor accounting errorMap s

/-- The next entry is the actual returned buffer when no writer intervenes.
Both Result error classes are admitted; pre-drain panics have no finish call. -/
theorem consecutive_selected_entry (b : Buffer EventOutcome)
    (constructor : ConstructorOutcome) (accounting : Bool) (errorMap : Nat → Nat)
    (s : HelperState) (next : Buffer EventOutcome)
    (noInterleavedMutation : next = (finish b constructor accounting errorMap s).2)
    (i : Input) :
    Layout next [] ∧ Fits [] i ∧
    ∃ last, Appends next ((appended i).map Event.observation) last ∧
      Layout last ((appended i).map Event.observation) := by
  have eq : next = empty := noInterleavedMutation.trans
    (finish_empty b constructor accounting errorMap s)
  subst next
  exact ⟨empty_layout EventOutcome, appended_empty_fits i, selected_empty_execution i⟩

/-- Apply the concrete ordered buffer drain to R15's control refinement. -/
theorem selected_control_refines (b last : Buffer EventOutcome) (old : List EventOutcome)
    (i : Input) (layout : Layout b old)
    (execution : Appends b ((appended i).map Event.observation) last)
    (constructor : ConstructorOutcome) (accounting : Bool) (s : HelperState) :
    runOps (controlOps constructor (takeEvents last).1 accounting s) s =
      controlState constructor (events old i) accounting s := by
  have drain := take_events_exact last (events old i)
    (appends_layout b last _ execution old layout)
  rw [drain]
  exact derived_control_refines old i constructor accounting s

end
end YulangClosure.FormalPermissionEventBuffer
