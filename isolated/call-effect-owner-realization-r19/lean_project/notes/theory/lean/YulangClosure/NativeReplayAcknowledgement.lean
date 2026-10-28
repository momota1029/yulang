import Std

/-!
Replay cursor and terminal-owner PROJECTION of candidate_context.rs and lib.rs.
This is not a whole native execution refinement. In particular, `completed`
pair admission, semantic child closure, representative/context transport, and
the cross-map worklist/journal correspondence are not defined as cursor facts.
The ghost preparation list records actual successful preflight events; it is
never supplied as an initial valid-acknowledgement hypothesis.
-/
namespace YulangClosure.NativeReplayAcknowledgement

structure Ack where
  operation : Nat
  index : Nat
  deriving DecidableEq, Repr

inductive Wait where
  | idle
  | running (ack : Ack) (drain : Nat)
  | ready (ack : Ack) (drain transitions : Nat)
  deriving DecidableEq, Repr

/-- Exactly the mutable ReplayOperation cursor fields saved in its undo record. -/
structure NativeState where
  queued : Nat
  consumed : Nat
  retired : Bool
  waiting : Wait
  deriving DecidableEq, Repr

/-- Birth is erased ghost identity, distinct from the reusable numeric runtime ID. -/
structure ChildIdentity where
  birth : Nat
  operation : Nat
  index : Nat
  deriving DecidableEq, Repr

def identity (birth operation index : Nat) : ChildIdentity := ⟨birth, operation, index⟩

structure Projection where
  native : NativeState
  present : Bool
  prepared : List Nat
  transfers : List Nat
  acknowledgements : List Nat
  deriving DecidableEq, Repr

def initial : Projection := ⟨⟨0, 0, false, .idle⟩, true, [], [], []⟩

/-- Operation-map erasure; reclaimed cursor data survives only in proof history. -/
def readback (s : Projection) : Option NativeState := if s.present then some s.native else none

def CompletionWait (operation i : Nat) (s : NativeState) : Prop :=
  s.waiting = .idle ∨ ∃ d, s.waiting = .running ⟨operation, i⟩ d ∧ s.queued = i + 1

structure Restoration where
  retired : Bool
  replay : Option Nat

def RestorationHeld (operation : Nat) (parent : Option Nat) (owners : Nat → Option Restoration) : Prop :=
  ∃ p r, parent = some p ∧ owners p = some r ∧ r.retired = false ∧ r.replay = some operation

def WaitExact (operation size : Nat) (s : NativeState) : Prop :=
  match s.waiting with
  | .idle => True
  | .running a _ => a.operation = operation ∧ a.index < size ∧
      s.queued = a.index + 1 ∧ (s.consumed = a.index ∨ s.consumed = a.index + 1)
  | .ready a _ _ => a.operation = operation ∧ a.index < size ∧
      s.queued = a.index + 1 ∧ s.consumed = a.index + 1

inductive Event where
  | transfer (ack : Ack) (fresh : Bool)
  | start (ack : Ack) (drain : Nat)
  | prepare (ack : Ack)
  | acknowledge (ack : Ack)
  | noChild
  | returnReady (ack : Ack) (drain transitions : Nat)
  | delivered (ack : Ack) (drain : Nat)
  | cancelOwnedDrain (drain : Nat)
  | commit
  | reclaim
  deriving DecidableEq, Repr

/-- Actual field writes; successful synchronous start includes enqueue's transfer.
`prepare` is separate from completion, as it is in the native Transport/terminal
owners. The retained preparation witness may be older than the completion.
Failures before a field write are stuttering steps and need no constructor. -/
inductive Step (operation : Nat) (children : List Nat) : Projection → Event → Projection → Prop
  | transferNew (s : Projection) (alive : s.present = true)
      (idle : s.native.waiting = .idle) (live : s.native.retired = false)
      (bound : s.native.queued < children.length) :
      Step operation children s (.transfer ⟨operation, s.native.queued⟩ true)
        { s with
          native := { s.native with queued := s.native.queued + 1 }
          transfers := s.transfers ++ [s.native.queued] }
  | transferOld (s : Projection) (i : Nat) (alive : s.present = true)
      (idle : s.native.waiting = .idle) (live : s.native.retired = false)
      (lower : s.native.consumed ≤ i) (upper : i < s.native.queued)
      (bound : i < children.length) :
      Step operation children s (.transfer ⟨operation, i⟩ false) s
  | start (s : Projection) (d : Nat) (alive : s.present = true)
      (idle : s.native.waiting = .idle) (live : s.native.retired = false)
      (equal : s.native.queued = s.native.consumed)
      (bound : s.native.consumed < children.length) :
      Step operation children s (.start ⟨operation, s.native.consumed⟩ d)
        { s with
          native := { s.native with
            queued := s.native.queued + 1
            waiting := .running ⟨operation, s.native.consumed⟩ d }
          transfers := s.transfers ++ [s.native.queued] }
  | prepare (s : Projection) (i : Nat) (alive : s.present = true)
      (lower : s.native.consumed ≤ i) (upper : i < s.native.queued)
      (wait : CompletionWait operation i s.native) :
      Step operation children s (.prepare ⟨operation, i⟩)
        { s with prepared := i :: s.prepared }
  | acknowledge (s : Projection) (i : Nat) (alive : s.present = true)
      (prepared : i ∈ s.prepared) (ordered : s.native.consumed = i)
      (wait : CompletionWait operation i s.native) :
      Step operation children s (.acknowledge ⟨operation, i⟩)
        { s with
          native := { s.native with
            consumed := i + 1
            retired := s.native.retired || decide (i + 1 = children.length) }
          acknowledgements := s.acknowledgements ++ [i] }
  | noChild (s : Projection) (alive : s.present = true)
      (idle : s.native.waiting = .idle) (equal : s.native.queued = s.native.consumed)
      (absent : children.length ≤ s.native.consumed) :
      Step operation children s .noChild { s with native := { s.native with retired := true } }
  | returnReady (s : Projection) (a : Ack) (d t : Nat) (alive : s.present = true)
      (owner : a.operation = operation)
      (waiting : s.native.waiting = .running a d)
      (consumed : s.native.consumed = a.index + 1)
      (queued : s.native.queued = a.index + 1) :
      Step operation children s (.returnReady a d t)
        { s with native := { s.native with waiting := .ready a d t } }
  | delivered (s : Projection) (a : Ack) (d t : Nat) (alive : s.present = true)
      (owner : a.operation = operation)
      (waiting : s.native.waiting = .ready a d t)
      (consumed : s.native.consumed = a.index + 1)
      (queued : s.native.queued = a.index + 1)
      (stackLength : Nat) (popped : stackLength = d) :
      Step operation children s (.delivered a d) { s with native := { s.native with waiting := .idle } }
  | cancelOwnedDrain (s : Projection) (a : Ack) (d : Nat)
      (alive : s.present = true) (waiting : s.native.waiting = .running a d) :
      Step operation children s (.cancelOwnedDrain d) { s with native := { s.native with waiting := .idle } }
  | commit (s : Projection) :
      Step operation children s .commit { s with prepared := [] }
  | reclaim (s : Projection) (alive : s.present = true)
      (retired : s.native.retired = true) (idle : s.native.waiting = .idle)
      (parent : Option Nat) (owners : Nat → Option Restoration)
      (released : ¬ RestorationHeld operation parent owners) :
      Step operation children s .reclaim { s with present := false }

structure Accounting (operation size : Nat) (s : Projection) : Prop where
  consumed_le_queued : s.native.consumed ≤ s.native.queued
  queued_le_size : s.native.queued ≤ size
  retired_complete : s.native.retired = true → s.native.consumed = size
  waiting_exact : WaitExact operation size s.native
  preparation_bound : ∀ i ∈ s.prepared, i < s.native.queued
  transfers_exact : s.transfers = List.range s.native.queued
  acknowledgements_exact : s.acknowledgements = List.range s.native.consumed

theorem initial_accounting (operation size : Nat) : Accounting operation size initial := by
  constructor <;> simp [initial, WaitExact]

theorem step_preserves {operation : Nat} {children : List Nat} {s u : Projection} {e : Event}
    (h : Step operation children s e u) (inv : Accounting operation children.length s) :
    Accounting operation children.length u := by
  rcases inv with ⟨hcq, hqn, hr, hw, hp, ht, ha⟩
  cases h with
  | transferNew alive idle live bound =>
      refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_, ha⟩
      · simpa using hr
      · simp [WaitExact, idle]
      · intro i hi; have := hp i hi; simp; omega
      · simpa [List.range_succ] using congrArg (· ++ [s.native.queued]) ht
  | transferOld => exact ⟨hcq, hqn, hr, hw, hp, ht, ha⟩
  | start d alive idle live equal bound =>
      refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_, ha⟩
      · simpa using hr
      · simp [WaitExact, equal, bound]
      · intro i hi; have := hp i hi; simp; omega
      · simpa [List.range_succ] using congrArg (· ++ [s.native.queued]) ht
  | prepare i alive lower upper wait =>
      refine ⟨hcq, hqn, hr, hw, ?_, ht, ha⟩
      intro j hj
      simp only [List.mem_cons] at hj
      rcases hj with rfl | hj
      · exact upper
      · exact hp j hj
  | acknowledge i alive prepared ordered wait =>
      have hiq := hp i prepared
      have hin : i + 1 ≤ children.length := by omega
      refine ⟨by simp; omega, hqn, ?_, ?_, hp, ht, ?_⟩
      · simp only [Bool.or_eq_true, decide_eq_true_eq]
        intro h
        rcases h with h | h
        · have := hr h; omega
        · exact h
      · rcases wait with idle | ⟨d, running, queued⟩
        · simp [WaitExact, idle]
        · simp [WaitExact, running, queued]; omega
      · simpa [List.range_succ, ordered] using congrArg (· ++ [i]) ha
  | noChild alive idle equal absent =>
      exact ⟨hcq, hqn, by intro _; change s.native.consumed = children.length; omega,
        by simp [WaitExact, idle], hp, ht, ha⟩
  | returnReady a d t alive owner waiting consumed queued =>
      have hx : a.index < children.length := by omega
      exact ⟨hcq, hqn, hr, by simp [WaitExact, owner, hx, consumed, queued], hp, ht, ha⟩
  | delivered => exact ⟨hcq, hqn, hr, by simp [WaitExact], hp, ht, ha⟩
  | cancelOwnedDrain => exact ⟨hcq, hqn, hr, by simp [WaitExact], hp, ht, ha⟩
  | commit => exact ⟨hcq, hqn, hr, hw, by simp, ht, ha⟩
  | reclaim => exact ⟨hcq, hqn, hr, hw, hp, ht, ha⟩

inductive Exec (operation : Nat) (children : List Nat) : Projection → List Event → Projection → Prop
  | nil (s) : Exec operation children s [] s
  | snoc {s u v es e} : Exec operation children s es u → Step operation children u e v →
      Exec operation children s (es ++ [e]) v

def Reachable (operation : Nat) (children : List Nat) (s : Projection) : Prop :=
  ∃ es, Exec operation children initial es s

theorem exec_preserves {operation : Nat} {children : List Nat} {s u : Projection} {es : List Event}
    (h : Exec operation children s es u) (inv : Accounting operation children.length s) :
    Accounting operation children.length u := by
  induction h with
  | nil => exact inv
  | snoc _ step ih => exact step_preserves step ih

/-- No accounting law or valid-ack list is a premise: initialization plus steps suffice. -/
theorem cursor_projection_accounting {operation : Nat} {children : List Nat} {s : Projection}
    (h : Reachable operation children s) : Accounting operation children.length s := by
  obtain ⟨es, h⟩ := h
  exact exec_preserves h (initial_accounting operation children.length)

theorem cursor_projection_ack_order {operation : Nat} {children : List Nat} {s : Projection}
    (h : Reachable operation children s) :
    s.acknowledgements = List.range s.native.consumed ∧
      s.transfers = List.range s.native.queued ∧ s.native.consumed ≤ s.native.queued ∧
      s.native.queued ≤ children.length := by
  have inv := cursor_projection_accounting h
  exact ⟨inv.acknowledgements_exact, inv.transfers_exact,
    inv.consumed_le_queued, inv.queued_le_size⟩

theorem acknowledgement_position_exact {operation : Nat} {children : List Nat} {s : Projection}
    (h : Reachable operation children s) {i : Nat} (hi : i < s.native.consumed) :
    s.acknowledgements[i]? = some i := by
  rw [(cursor_projection_accounting h).acknowledgements_exact]
  exact List.getElem?_range hi

theorem acknowledgements_unique {operation : Nat} {children : List Nat} {s : Projection}
    (h : Reachable operation children s) : s.acknowledgements.Nodup := by
  rw [(cursor_projection_accounting h).acknowledgements_exact]
  exact List.nodup_range

theorem acknowledged_child_readback {operation : Nat} {children : List Nat} {s : Projection}
    (h : Reachable operation children s) {i : Nat} (hi : i < s.native.consumed) :
    ∃ relation, children[i]? = some relation := by
  have inv := cursor_projection_accounting h
  have bound : i < children.length := by have := inv.consumed_le_queued; have := inv.queued_le_size; omega
  exact ⟨children[i], List.getElem?_eq_getElem bound⟩

theorem occurrence_identity_injective (birth operation i j : Nat) :
    identity birth operation i = identity birth operation j ↔ i = j := by
  simp [identity, ChildIdentity.mk.injEq]

theorem numeric_reuse_distinct (birth₁ birth₂ operation i j : Nat) (h : birth₁ ≠ birth₂) :
    identity birth₁ operation i ≠ identity birth₂ operation j := by
  simp [identity, ChildIdentity.mk.injEq, h]

theorem ready_owner_exact {operation : Nat} {children : List Nat} {s : Projection}
    (h : Reachable operation children s) {a : Ack} {d t : Nat}
    (ready : s.native.waiting = .ready a d t) :
    a.operation = operation ∧ a.index < children.length ∧
      s.native.queued = a.index + 1 ∧ s.native.consumed = a.index + 1 := by
  have hw := (cursor_projection_accounting h).waiting_exact
  simpa [WaitExact, ready] using hw

theorem running_before_or_after_ack {operation : Nat} {children : List Nat} {s : Projection}
    (h : Reachable operation children s) {a : Ack} {d : Nat}
    (running : s.native.waiting = .running a d) :
    a.operation = operation ∧ a.index < children.length ∧ s.native.queued = a.index + 1 ∧
      (s.native.consumed = a.index ∨ s.native.consumed = a.index + 1) := by
  have hw := (cursor_projection_accounting h).waiting_exact
  simpa [WaitExact, running] using hw

/-- Readback of candidate_context_replay_returned, not a semantic child judgment. -/
def Returned (s : Projection) : Prop := s.native.retired = true ∧ s.native.waiting = .idle
def QueuedOutcome (children : List Nat) (s : Projection) : Prop :=
  s.native.waiting = .idle ∧ s.native.queued = children.length ∧ s.native.consumed < children.length

theorem queued_is_not_returned {operation : Nat} {children : List Nat} {s : Projection}
    (h : Reachable operation children s) (q : QueuedOutcome children s) : ¬ Returned s := by
  intro r
  have := (cursor_projection_accounting h).retired_complete r.1
  have := q.2.2
  omega

theorem delivered_does_not_acknowledge {operation : Nat} {children : List Nat}
    {s u : Projection} {a : Ack} {d : Nat} (h : Step operation children s (.delivered a d) u) :
    u.native.consumed = s.native.consumed ∧ u.acknowledgements = s.acknowledgements := by
  cases h
  exact ⟨rfl, rfl⟩

theorem commit_preserves_cursor {operation : Nat} {children : List Nat}
    {s u : Projection} (h : Step operation children s .commit u) :
    u.native = s.native ∧ u.acknowledgements = s.acknowledgements ∧ u.prepared = [] := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem reclamation_preserves_erased_history {operation : Nat} {children : List Nat}
    {s u : Projection} (h : Step operation children s .reclaim u) :
    readback u = none ∧ u.acknowledgements = s.acknowledgements ∧ u.native = s.native := by
  cases h
  exact ⟨rfl, rfl, rfl⟩

theorem returnReady_exact_event {operation : Nat} {children : List Nat}
    {s u : Projection} {a : Ack} {d t : Nat}
    (h : Step operation children s (.returnReady a d t) u) :
    s.native.waiting = .running a d ∧ u.native.waiting = .ready a d t ∧
      s.native.consumed = a.index + 1 ∧ s.native.queued = a.index + 1 := by
  cases h
  exact ⟨by assumption, rfl, by assumption, by assumption⟩

/-- Actual retention guard; the supplied map must still be tied to native readback. -/
def Reclaimable (operation : Nat) (parent : Option Nat) (owners : Nat → Option Restoration)
    (s : NativeState) : Prop :=
  s.retired = true ∧ s.waiting = .idle ∧ ¬ RestorationHeld operation parent owners

theorem running_not_reclaimable (operation : Nat) (parent : Option Nat)
    (owners : Nat → Option Restoration) (s : NativeState) (a : Ack) (d : Nat)
    (h : s.waiting = .running a d) : ¬ Reclaimable operation parent owners s := by
  intro reclaim
  have heq := reclaim.2.1
  rw [h] at heq
  cases heq

/-- Newest-first readback of the native undo records traversed in reverse. -/
def restoreCursor : NativeState → List NativeState → NativeState
  | current, [] => current
  | _, saved :: rest => restoreCursor saved rest

inductive Journaled (operation : Nat) (children : List Nat) :
    Projection → List NativeState → Projection → Prop
  | nil (s) : Journaled operation children s [] s
  | save {s u undo} : Journaled operation children s undo u →
      Journaled operation children s (u.native :: undo) u
  | write {s u v undo e} : Journaled operation children s undo u →
      Step operation children u e v →
      (e ≠ .commit ∧ e ≠ .reclaim) →
      (undo ≠ [] ∨ u.native = v.native) → Journaled operation children s undo v

theorem restoreCursor_irrelevant (a b : NativeState) (saved : NativeState) (rest : List NativeState) :
    restoreCursor a (saved :: rest) = restoreCursor b (saved :: rest) := rfl

theorem journal_restores_exact_cursor {operation : Nat} {children : List Nat}
    {s u : Projection} {undo : List NativeState} (h : Journaled operation children s undo u) :
    restoreCursor u.native undo = s.native := by
  induction h with
  | nil => rfl
  | save h ih => exact ih
  | @write u v undo e h step mode saved ih =>
      rcases saved with nonempty | unchanged
      · cases undo with
        | nil => contradiction
        | cons saved rest => exact ih
      · simpa [← unchanged] using ih

/-- Erased event histories roll back to the same checkpoint as the native tuple.
This cancels mutations of old owners, not merely newly allocated operations. -/
def cancelProjection (saved current : Projection) (undo : List NativeState) : Projection :=
  { saved with native := restoreCursor current.native undo }

theorem journal_cancel_projection_exact {operation : Nat} {children : List Nat}
    {s u : Projection} {undo : List NativeState} (h : Journaled operation children s undo u) :
    cancelProjection s u undo = s := by
  simp [cancelProjection, journal_restores_exact_cursor h]

theorem cancelled_prefix_accounting {operation : Nat} {children : List Nat}
    {s u : Projection} {undo : List NativeState} (hprefix : Reachable operation children s)
    (suffix : Journaled operation children s undo u) :
    Accounting operation children.length (cancelProjection s u undo) := by
  rw [journal_cancel_projection_exact suffix]
  exact cursor_projection_accounting hprefix

/-- Native rollback deletes new IDs; old owners restore their mutable tuples. -/
def rollbackReadback (frontier id : Nat) (current : NativeState) (undo : List NativeState) :
    Option NativeState := if id < frontier then some (restoreCursor current undo) else none

theorem rollback_existing_exact {operation frontier : Nat} {children : List Nat}
    {s u : Projection} {undo : List NativeState} (h : Journaled operation children s undo u)
    (old : operation < frontier) :
    rollbackReadback frontier operation u.native undo = some s.native := by
  simp [rollbackReadback, old, journal_restores_exact_cursor h]

theorem rollback_new_absent (frontier operation : Nat) (s : NativeState) (undo : List NativeState)
    (new : frontier ≤ operation) : rollbackReadback frontier operation s undo = none := by
  simp [rollbackReadback, Nat.not_lt.mpr new]

/-! Terminal-frame projection. `working` erases the nonterminal stages only;
it does not assert that structural children have completed. `diagnosed` and
`done` are ghost event readbacks. Stack authenticity is a separate bridge. -/
inductive TerminalStage where
  | working | diagnostics | acknowledgements | returnReady
  deriving DecidableEq, Repr

structure FrameProjection where
  acks : List Ack
  completed : Nat
  prepared : Nat
  terminalPrepared : Bool
  stage : TerminalStage
  destination : Option Ack
  index : Nat
  stackLength : Nat
  transitions : Nat
  present : Bool
  diagnosed : Bool
  done : List Ack
  deriving DecidableEq, Repr

def initialFrame (index : Nat) (destination : Option Ack) : FrameProjection :=
  ⟨[], 0, 0, false, .working, destination, index, index + 1, 0, true, false, []⟩

inductive FrameEvent where
  | takeAck (a : Ack)
  | dispatchReturn (transitions : Nat)
  | enterDiagnostics
  | diagnostics
  | preflight (a : Ack)
  | reprepare (slot : Nat) (a : Ack)
  | markTerminal (transactional : Bool)
  | complete (a : Ack)
  | emptyReady
  | pop (destination : Option Ack) (index transitions : Nat)
  | commit
  deriving DecidableEq, Repr

inductive FrameStep : FrameProjection → FrameEvent → FrameProjection → Prop
  | takeAck (f : FrameProjection) (a : Ack) (alive : f.present = true)
      (working : f.stage = .working) :
      FrameStep f (.takeAck a) { f with
        acks := f.acks ++ [a]
        prepared := f.prepared + 1 }
  | dispatchReturn (f : FrameProjection) (transitions : Nat) (alive : f.present = true)
      (working : f.stage = .working) :
      FrameStep f (.dispatchReturn transitions) { f with transitions := transitions }
  | enterDiagnostics (f : FrameProjection) (alive : f.present = true)
      (working : f.stage = .working) :
      FrameStep f .enterDiagnostics { f with stage := .diagnostics }
  | diagnostics (f : FrameProjection) (alive : f.present = true)
      (stage : f.stage = .diagnostics) :
      FrameStep f .diagnostics { f with stage := .acknowledgements, diagnosed := true }
  | preflight (f : FrameProjection) (a : Ack) (alive : f.present = true)
      (stage : f.stage = .acknowledgements) (same : f.completed = f.prepared)
      (readback : f.acks[f.completed]? = some a) (bound : f.completed < f.acks.length) :
      FrameStep f (.preflight a) { f with prepared := f.prepared + 1 }
  /-- prepare_nonterminal_drain has no stage test and reads the prepared index. -/
  | reprepare (f : FrameProjection) (a : Ack) (alive : f.present = true)
      (top : f.index + 1 = f.stackLength) (lower : f.completed ≤ f.prepared)
      (bound : f.prepared < f.acks.length) (readback : f.acks[f.prepared]? = some a) :
      FrameStep f (.reprepare f.prepared a) { f with prepared := f.prepared + 1 }
  | markTerminal (f : FrameProjection) (transactional : Bool) (alive : f.present = true)
      (stage : f.stage = .acknowledgements ∨ f.stage = .returnReady) :
      FrameStep f (.markTerminal transactional) { f with terminalPrepared := transactional }
  | complete (f : FrameProjection) (a : Ack) (alive : f.present = true)
      (stage : f.stage = .acknowledgements) (prepared : f.completed < f.prepared)
      (readback : f.acks[f.completed]? = some a) :
      FrameStep f (.complete a) { f with
        completed := f.completed + 1
        stage := if f.completed + 1 = f.acks.length then .returnReady else .acknowledgements
        done := f.done ++ [a] }
  | emptyReady (f : FrameProjection) (alive : f.present = true)
      (stage : f.stage = .acknowledgements) (complete : f.completed = f.acks.length) :
      FrameStep f .emptyReady { f with stage := .returnReady }
  | pop (f : FrameProjection) (alive : f.present = true)
      (stage : f.stage = .returnReady) (top : f.index + 1 = f.stackLength)
      (complete : f.completed = f.acks.length) :
      FrameStep f (.pop f.destination f.index f.transitions)
        { f with present := false, stackLength := f.index }
  | commit (f : FrameProjection) (alive : f.present = true) :
      FrameStep f .commit { f with prepared := f.completed, terminalPrepared := false }

structure FrameAccounting (f : FrameProjection) : Prop where
  completed_le_prepared : f.completed ≤ f.prepared
  prepared_le_length : f.prepared ≤ f.acks.length
  prefix_exact : f.done = f.acks.take f.completed
  working_zero : f.stage = .working → f.completed = 0
  ready_complete : f.stage = .returnReady → f.completed = f.acks.length
  diagnostics_first : f.stage = .acknowledgements ∨ f.stage = .returnReady → f.diagnosed = true
  popped_exact : f.present = false → f.stage = .returnReady ∧ f.completed = f.acks.length ∧
    f.stackLength = f.index

theorem initial_frame_accounting (index : Nat) (destination : Option Ack) :
    FrameAccounting (initialFrame index destination) := by
  constructor <;> simp [initialFrame]

theorem frame_step_preserves {f g : FrameProjection} {e : FrameEvent}
    (h : FrameStep f e g) (inv : FrameAccounting f) : FrameAccounting g := by
  rcases inv with ⟨hcp, hpl, hx, hz, hr, hd, hp⟩
  cases h with
  | takeAck a alive working =>
      have hc := hz working
      refine ⟨by simp; omega, by simp; omega, ?_, ?_, ?_, ?_, ?_⟩
      · simpa [hc] using hx
      · simpa using hz
      · simp [working]
      · simp [working]
      · simp [alive]
  | dispatchReturn => exact ⟨hcp, hpl, hx, hz, hr, hd, hp⟩
  | enterDiagnostics alive working =>
      exact ⟨hcp, hpl, hx, by simp, by simp, by simp, by simp [alive]⟩
  | diagnostics alive stage =>
      exact ⟨hcp, hpl, hx, by simp, by simp, by simp, by simp [alive]⟩
  | preflight a alive stage same readback bound =>
      exact ⟨by simp; omega, by simp; omega, hx, hz, hr, hd, by simp [alive]⟩
  | reprepare a alive top lower bound readback =>
      exact ⟨by simp; omega, by simp; omega, hx, hz, hr, hd, by simp [alive]⟩
  | markTerminal transactional alive stage =>
      exact ⟨hcp, hpl, hx, hz, hr, hd, hp⟩
  | complete a alive stage prepared readback =>
      have diagnosed := hd (Or.inl stage)
      refine ⟨by simp; omega, hpl, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [List.take_add_one, readback, Option.toList_some] using
          congrArg (· ++ [a]) hx
      · simp only; split <;> simp
      · simp only; split <;> simp_all
      · simp [diagnosed]
      · simp [alive]
  | emptyReady alive stage complete =>
      have diagnosed := hd (Or.inl stage)
      exact ⟨hcp, hpl, hx, by simp, by simpa using complete, by simp [diagnosed], by simp [alive]⟩
  | pop alive stage top complete =>
      exact ⟨hcp, hpl, hx, hz, hr, hd, by simp [stage, complete]⟩
  | commit => exact ⟨Nat.le_refl _, by change f.completed ≤ f.acks.length; omega, hx, hz, hr, hd, hp⟩

inductive FrameReachable (index : Nat) (destination : Option Ack) : FrameProjection → Prop
  | initial : FrameReachable index destination (initialFrame index destination)
  | step {f g e} : FrameReachable index destination f → FrameStep f e g →
      FrameReachable index destination g

theorem terminal_projection_accounting {index : Nat} {destination : Option Ack} {f : FrameProjection}
    (h : FrameReachable index destination f) : FrameAccounting f := by
  induction h with
  | initial => exact initial_frame_accounting _ _
  | step _ step ih => exact frame_step_preserves step ih

theorem terminal_projection_live_top {index : Nat} {destination : Option Ack} {f : FrameProjection}
    (h : FrameReachable index destination f) (alive : f.present = true) :
    f.stackLength = f.index + 1 := by
  induction h with
  | initial => rfl
  | step h step ih => cases step <;> simp_all

theorem terminal_projection_pop_all {index : Nat} {destination : Option Ack} {f : FrameProjection}
    (h : FrameReachable index destination f) (popped : f.present = false) :
    f.done = f.acks ∧ f.diagnosed = true ∧ f.stackLength = f.index := by
  have inv := terminal_projection_accounting h
  obtain ⟨stage, complete, stack⟩ := inv.popped_exact popped
  exact ⟨by simpa [complete] using inv.prefix_exact, inv.diagnostics_first (Or.inr stage), stack⟩

theorem terminal_commit_preserves_completed (f : FrameProjection) :
    let g := { f with prepared := f.completed, terminalPrepared := false }
    g.completed = f.completed ∧ g.done = f.done ∧ g.prepared = g.completed ∧
      g.terminalPrepared = false := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Joint projected consumer of the exact native prepare_replay_return guard.
These histories are still to be authenticated against the SAME native maps. -/
theorem terminal_cursor_projection_return {operation index : Nat} {children : List Nat}
    {s : Projection} {f : FrameProjection} {a : Ack} {destination : Option Ack}
    (cursor : Reachable operation children s) (frame : FrameReachable index destination f)
    (salive : s.present = true) (falive : f.present = true)
    (dest : f.destination = some a) (stage : f.stage = .returnReady)
    (waiting : s.native.waiting = .running a f.index)
    (consumed : s.native.consumed = a.index + 1) (queued : s.native.queued = a.index + 1) :
    ∃ u g, Step operation children s (.returnReady a f.index f.transitions) u ∧
      FrameStep f (.pop (some a) f.index f.transitions) g ∧
      Accounting operation children.length u ∧ FrameAccounting g ∧
      g.done = g.acks ∧ g.diagnosed = true ∧ g.stackLength = f.index := by
  have owner := (running_before_or_after_ack cursor waiting).1
  have fi := terminal_projection_accounting frame
  have complete := fi.ready_complete stage
  have top := terminal_projection_live_top frame falive
  have hs := Step.returnReady (children := children) s a f.index f.transitions salive owner waiting consumed queued
  have hf := FrameStep.pop f falive stage top.symm complete
  rw [dest] at hf
  refine ⟨_, _, hs, hf, step_preserves hs (cursor_projection_accounting cursor),
    frame_step_preserves hf fi, ?_, ?_, rfl⟩
  · simpa [complete] using fi.prefix_exact
  · exact fi.diagnostics_first (Or.inr stage)

structure AllocationClock where
  nextOperation : Nat
  nextBirth : Nat
  deriving DecidableEq, Repr

def advanceAllocation (c : AllocationClock) : AllocationClock :=
  ⟨c.nextOperation + 1, c.nextBirth + 1⟩

/-- Only the native numeric frontier rolls back; birth is erased proof history. -/
def rollbackAllocation (saved current : AllocationClock) : AllocationClock :=
  ⟨saved.nextOperation, current.nextBirth⟩

theorem rollback_reuses_id_with_fresh_birth (c : AllocationClock) (i : Nat) :
    let next := rollbackAllocation c (advanceAllocation c)
    next.nextOperation = c.nextOperation ∧
      identity next.nextBirth next.nextOperation i ≠ identity c.nextBirth c.nextOperation i := by
  simp [rollbackAllocation, advanceAllocation, identity, ChildIdentity.mk.injEq]

namespace Witness
def started : Projection := ⟨⟨1, 0, false, .running ⟨0, 0⟩ 0⟩, true, [], [0], []⟩
def prepared : Projection := { started with prepared := [0] }
def acknowledged : Projection :=
  { prepared with native := ⟨1, 1, true, .running ⟨0, 0⟩ 0⟩, acknowledgements := [0] }

theorem retired_running_reachable : Reachable 0 [7] acknowledged ∧
    acknowledged.native.retired = true ∧
    acknowledged.native.waiting = .running ⟨0, 0⟩ 0 ∧ ¬ Returned acknowledged := by
  have h₁ : Step 0 [7] initial (.start ⟨0, 0⟩ 0) started :=
    Step.start initial 0 rfl rfl rfl rfl (by decide)
  have h₂ : Step 0 [7] started (.prepare ⟨0, 0⟩) prepared :=
    Step.prepare started 0 rfl (by decide) (by decide) (Or.inr ⟨0, rfl, rfl⟩)
  have h₃ : Step 0 [7] prepared (.acknowledge ⟨0, 0⟩) acknowledged :=
    Step.acknowledge prepared 0 rfl (by decide) rfl (Or.inr ⟨0, rfl, rfl⟩)
  refine ⟨⟨_, Exec.snoc (Exec.snoc (Exec.snoc (Exec.nil initial) h₁) h₂) h₃⟩,
    rfl, rfl, ?_⟩
  simp [Returned, acknowledged]

theorem repeated_relation_distinct_occurrences :
    ([7, 7] : List Nat)[0]? = ([7, 7] : List Nat)[1]? ∧
      identity 0 0 0 ≠ identity 0 0 1 := by decide

theorem empty_initial_not_retired : initial.native.retired = false ∧
    Step 0 [] initial .noChild { initial with native := { initial.native with retired := true } } := by
  exact ⟨rfl, Step.noChild initial rfl rfl rfl (by decide)⟩
end Witness

/-! Retained-ack re-preparation delta. Resource reservation remains separate
from this executable native cursor-guard scan. A successful guard scan is not
an unconditional native `Ok`, nor authentication of the supplied owner map. -/
namespace Repreparation

/-- Exact successful cursor guards of prepare_replay_child_completion.
The native function does not test retired, and Ready is rejected. -/
def prepareGuard (owner : Option NativeState) (a : Ack) : Bool :=
  match owner with
  | none => false
  | some s => decide (s.consumed ≤ a.index ∧ a.index < s.queued) &&
      match s.waiting with
      | .idle => true
      | .running expected _ => decide (expected = a ∧ s.queued = a.index + 1)
      | .ready _ _ _ => false

theorem prepareGuard_some_exact (s : NativeState) (a : Ack) :
    prepareGuard (some s) a = true ↔
      s.consumed ≤ a.index ∧ a.index < s.queued ∧ CompletionWait a.operation a.index s := by
  cases s with
  | mk queued consumed retired waiting =>
      cases waiting <;> simp [prepareGuard, CompletionWait, and_assoc]

theorem prepareGuard_readback_exact (s : Projection) (a : Ack) :
    prepareGuard (readback s) a = true ↔ s.present = true ∧
      s.native.consumed ≤ a.index ∧ a.index < s.native.queued ∧
      CompletionWait a.operation a.index s.native := by
  cases h : s.present with
  | false => simp [readback, h, prepareGuard]
  | true => simpa [readback, h] using prepareGuard_some_exact s.native a

abbrev Owners := Nat → Option NativeState

def guard (owners : Owners) (a : Ack) : Bool := prepareGuard (owners a.operation) a

/-- Number of consecutive successful native guard checks, stopping at the first failure. -/
def scanCount (owners : Owners) : List Ack → Nat
  | [] => 0
  | a :: rest => if guard owners a then scanCount owners rest + 1 else 0

theorem scanCount_bound (owners : Owners) (xs : List Ack) :
    scanCount owners xs ≤ xs.length := by
  induction xs with
  | nil => simp [scanCount]
  | cons a xs ih => simp only [scanCount]; split <;> simp_all

theorem scanCount_prefix (owners : Owners) (xs : List Ack) :
    ∀ i < scanCount owners xs, ∃ a, xs[i]? = some a ∧ guard owners a = true := by
  induction xs with
  | nil => simp [scanCount]
  | cons a xs ih =>
      intro i hi
      by_cases hg : guard owners a = true
      · cases i with
        | zero => exact ⟨a, rfl, hg⟩
        | succ i =>
            have bound : i < scanCount owners xs := by simp [scanCount, hg] at hi; omega
            obtain ⟨b, hb, good⟩ := ih i bound
            exact ⟨b, hb, good⟩
      · simp [scanCount, hg] at hi

theorem scanCount_finish_or_failure (owners : Owners) (xs : List Ack) :
    scanCount owners xs = xs.length ∨
      ∃ a, xs[scanCount owners xs]? = some a ∧ guard owners a = false := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons a xs ih =>
      by_cases hg : guard owners a = true
      · rcases ih with done | ⟨b, hb, bad⟩
        · exact Or.inl (by simp [scanCount, hg, done])
        · exact Or.inr ⟨b, by simpa [scanCount, hg] using hb, bad⟩
      · exact Or.inr ⟨a, by simp [scanCount, hg], by simpa using hg⟩

def scanSteps (owners : Owners) (f : FrameProjection) : Nat :=
  scanCount owners (f.acks.drop f.prepared)

def scanFrame (owners : Owners) (f : FrameProjection) : FrameProjection :=
  { f with prepared := f.prepared + scanSteps owners f }

/-- A finite sequence of the actual prepared-index writes and selected guards. -/
inductive Trace (owners : Owners) : FrameProjection → Nat → FrameProjection → Prop
  | nil (f) : Trace owners f 0 f
  | cons {f g h n a} : guard owners a = true →
      FrameStep f (.reprepare f.prepared a) g → Trace owners g n h →
      Trace owners f (n + 1) h

theorem trace_reachable {owners : Owners} {f g : FrameProjection} {n index : Nat}
    {destination : Option Ack} (trace : Trace owners f n g)
    (reachable : FrameReachable index destination f) : FrameReachable index destination g := by
  induction trace with
  | nil => exact reachable
  | cons good step rest ih => exact ih (FrameReachable.step reachable step)

theorem trace_exact_fields {owners : Owners} {f g : FrameProjection} {n : Nat}
    (trace : Trace owners f n g) : g = { f with prepared := f.prepared + n } := by
  induction trace with
  | nil => simp
  | cons good step rest ih =>
      cases step
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih

theorem scan_trace_aux (owners : Owners) (xs : List Ack) {index : Nat} {destination : Option Ack} :
    ∀ f, FrameReachable index destination f → f.present = true →
      f.acks.drop f.prepared = xs →
      Trace owners f (scanCount owners xs)
        { f with prepared := f.prepared + scanCount owners xs } := by
  induction xs with
  | nil =>
      intro f reachable alive drop
      simpa [scanCount] using Trace.nil (owners := owners) f
  | cons a xs ih =>
      intro f reachable alive drop
      by_cases good : guard owners a = true
      · have selected : f.acks[f.prepared]? = some a := by
          simpa only [List.head?_drop, List.head?_cons] using congrArg List.head? drop
        obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp selected
        have inv := terminal_projection_accounting reachable
        have top := terminal_projection_live_top reachable alive
        have step := FrameStep.reprepare f a alive top.symm inv.completed_le_prepared bound selected
        have next := FrameReachable.step reachable step
        have tail : ({ f with prepared := f.prepared + 1 } : FrameProjection).acks.drop
            ({ f with prepared := f.prepared + 1 } : FrameProjection).prepared = xs := by
          simp only [List.drop_add_one_eq_tail_drop, drop, List.tail_cons]
        have rest := ih _ next alive tail
        have result := Trace.cons good step rest
        simpa [scanCount, good, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using result
      · simpa [scanCount, good] using Trace.nil (owners := owners) f

theorem scan_constructs_trace (owners : Owners) {index : Nat} {destination : Option Ack}
    {f : FrameProjection} (reachable : FrameReachable index destination f) (alive : f.present = true) :
    Trace owners f (scanSteps owners f) (scanFrame owners f) := by
  exact scan_trace_aux owners _ f reachable alive rfl

/-- No valid-ack list or completion invariant is supplied: the scan computes its prefix. -/
theorem scan_accounted (owners : Owners) {index : Nat} {destination : Option Ack}
    {f : FrameProjection} (reachable : FrameReachable index destination f) (alive : f.present = true) :
    FrameReachable index destination (scanFrame owners f) ∧ FrameAccounting (scanFrame owners f) := by
  have h := trace_reachable (scan_constructs_trace owners reachable alive) reachable
  exact ⟨h, terminal_projection_accounting h⟩

theorem scan_steps_bounded (owners : Owners) (f : FrameProjection) :
    scanSteps owners f ≤ f.acks.length - f.prepared := by
  simpa [scanSteps] using scanCount_bound owners (f.acks.drop f.prepared)

theorem scan_exact_first_failure (owners : Owners) {index : Nat} {destination : Option Ack}
    {f : FrameProjection} (reachable : FrameReachable index destination f) :
    (scanFrame owners f).prepared = f.acks.length ∨
      ∃ a, f.acks[(scanFrame owners f).prepared]? = some a ∧ guard owners a = false := by
  have bound := (terminal_projection_accounting reachable).prepared_le_length
  rcases scanCount_finish_or_failure owners (f.acks.drop f.prepared) with done | ⟨a, selected, bad⟩
  · left
    have hcount : scanSteps owners f = f.acks.length - f.prepared := by simpa [scanSteps] using done
    simp only [scanFrame, hcount]
    omega
  · right
    exact ⟨a, by simpa only [scanFrame, scanSteps, List.getElem?_drop] using selected, bad⟩

theorem scan_successful_prefix (owners : Owners) (f : FrameProjection) :
    ∀ i < scanSteps owners f, ∃ a, f.acks[f.prepared + i]? = some a ∧ guard owners a = true := by
  intro i hi
  obtain ⟨a, selected, good⟩ := scanCount_prefix owners (f.acks.drop f.prepared) i hi
  exact ⟨a, by simpa only [List.getElem?_drop] using selected, good⟩

theorem scan_complete_exact_steps (owners : Owners) (f : FrameProjection)
    (done : (scanFrame owners f).prepared = f.acks.length) :
    scanSteps owners f = f.acks.length - f.prepared := by
  change f.prepared + scanSteps owners f = f.acks.length at done
  omega

/-- The same selected ack supplies both existing cursor preparation and the new frame write. -/
theorem paired_cursor_frame_step {index : Nat} {destination : Option Ack} {children : List Nat}
    {f : FrameProjection} {s : Projection} {a : Ack}
    (frame : FrameReachable index destination f) (cursor : Reachable a.operation children s)
    (alive : f.present = true) (selected : f.acks[f.prepared]? = some a)
    (good : prepareGuard (readback s) a = true) :
    ∃ u g, Step a.operation children s (.prepare a) u ∧
      FrameStep f (.reprepare f.prepared a) g ∧
      Accounting a.operation children.length u ∧ FrameAccounting g := by
  obtain ⟨salive, lower, upper, waiting⟩ := (prepareGuard_readback_exact s a).mp good
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp selected
  have fi := terminal_projection_accounting frame
  have top := terminal_projection_live_top frame alive
  have hs := Step.prepare (children := children) s a.index salive lower upper waiting
  have hf := FrameStep.reprepare f a alive top.symm fi.completed_le_prepared bound selected
  exact ⟨_, _, hs, hf, step_preserves hs (cursor_projection_accounting cursor), frame_step_preserves hf fi⟩

/-- Restoring the original prepared counter restores the entire original frame. -/
theorem scan_preserves_other_fields (owners : Owners) (f : FrameProjection) :
    { scanFrame owners f with prepared := f.prepared } = f := by
  cases f
  rfl

theorem scan_complete_frame (owners : Owners) (f : FrameProjection)
    (done : (scanFrame owners f).prepared = f.acks.length) :
    scanFrame owners f = { f with prepared := f.acks.length } := by
  exact congrArg (fun p => { f with prepared := p }) done

theorem trace_prefix {owners : Owners} {f g : FrameProjection} {n : Nat}
    (trace : Trace owners f n g) : ∀ k ≤ n, ∃ h, Trace owners f k h := by
  induction trace with
  | nil =>
      intro k bound
      have : k = 0 := by omega
      subst k
      exact ⟨_, Trace.nil _⟩
  | @cons f g h n a good step rest ih =>
      intro k bound
      cases k with
      | zero => exact ⟨_, Trace.nil _⟩
      | succ k =>
          obtain ⟨u, hu⟩ := ih k (by omega)
          exact ⟨u, Trace.cons good step hu⟩

/-- Any resource-stopped successful prefix remains accounted, including the
full prefix before a failing final resource observation. This does not assert
that native resource reservation succeeds or authenticate a resource event. -/
theorem resource_stop_prefix (owners : Owners) {index : Nat} {destination : Option Ack}
    {f : FrameProjection} (reachable : FrameReachable index destination f) (alive : f.present = true)
    (k : Nat) (bound : k ≤ scanSteps owners f) :
    ∃ g, Trace owners f k g ∧ FrameReachable index destination g ∧ FrameAccounting g ∧
      g = { f with prepared := f.prepared + k } := by
  obtain ⟨g, hg⟩ := trace_prefix (scan_constructs_trace owners reachable alive) k bound
  have hr := trace_reachable hg reachable
  exact ⟨g, hg, hr, terminal_projection_accounting hr, trace_exact_fields hg⟩

def committed (f : FrameProjection) : FrameProjection :=
  { f with prepared := f.completed, terminalPrepared := false }

theorem committed_reachable {index : Nat} {destination : Option Ack} {f : FrameProjection}
    (reachable : FrameReachable index destination f) (alive : f.present = true) :
    FrameReachable index destination (committed f) :=
  FrameReachable.step reachable (FrameStep.commit f alive)

/-- Post-commit frontier restoration or the exact first failed guard; no stage
restriction excludes Diagnostics, and no completed-frontier premise is assumed. -/
theorem commit_scan_outcome (owners : Owners) {index : Nat} {destination : Option Ack}
    {f : FrameProjection} (reachable : FrameReachable index destination f) (alive : f.present = true) :
    let g := scanFrame owners (committed f)
    FrameReachable index destination g ∧ FrameAccounting g ∧
      g.terminalPrepared = false ∧ g.stage = f.stage ∧ g.completed = f.completed ∧
      g.done = f.done ∧
      (g.prepared = f.acks.length ∨ ∃ a, f.acks[g.prepared]? = some a ∧ guard owners a = false) := by
  have start := committed_reachable reachable alive
  have accounted := scan_accounted owners start alive
  have outcome := scan_exact_first_failure owners start
  exact ⟨accounted.1, accounted.2, rfl, rfl, rfl, rfl, outcome⟩

theorem commit_scan_complete_frame (owners : Owners) (f : FrameProjection)
    (done : (scanFrame owners (committed f)).prepared = f.acks.length) :
    scanFrame owners (committed f) =
      { f with prepared := f.acks.length, terminalPrepared := false } := by
  exact scan_complete_frame owners (committed f) done

theorem complete_scan_then_append (owners : Owners) {index : Nat} {destination : Option Ack}
    {f : FrameProjection} (reachable : FrameReachable index destination f) (alive : f.present = true)
    (working : f.stage = .working) (done : (scanFrame owners f).prepared = f.acks.length) (a : Ack) :
    ∃ g, FrameStep (scanFrame owners f) (.takeAck a) g ∧
      FrameReachable index destination g ∧ FrameAccounting g ∧ g.prepared = g.acks.length := by
  have accounted := scan_accounted owners reachable alive
  have step := FrameStep.takeAck (scanFrame owners f) a alive working
  have hr := FrameReachable.step accounted.1 step
  refine ⟨_, step, hr, terminal_projection_accounting hr, ?_⟩
  simpa [scanFrame, List.length_append] using done

theorem reprepare_deficit_decreases {f g : FrameProjection} {slot : Nat} {a : Ack}
    (step : FrameStep f (.reprepare slot a) g) :
    (f.acks.length - g.prepared) + 1 = f.acks.length - f.prepared := by
  cases step
  simp only
  omega

/-- Combined finite scan root. All success/failure information is computed
from the native cursor readbacks, not supplied as a valid retained-ack list. -/
theorem nonterminal_reprepare (owners : Owners) {index : Nat} {destination : Option Ack}
    {f : FrameProjection} (reachable : FrameReachable index destination f) (alive : f.present = true) :
    let n := scanSteps owners f
    let g := scanFrame owners f
    Trace owners f n g ∧ FrameReachable index destination g ∧ FrameAccounting g ∧
      { g with prepared := f.prepared } = f ∧ n ≤ f.acks.length - f.prepared ∧
      (∀ i < n, ∃ a, f.acks[f.prepared + i]? = some a ∧ guard owners a = true) ∧
      (g.prepared = f.acks.length ∨ ∃ a, f.acks[g.prepared]? = some a ∧ guard owners a = false) := by
  have accounted := scan_accounted owners reachable alive
  exact ⟨scan_constructs_trace owners reachable alive, accounted.1, accounted.2,
    scan_preserves_other_fields owners f, scan_steps_bounded owners f,
    scan_successful_prefix owners f, scan_exact_first_failure owners reachable⟩

theorem paired_owner_lookup_step (owners : Owners) {index : Nat} {destination : Option Ack}
    {children : List Nat} {f : FrameProjection} {s : Projection} {a : Ack}
    (frame : FrameReachable index destination f) (cursor : Reachable a.operation children s)
    (alive : f.present = true) (selected : f.acks[f.prepared]? = some a)
    (lookup : owners a.operation = readback s) (good : guard owners a = true) :
    ∃ u g, Step a.operation children s (.prepare a) u ∧
      FrameStep f (.reprepare f.prepared a) g ∧
      Accounting a.operation children.length u ∧ FrameAccounting g := by
  exact paired_cursor_frame_step frame cursor alive selected (by simpa [guard, lookup] using good)

namespace Witness
def firstAck : Ack := ⟨0, 0⟩
def secondAck : Ack := ⟨0, 1⟩
def owners : Owners := fun operation =>
  if operation = 0 then some ⟨2, 0, false, .idle⟩ else none
def retainedWorking : FrameProjection :=
  { initialFrame 0 none with acks := [firstAck, secondAck], prepared := 2 }
def retainedDiagnostics : FrameProjection :=
  { retainedWorking with stage := .diagnostics }

theorem retained_working_reachable : FrameReachable 0 none retainedWorking := by
  have h₁ := FrameStep.takeAck (initialFrame 0 none) firstAck rfl rfl
  have h₂ := FrameStep.takeAck
    { initialFrame 0 none with acks := [firstAck], prepared := 1 } secondAck rfl rfl
  exact FrameReachable.step (FrameReachable.step FrameReachable.initial h₁) h₂

theorem retained_diagnostics_reachable : FrameReachable 0 none retainedDiagnostics :=
  FrameReachable.step retained_working_reachable
    (FrameStep.enterDiagnostics retainedWorking rfl rfl)

theorem working_commit_reprepare :
    scanSteps owners (committed retainedWorking) = 2 ∧
      scanFrame owners (committed retainedWorking) = retainedWorking ∧
      FrameReachable 0 none (scanFrame owners (committed retainedWorking)) := by
  exact ⟨rfl, rfl, (commit_scan_outcome owners retained_working_reachable rfl).1⟩

theorem diagnostics_commit_reprepare :
    scanSteps owners (committed retainedDiagnostics) = 2 ∧
      scanFrame owners (committed retainedDiagnostics) = retainedDiagnostics ∧
      FrameReachable 0 none (scanFrame owners (committed retainedDiagnostics)) := by
  exact ⟨rfl, rfl, (commit_scan_outcome owners retained_diagnostics_reachable rfl).1⟩

theorem second_reprepare_uses_prepared_not_completed :
    let f := { committed retainedWorking with prepared := 1 }
    f.completed = 0 ∧ f.prepared = 1 ∧ f.acks[f.prepared]? = some secondAck ∧
      FrameStep f (.reprepare 1 secondAck) retainedWorking := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact FrameStep.reprepare _ secondAck rfl rfl (by decide) (by decide) rfl

theorem missing_owner_stops_at_first :
    scanSteps (fun _ => none) (committed retainedWorking) = 0 ∧
      guard (fun _ => none) firstAck = false := ⟨rfl, rfl⟩
end Witness

end Repreparation

end YulangClosure.NativeReplayAcknowledgement
