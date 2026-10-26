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

end YulangClosure.NativeReplayAcknowledgement
