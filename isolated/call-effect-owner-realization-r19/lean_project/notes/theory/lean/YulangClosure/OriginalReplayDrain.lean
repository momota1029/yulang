import YulangClosure.NativeValueRelationExecution

/-!
The ordinary and suspended native Replay consumer, on the SAME worklist as
structured Value dispatch. The ordinary loop is total by its actual remaining
child vector, not caller fuel. A `Queued` return does not mean child completion.
This module is a control/ownership bridge for NQ §§5.2–5.3, not a termination
theorem for original inference or for a synchronously stepped child drain.
-/
namespace YulangClosure.OriginalReplayDrain

namespace C
export NativeDrainOwnership (State Operation Child Work Ticket Frame Wait Phase Step Run
  put work pushWork selectedTicket completedOperation initial)
end C

open NativeValuePorts (Pair Key)

inductive Outcome where
  | more | complete | queued | failed
  deriving DecidableEq, Repr

/-- Capacity/undo outcomes are sampled at the actual fallible cuts. Their
capacity-only effects erase from `C.State`; no successful resource is assumed. -/
structure Resources where
  transactional : Bool := false
  queueReserved : Bool := true
  undoReserved : Bool := true
  /-- Result of the raw `restoration` / `restorations` back-reference test,
  not a resource or child-completion fact. -/
  restorationHeld : Bool := false

def ackReady (resources : Resources) : Bool :=
  !resources.transactional || resources.undoReserved

def enqueued (s : C.State) (id : Nat) (op : C.Operation) (child : C.Child) : C.State :=
  let ticket := C.selectedTicket id op op.queued child.relation
  let issued := C.work s child.task child.relation (some ticket)
  { C.pushWork s issued false with
    operations := C.put s.operations id {op with queued := op.queued + 1}
    transferred := s.transferred ++ [ticket] }

def noChild (resources : Resources) (s : C.State) (id : Nat) (op : C.Operation) :
    C.State × Outcome :=
  if op.consumed < op.children.length then
    (s, if op.retired then .complete else .queued)
  else if ackReady resources = false then (s, .failed)
  else
    let completed := C.completedOperation op
    let next := if resources.transactional = false ∧ resources.restorationHeld = false ∧
        completed.retired = true then
      {s with operations := fun key => if key = id then none else s.operations key}
    else {s with operations := C.put s.operations id completed}
    (next, if completed.retired then .complete else .queued)

/-- `consume_replay_child(id,None)` followed by drive's return tests.
`queue_next` does not mutate the cursor. Only successful enqueue transfers the
ticket, increments `queued`, and then performs the infallible push_back. -/
def ordinaryStep (resources : Resources) (id : Nat) (s : C.State) : C.State × Outcome :=
  match s.operations id with
  | none => (s, .failed)
  | some op =>
      if op.waiting ≠ .idle then (s, .failed)
      else
        let next := if op.retired then none else op.children[op.queued]?
        match next with
        | none => noChild resources s id op
        | some child =>
            if resources.queueReserved = false ∨ op.consumed > op.queued ∨
                ackReady resources = false then (s, .failed)
            else (enqueued s id op child, .more)

def rank (id : Nat) (s : C.State) : Nat :=
  match s.operations id with
  | none => 0
  | some op => op.children.length - op.queued

theorem noChild_not_more (resources : Resources) (s : C.State) (id : Nat) (op : C.Operation) :
    (noChild resources s id op).2 ≠ .more := by
  unfold noChild
  split <;> simp only
  · cases op.retired <;> decide
  · split <;> simp only
    · decide
    · cases (C.completedOperation op).retired <;> decide

theorem ordinary_more_exact {resources : Resources} {id : Nat} {s t : C.State}
    (computed : ordinaryStep resources id s = (t, .more)) :
    ∃ op child, s.operations id = some op ∧ op.waiting = .idle ∧ op.retired = false ∧
      op.children[op.queued]? = some child ∧ op.consumed ≤ op.queued ∧
      t = enqueued s id op child := by
  unfold ordinaryStep at computed
  cases selected : s.operations id with
  | none => simp [selected] at computed
  | some op =>
      simp only [selected] at computed
      split at computed
      · cases computed
      · rename_i idle
        have wait : op.waiting = .idle := by simpa using idle
        cases retired : op.retired with
        | true =>
            simp only [retired, ↓reduceIte] at computed
            have impossible := noChild_not_more resources s id op
            rw [computed] at impossible
            exact False.elim (impossible rfl)
        | false =>
            simp only [retired, Bool.false_eq_true, ↓reduceIte] at computed
            cases childAt : op.children[op.queued]? with
            | none =>
                simp only [childAt] at computed
                have impossible := noChild_not_more resources s id op
                rw [computed] at impossible
                exact False.elim (impossible rfl)
            | some child =>
                simp only [childAt] at computed
                split at computed
                · cases computed
                · rename_i guards
                  have lower : op.consumed ≤ op.queued := by omega
                  cases computed
                  exact ⟨op, child, rfl, wait, retired, childAt, lower, rfl⟩

theorem ordinary_more_decreases {resources : Resources} {id : Nat} {s t : C.State}
    (computed : ordinaryStep resources id s = (t, .more)) : rank id t < rank id s := by
  obtain ⟨op, child, selected, _, _, found, _, rfl⟩ := ordinary_more_exact computed
  have less := (List.getElem?_eq_some_iff.mp found).1
  simp only [rank, selected, enqueued, C.put, ↓reduceIte]
  omega

/-- Fuel-free exact ordinary drive; errors and Queued are genuine outputs.
The decreasing argument uses only this operation's immutable child vector. -/
def ordinaryDrive (resources : C.State → Resources) (id : Nat) (s : C.State) :
    C.State × Outcome :=
  match _result : ordinaryStep (resources s) id s with
  | (next, .more) => ordinaryDrive resources id next
  | answer => answer
termination_by rank id s
decreasing_by exact ordinary_more_decreases _result

theorem ordinary_more_control {resources : Resources} {id : Nat} {s t : C.State}
    (computed : ordinaryStep resources id s = (t, .more))
    (active : ∃ frame rest, s.frames = frame :: rest ∧ frame.phase = .working) :
    C.Step s t := by
  obtain ⟨op, child, owner, idle, live, found, lower, rfl⟩ := ordinary_more_exact computed
  obtain ⟨frame, rest, top, phase⟩ := active
  have step := _root_.YulangClosure.NativeDrainOwnership.Step.enqueueReplay s frame rest id op.queued child.task child.relation
    op false top phase owner idle live (by cases child; exact found) lower (Nat.le_refl _)
  simpa [enqueued] using step

structure Batch where
  id : Nat
  birth : Nat
  task : Nat
  children : List C.Child

def Batch.operation (batch : Batch) (queued : Nat) : C.Operation :=
  {birth := batch.birth, task := batch.task, children := batch.children, queued := queued}

def Issued (batch : Batch) (s : C.State) (index : Nat) : Prop :=
  ∃ child, batch.children[index]? = some child ∧
    ∃ work ∈ s.issued, work ∈ s.queue ∧
      work.task = child.task ∧ work.relation = child.relation ∧
      work.ticket = some ⟨batch.birth, batch.id, index, child.relation⟩

def Prefix (batch : Batch) (s : C.State) (queued : Nat) : Prop :=
  ∀ index, index < queued → Issued batch s index

def At (batch : Batch) (s : C.State) (queued : Nat) : Prop :=
  s.operations batch.id = some (batch.operation queued) ∧
  queued ≤ batch.children.length ∧ Prefix batch s queued

theorem issued_mono {batch : Batch} {s t : C.State}
    (kept : ∀ work ∈ s.issued, work ∈ t.issued)
    (queued : ∀ work ∈ s.queue, work ∈ t.queue) {index : Nat}
    (issued : Issued batch s index) : Issued batch t index := by
  obtain ⟨child, found, work, member, pending, task, relation, ticket⟩ := issued
  exact ⟨child, found, work, kept work member, queued work pending, task, relation, ticket⟩

theorem enqueued_at {batch : Batch} {s : C.State} {queued : Nat} {child : C.Child}
    (valid : At batch s queued) (found : batch.children[queued]? = some child) :
    At batch (enqueued s batch.id (batch.operation queued) child) (queued + 1) := by
  have less := (List.getElem?_eq_some_iff.mp found).1
  refine ⟨by simp [enqueued, C.put, Batch.operation], by omega, ?_⟩
  intro index bound
  by_cases same : index = queued
  · subst index
    refine ⟨child, found, C.work s child.task child.relation
      (some (C.selectedTicket batch.id (batch.operation queued) queued child.relation)), ?_, ?_, rfl, rfl, rfl⟩
    all_goals simp [enqueued, C.pushWork, Batch.operation]
  · have earlier : index < queued := by omega
    exact issued_mono (fun work member => by simp [enqueued, C.pushWork, member])
      (fun work member => by simp [enqueued, C.pushWork, member])
      (valid.2.2 index earlier)

theorem ordinary_step_batch {batch : Batch} {s : C.State} {queued : Nat}
    (valid : At batch s queued) (resources : Resources)
    (active : ∃ frame rest, s.frames = frame :: rest ∧ frame.phase = .working) :
    let result := ordinaryStep resources batch.id s
    C.Run s result.1 ∧ result.1.frames = s.frames ∧
    (result.2 = .more → At batch result.1 (queued + 1)) ∧
    (result.2 = .complete ∨ result.2 = .queued →
      ∀ index, index < batch.children.length → Issued batch result.1 index) := by
  have owner := valid.1
  have bounded := valid.2.1
  by_cases pending : queued < batch.children.length
  · let child := batch.children[queued]
    have found : batch.children[queued]? = some child := List.getElem?_eq_getElem pending
    by_cases blocked : resources.queueReserved = false ∨ ackReady resources = false
    · have computed : ordinaryStep resources batch.id s = (s, .failed) := by
        simp [ordinaryStep, owner, Batch.operation, found, blocked]
      rw [computed]
      exact ⟨.nil _, rfl, by simp, by simp⟩
    · have computed : ordinaryStep resources batch.id s =
          (enqueued s batch.id (batch.operation queued) child, .more) := by
        simp [ordinaryStep, owner, Batch.operation, found, blocked]
      rw [computed]
      exact ⟨.snoc (.nil _) (ordinary_more_control computed active), rfl,
        fun _ => enqueued_at valid found, by simp⟩
  · have finished : queued = batch.children.length := by omega
    have found : batch.children[queued]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    by_cases nonempty : 0 < batch.children.length
    · have computed : ordinaryStep resources batch.id s = (s, .queued) := by
        simp [ordinaryStep, owner, Batch.operation, found, noChild, nonempty]
      rw [computed]
      exact ⟨.nil _, rfl, by simp, fun _ index bound => valid.2.2 index (by omega)⟩
    · have empty : batch.children = [] := List.eq_nil_of_length_eq_zero (by omega)
      have zero : queued = 0 := by simp [empty] at finished; exact finished
      clear finished
      subst queued
      by_cases unavailable : ackReady resources = false
      · have computed : ordinaryStep resources batch.id s = (s, .failed) := by
          simp [ordinaryStep, owner, Batch.operation, empty, noChild, unavailable]
        rw [computed]
        exact ⟨.nil _, rfl, by simp, by simp [empty]⟩
      · have ack := _root_.YulangClosure.NativeDrainOwnership.Step.noChild
          s batch.id (batch.operation 0) owner rfl rfl (by simp [Batch.operation, empty])
        have next : C.completedOperation (batch.operation 0) =
            {batch.operation 0 with retired := true} := by
          simp [C.completedOperation, Batch.operation, empty]
        by_cases transaction : resources.transactional = false ∧ resources.restorationHeld = false
        · let after := {s with operations := fun key => if key = batch.id then none else s.operations key}
          have computed : ordinaryStep resources batch.id s = (after, .complete) := by
            simp [ordinaryStep, owner, Batch.operation, empty, noChild, unavailable,
              C.completedOperation, transaction, after]
          have removal := _root_.YulangClosure.NativeDrainOwnership.Step.reclaim
            {s with operations := C.put s.operations batch.id (C.completedOperation (batch.operation 0))}
            batch.id (C.completedOperation (batch.operation 0))
            (by simp [C.put]) (by simp [C.completedOperation, Batch.operation]) (by simp [C.completedOperation, Batch.operation, empty])
          rw [computed]
          refine ⟨?_, rfl, by simp, by simp [empty]⟩
          have erased : (fun key => if key = batch.id then none else
              (C.put s.operations batch.id (C.completedOperation (batch.operation 0))) key) =
              (fun key => if key = batch.id then none else s.operations key) := by
            funext key
            by_cases same : key = batch.id <;> simp [C.put, same]
          simpa only [erased, after] using
            _root_.YulangClosure.NativeDrainOwnership.Run.snoc
              (_root_.YulangClosure.NativeDrainOwnership.Run.snoc (.nil _) ack) removal
        · let after := {s with operations := C.put s.operations batch.id (C.completedOperation (batch.operation 0))}
          have computed : ordinaryStep resources batch.id s = (after, .complete) := by
            simp [ordinaryStep, owner, Batch.operation, empty, noChild, unavailable,
              C.completedOperation, transaction, after]
          rw [computed]
          exact ⟨.snoc (.nil _) ack, rfl, by simp, by simp [empty]⟩

theorem ordinary_drive_batch {batch : Batch} {s : C.State} {queued : Nat}
    (valid : At batch s queued) (resources : C.State → Resources)
    (active : ∃ frame rest, s.frames = frame :: rest ∧ frame.phase = .working) :
    let result := ordinaryDrive resources batch.id s
    C.Run s result.1 ∧ result.1.frames = s.frames ∧ result.2 ≠ .more ∧
    (result.2 = .complete ∨ result.2 = .queued →
      ∀ index, index < batch.children.length → Issued batch result.1 index) := by
  induction s using (measure (rank batch.id)).wf.induction generalizing queued with
  | h s ih =>
      have details := ordinary_step_batch valid (resources s) active
      cases computed : ordinaryStep (resources s) batch.id s with
      | mk next outcome =>
          simp only [computed] at details
          rw [ordinaryDrive, computed]
          cases outcome with
          | more =>
              have nextActive : ∃ frame rest, next.frames = frame :: rest ∧ frame.phase = .working := by
                simpa [details.2.1] using active
              have rest := ih next (ordinary_more_decreases computed) (details.2.2.1 rfl) nextActive
              exact ⟨NativeValueDrain.control_run_trans details.1 rest.1,
                rest.2.1.trans details.2.1, rest.2.2⟩
          | complete | queued | failed => exact ⟨details.1, details.2.1, by simp, details.2.2.2⟩

def begin (s : C.State) (task : Nat) (children : List C.Child) : C.State :=
  let operation : C.Operation := { birth := s.nextBirth, task := task, children := children }
  { s with
    operations := C.put s.operations s.nextOperation operation
    nextOperation := s.nextOperation + 1
    nextBirth := s.nextBirth + 1 }

def batch (s : C.State) (task : Nat) (children : List C.Child) : Batch :=
  ⟨s.nextOperation, s.nextBirth, task, children⟩

theorem begin_at (s : C.State) (task : Nat) (children : List C.Child) :
    At (batch s task children) (begin s task children) 0 := by
  simp [At, Prefix, begin, batch, Batch.operation, C.put]

/-- Exact normal ordinary return: every child of the actual finite Replay
vector has an immutable occurrence in the SAME issued/worklist history.
Its consumed cursor may still be zero. No child completion is a premise. -/
theorem ordinary_return_issues_all (s : C.State) (task : Nat) (children : List C.Child)
    (resources : C.State → Resources)
    (active : ∃ frame rest, s.frames = frame :: rest ∧ frame.phase = .working) :
    let b := batch s task children
    let result := ordinaryDrive resources b.id (begin s task children)
    C.Run s result.1 ∧ result.2 ≠ .more ∧
      (result.2 = .complete ∨ result.2 = .queued →
        ∀ index, index < children.length → Issued b result.1 index) := by
  have constructed := ordinary_drive_batch (begin_at s task children) resources active
  exact ⟨NativeValueDrain.control_run_trans
    (.snoc (.nil _) (.allocate s task children)) constructed.1,
    constructed.2.2.1, constructed.2.2.2⟩

/-! ### The first empty Transport boundary, before the owning frame returns -/

/-- Native frames are stored newest first in the control projection. -/
def Indexed : List C.Frame → Prop
  | [] => True
  | frame :: rest => frame.index = rest.length ∧ Indexed rest

theorem indexed_member {frames : List C.Frame} (valid : Indexed frames)
    {frame : C.Frame} (member : frame ∈ frames) : frame.index < frames.length := by
  induction frames with
  | nil => simp at member
  | cons head rest ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · simp only [List.length_cons]; have := valid.1; omega
      · have below := ih valid.2 member
        simp only [List.length_cons]; omega

theorem indexed_commit (frames : List C.Frame) (valid : Indexed frames) :
    Indexed (frames.map fun frame => {frame with prepared := frame.completed}) := by
  induction frames with
  | nil => trivial
  | cons head rest ih =>
      exact ⟨by simpa using valid.1, ih valid.2⟩

theorem step_indexed {s t : C.State} (step : C.Step s t) (valid : Indexed s.frames) :
    Indexed t.frames := by
  cases step with
  | commit => exact indexed_commit _ valid
  | _ => simp_all [Indexed, C.pushWork, NativeDrainOwnership.newFrame,
      NativeDrainOwnership.consumedFrame]

theorem run_indexed {s t : C.State} (run : C.Run s t) (valid : Indexed s.frames) :
    Indexed t.frames := by
  induction run with
  | nil => exact valid
  | snoc _ step ih => exact step_indexed step ih

/-- A real dispatch exit, possibly in a nested frame that has since returned.
This does not mean that the relation was semantically successful or diagnosed. -/
def Processed (s : C.State) (work : C.Work) : Prop :=
  (∃ frame ∈ s.frames, work ∈ frame.processed) ∨
    NativeDrainOwnership.returnedWork work s.returns

/-- Conservation for one queued occurrence while its owning frame remains
on the stack. Nested synchronous drains remain in this same state. -/
def PendingAbove (floor : Nat) (s : C.State) (work : C.Work) : Prop :=
  work ∈ s.queue ∨ Processed s work ∨
    ∃ frame ∈ s.frames, frame.current = some work ∧ floor ≤ frame.index

theorem step_pending_above {s t : C.State} {floor : Nat} {work : C.Work}
    (step : C.Step s t) (indexed : Indexed s.frames) (inside : floor < s.frames.length)
    (held : PendingAbove floor s work) : PendingAbove floor t work := by
  cases step with
  | enqueuePlain f fs task relation front top phase =>
      cases front <;>
        simp_all [PendingAbove, Processed, C.pushWork,
          NativeDrainOwnership.returnedWork, or_and_right, exists_or] <;> grind
  | enqueueReplay f fs id index task relation op front top phase owner idle live child lower upper =>
      cases front <;>
        simp_all [PendingAbove, Processed, C.pushWork,
          NativeDrainOwnership.returnedWork, or_and_right, exists_or] <;> grind
  | _ =>
      simp_all [PendingAbove, Processed, Indexed, C.pushWork,
        NativeDrainOwnership.newFrame, NativeDrainOwnership.consumedFrame,
        NativeDrainOwnership.returnedWork, or_and_right, exists_or] <;> grind

/-- The finite prefix of one still-owned drain call. This is a stack-depth
condition on each actual control step, never a child-completion hypothesis.
It allows nested Some-provenance drains, acknowledgement and their returns. -/
inductive BeforeReturn (floor : Nat) : C.State → C.State → Prop
  | nil (s : C.State) : BeforeReturn floor s s
  | snoc {s t u : C.State} : BeforeReturn floor s t →
      floor < t.frames.length → C.Step t u → BeforeReturn floor s u

theorem before_return_control {floor : Nat} {s t : C.State}
    (run : BeforeReturn floor s t) : C.Run s t := by
  induction run with
  | nil => exact .nil _
  | snoc _ _ step ih => exact .snoc ih step

theorem before_return_pending {floor : Nat} {s t : C.State} {work : C.Work}
    (run : BeforeReturn floor s t) (indexed : Indexed s.frames)
    (held : PendingAbove floor s work) : PendingAbove floor t work := by
  induction run with
  | nil => exact held
  | snoc history inside step ih =>
      exact step_pending_above step (run_indexed (before_return_control history) indexed) inside ih

/-- NQ's first empty Transport cut needs no empty whole stack, no diagnosis,
no Replay consumed-cursor equality and no fairness assumption. -/
theorem queued_before_empty_transport {s t : C.State} {floor : Nat} {work : C.Work}
    (run : BeforeReturn floor s t) (indexed : Indexed s.frames)
    (queued : work ∈ s.queue)
    (empty : t.queue = []) {frame : C.Frame} {rest : List C.Frame}
    (top : t.frames = frame :: rest) (sameFrame : rest.length = floor)
    (noCurrent : frame.current = none) : Processed t work := by
  have held := before_return_pending run indexed (Or.inl queued)
  rcases held with pending | processed | ⟨currentFrame, member, current, above⟩
  · simp [empty] at pending
  · exact processed
  · have ordered := run_indexed (before_return_control run) indexed
    rw [top] at ordered member
    simp only [List.mem_cons] at member
    rcases member with rfl | older
    · simp [noCurrent] at current
    · have below := indexed_member ordered.2 older
      omega

/-- All children of an ordinary Replay return are processed before the same
drain's next empty Transport, even with suspended older frames underneath. -/
theorem ordinary_children_processed
    (s : C.State) (task : Nat) (children : List C.Child)
    (resources : C.State → Resources)
    (active : ∃ frame rest, s.frames = frame :: rest ∧ frame.phase = .working)
    (indexed : Indexed s.frames)
    {last : C.State} {frame : C.Frame} {rest : List C.Frame}
    (normal : (ordinaryDrive resources (batch s task children).id
      (begin s task children)).2 = .complete ∨
      (ordinaryDrive resources (batch s task children).id
      (begin s task children)).2 = .queued)
    (continuation : BeforeReturn rest.length
      (ordinaryDrive resources (batch s task children).id (begin s task children)).1 last)
    (empty : last.queue = []) (top : last.frames = frame :: rest)
    (noCurrent : frame.current = none) :
    ∀ index, index < children.length →
      ∃ child, children[index]? = some child ∧
        ∃ work, work.task = child.task ∧ work.relation = child.relation ∧
          work.ticket = some ⟨s.nextBirth, s.nextOperation, index, child.relation⟩ ∧
          Processed last work := by
  have computed := ordinary_return_issues_all s task children resources active
  intro index bound
  obtain ⟨child, found, work, _, pending, taskMatch, relation, ticket⟩ :=
    computed.2.2 normal index bound
  exact ⟨child, found, work, taskMatch, relation, ticket,
    queued_before_empty_transport continuation (run_indexed computed.1 indexed)
      pending empty top rfl noCurrent⟩

/-! ### Some-provenance restoration: actual wait guards and returned ownership -/

structure Restoration where
  retired : Bool
  replay : Option Nat
  deriving DecidableEq, Repr

/-- Exact `retire_replay_candidate` parent/back-reference test. -/
def restorationHeld (id : Nat) (parent : Option Nat)
    (restorations : Nat → Option Restoration) : Bool :=
  match parent with
  | none => false
  | some owner => match restorations owner with
    | none => false
    | some restoration => !restoration.retired && decide (restoration.replay = some id)

theorem restoration_held_exact (id : Nat) (parent : Option Nat)
    (restorations : Nat → Option Restoration) :
    restorationHeld id parent restorations = true ↔
      ∃ owner restored, parent = some owner ∧ restorations owner = some restored ∧
        restored.retired = false ∧ restored.replay = some id := by
  cases parent with
  | none => simp [restorationHeld]
  | some owner =>
      cases found : restorations owner <;> simp [restorationHeld, found]

structure Provenance where
  occurrence : Nat
  cause : Nat
  deriving DecidableEq, Repr

/-- The frame vector is reversed only by the shared control representation. -/
def frameAt (s : C.State) (index : Nat) : Option C.Frame := s.frames.reverse[index]?

inductive SyncAction where
  | failed
  | start (operation : C.Operation) (child : C.Child)
  | noChild (operation : C.Operation)
  | advance (operation : C.Operation) (ack : C.Ticket) (index : Nat)
  | deliver (operation : C.Operation) (ack : C.Ticket) (index transitions : Nat)
  deriving DecidableEq, Repr

/-- Exhaustive native `step_replay_child` branch selection. `maximum` is the
actual bounded integer maximum for checked_add, not inference fuel. Frame
occurrence/cause readbacks remain raw data; they are not child-typing facts. -/
def syncAction (maximum id : Nat) (provenance : Provenance)
    (tags : Nat → Option Provenance) (s : C.State) : SyncAction :=
  match s.operations id with
  | none => .failed
  | some op => match op.waiting with
    | .idle =>
        if op.queued ≠ op.consumed ∨ s.queue ≠ [] then .failed
        else match op.children[op.consumed]? with
          | none => .noChild op
          | some child => .start op child
    | .running ack index =>
        if ack.index ≥ maximum ∨ ack.operation ≠ id ∨ op.queued ≠ ack.index + 1 ∨
            (op.consumed ≠ ack.index ∧ op.consumed ≠ ack.index + 1) then .failed
        else match frameAt s index with
          | none => .failed
          | some frame =>
              if frame.destination ≠ some ack ∨ tags frame.birth ≠ some provenance then .failed
              else .advance op ack index
    | .ready ack index transitions =>
        if ack.index ≥ maximum ∨ ack.operation ≠ id ∨ op.consumed ≠ ack.index + 1 ∨
            op.queued ≠ ack.index + 1 ∨ s.frames.length ≠ index then .failed
        else .deliver op ack index transitions

def started (s : C.State) (id : Nat) (op : C.Operation) (child : C.Child) : C.State :=
  let ack := C.selectedTicket id op op.consumed child.relation
  { C.pushWork s (C.work s child.task child.relation (some ack)) false with
    operations := C.put s.operations id
      {op with queued := op.queued + 1, waiting := .running ack s.frames.length}
    frames := NativeDrainOwnership.newFrame s (some ack) :: s.frames
    nextBirth := s.nextBirth + 1
    transferred := s.transferred ++ [ack] }

def delivered (s : C.State) (id : Nat) (op : C.Operation) : C.State :=
  {s with operations := C.put s.operations id {op with waiting := .idle}}

theorem sync_start_exact {maximum id : Nat} {provenance : Provenance}
    {tags : Nat → Option Provenance} {s : C.State} {op : C.Operation} {child : C.Child}
    (selected : syncAction maximum id provenance tags s = .start op child)
    (live : op.retired = false) : C.Step s (started s id op child) := by
  unfold syncAction at selected
  cases owner : s.operations id with
  | none => simp [owner] at selected
  | some operation =>
      simp only [owner] at selected
      cases waiting : operation.waiting with
      | idle =>
          simp only [waiting] at selected
          split at selected
          · cases selected
          · rename_i guards
            cases found : operation.children[operation.consumed]? with
            | none => simp [found] at selected
            | some actual =>
                simp only [found, SyncAction.start.injEq] at selected
                obtain ⟨rfl, rfl⟩ := selected
                exact _root_.YulangClosure.NativeDrainOwnership.Step.startReplay
                  s id actual.task actual.relation operation owner (by simp_all)
                  waiting live (by simp_all) (by cases actual; exact found)
      | running ack index =>
          simp only [waiting] at selected
          split at selected
          · cases selected
          · cases found : frameAt s index <;> simp only [found] at selected
            · cases selected
            · split at selected <;> cases selected
      | ready ack index transitions =>
          simp only [waiting] at selected
          split at selected <;> cases selected

theorem sync_deliver_exact {maximum id : Nat} {provenance : Provenance}
    {tags : Nat → Option Provenance} {s : C.State} {op : C.Operation}
    {ack : C.Ticket} {index transitions : Nat}
    (selected : syncAction maximum id provenance tags s = .deliver op ack index transitions) :
    s.operations id = some op ∧ op.waiting = .ready ack index transitions ∧
      C.Step s (delivered s id op) := by
  unfold syncAction at selected
  cases owner : s.operations id with
  | none => simp [owner] at selected
  | some operation =>
      simp only [owner] at selected
      cases waiting : operation.waiting with
      | idle =>
          simp only [waiting] at selected
          split at selected
          · cases selected
          · cases found : operation.children[operation.consumed]? <;> simp [found] at selected
      | running ticket drain =>
          simp only [waiting] at selected
          split at selected
          · cases selected
          · cases found : frameAt s drain <;> simp only [found] at selected
            · cases selected
            · split at selected <;> cases selected
      | ready ticket drain count =>
          simp only [waiting] at selected
          split at selected
          · cases selected
          · rename_i guards
            simp only [SyncAction.deliver.injEq] at selected
            obtain ⟨rfl, rfl, rfl, rfl⟩ := selected
            exact ⟨rfl, waiting, _root_.YulangClosure.NativeDrainOwnership.Step.delivered
              s id operation ticket drain count owner (by simp_all) waiting
              (by simp_all) (by simp_all) (by simp_all)⟩

/-- Ready can only be published by the real `popReplay` return cut. The
receipt below is derived from the common control history, not supplied by
the caller or stored as a child-completion premise. -/
def ReadyOwned (s : C.State) : Prop :=
  ∀ id op ack index transitions,
    s.operations id = some op → op.waiting = .ready ack index transitions →
    ∃ returned ∈ s.returns,
      returned.frame.destination = some ack ∧ returned.frame.index = index ∧
      returned.frame.transitions = transitions ∧ returned.frame.phase = .returnReady ∧
      returned.frame.diagnosed = true ∧ returned.frame.current = none ∧
      returned.frame.pending = []

theorem initial_ready_owned : ReadyOwned C.initial := by simp [ReadyOwned, C.initial]

theorem step_ready_owned {s t : C.State} (step : C.Step s t) (owned : ReadyOwned s) :
    ReadyOwned t := by
  cases step <;>
    simp_all [ReadyOwned, C.put, C.pushWork, C.completedOperation] <;> grind

theorem run_ready_owned {s t : C.State} (run : C.Run s t) (owned : ReadyOwned s) :
    ReadyOwned t := by
  induction run with
  | nil => exact owned
  | snoc _ step ih => exact step_ready_owned step ih

theorem synchronous_delivery_has_real_return {maximum id : Nat} {provenance : Provenance}
    {tags : Nat → Option Provenance} {s : C.State} {op : C.Operation}
    {ack : C.Ticket} {index transitions : Nat}
    (history : C.Run C.initial s)
    (selected : syncAction maximum id provenance tags s = .deliver op ack index transitions) :
    ∃ returned ∈ s.returns,
      returned.frame.destination = some ack ∧ returned.frame.index = index ∧
      returned.frame.transitions = transitions ∧ returned.frame.phase = .returnReady ∧
      returned.frame.diagnosed = true ∧ returned.frame.current = none ∧
      returned.frame.pending = [] := by
  have exactSelection := sync_deliver_exact selected
  exact (run_ready_owned history initial_ready_owned) id op ack index transitions
    exactSelection.1 exactSelection.2.1

def release (resources : Resources) (id : Nat) (s : C.State) : C.State :=
  match s.operations id with
  | none => s
  | some op =>
      if resources.transactional = false ∧ resources.restorationHeld = false ∧
          op.retired = true ∧ op.waiting = .idle then
        {s with operations := fun key => if key = id then none else s.operations key}
      else s

theorem release_control (resources : Resources) (id : Nat) (s : C.State) :
    C.Run s (release resources id s) := by
  unfold release
  cases owner : s.operations id with
  | none => exact .nil _
  | some op =>
      simp only
      split
      · rename_i guard
        exact .snoc (.nil _) (.reclaim s id op owner guard.2.2.2 guard.2.2.1)
      · exact .nil _

def acknowledged (resources : Resources) (id : Nat) (op : C.Operation)
    (s : C.State) : C.State :=
  release resources id {s with operations := C.put s.operations id (C.completedOperation op)}

theorem sync_no_child_exact {maximum id : Nat} {provenance : Provenance}
    {tags : Nat → Option Provenance} {s : C.State} {op : C.Operation}
    (selected : syncAction maximum id provenance tags s = .noChild op)
    (resources : Resources) : C.Run s (acknowledged resources id op s) := by
  unfold syncAction at selected
  cases owner : s.operations id with
  | none => simp [owner] at selected
  | some operation =>
      simp only [owner] at selected
      cases waiting : operation.waiting with
      | idle =>
          simp only [waiting] at selected
          split at selected
          · cases selected
          · rename_i guards
            cases found : operation.children[operation.consumed]? with
            | some child => simp [found] at selected
            | none =>
                simp only [found, SyncAction.noChild.injEq] at selected
                subst op
                have same : operation.queued = operation.consumed := by simp_all
                have step := _root_.YulangClosure.NativeDrainOwnership.Step.noChild
                  s id operation owner waiting same (by simpa [same] using found)
                exact NativeValueDrain.control_run_trans (.snoc (.nil _) step)
                  (release_control resources id _)
      | running ack index =>
          simp only [waiting] at selected
          split at selected
          · cases selected
          · cases found : frameAt s index <;> simp only [found] at selected
            · cases selected
            · split at selected <;> cases selected
      | ready ack index transitions =>
          simp only [waiting] at selected
          split at selected <;> cases selected

inductive AvailabilityError where
  | identityExhausted
  /-- Opaque exact remaining native error value. No error is treated as a
  completed child, and the model does not require native errors to be absent. -/
  | native (code : Nat)
  deriving DecidableEq, Repr

inductive SyncOutcome where
  | more | delivered | noChild
  | failed (error : AvailabilityError)
  deriving DecidableEq, Repr

/-- Partial `start_typed_drain` after begin_typed_drain, before enqueue.
The new frame has no receipt and no queued child. -/
def opened (s : C.State) : C.State :=
  { s with
    frames := NativeDrainOwnership.newFrame s none :: s.frames
    nextBirth := s.nextBirth + 1 }

/-- A control-cut machine for the Some branch. An advance is one shared
drain event, not a returned-child oracle. Silent native stage writes erase to
`tick`. An inner error carries its partial state without constraining it by
the successful-run relation; this overapproximates all inner failure cuts.
Context/operand dispatch bodies remain their existing native owners. The
selector covers every Idle/Running/Ready and invalid-guard branch. -/
inductive SyncStep (maximum id : Nat) (provenance : Provenance)
    (tags : Nat → Option Provenance) (resources : Resources) :
    C.State → C.State → SyncOutcome → Prop
  | rejected (s : C.State)
      (selected : syncAction maximum id provenance tags s = .failed) :
      SyncStep maximum id provenance tags resources s s (.failed .identityExhausted)
  | waitFailure (s : C.State) (error : AvailabilityError)
      (preparing : (∃ op child, syncAction maximum id provenance tags s = .start op child) ∨
        (∃ op, syncAction maximum id provenance tags s = .noChild op) ∨
        (∃ op ack index count, syncAction maximum id provenance tags s = .deliver op ack index count)) :
      SyncStep maximum id provenance tags resources s s (.failed error)
  | beginFailure (s : C.State) (op : C.Operation) (child : C.Child) (error : AvailabilityError)
      (selected : syncAction maximum id provenance tags s = .start op child) :
      SyncStep maximum id provenance tags resources s s (.failed error)
  | startFailure (s : C.State) (op : C.Operation) (child : C.Child) (error : AvailabilityError)
      (selected : syncAction maximum id provenance tags s = .start op child) :
      SyncStep maximum id provenance tags resources s (opened s) (.failed error)
  | start (s : C.State) (op : C.Operation) (child : C.Child)
      (selected : syncAction maximum id provenance tags s = .start op child)
      (live : op.retired = false) (queueReserved : resources.queueReserved = true)
      (undoReserved : ackReady resources = true) :
      SyncStep maximum id provenance tags resources s (started s id op child) .more
  | noChild (s : C.State) (op : C.Operation)
      (selected : syncAction maximum id provenance tags s = .noChild op)
      (undoReserved : ackReady resources = true) :
      SyncStep maximum id provenance tags resources s (acknowledged resources id op s) .noChild
  | advance (s t : C.State) (op : C.Operation) (ack : C.Ticket) (index : Nat)
      (selected : syncAction maximum id provenance tags s = .advance op ack index)
      (event : C.Step s t) :
      SyncStep maximum id provenance tags resources s t .more
  | tick (s : C.State) (op : C.Operation) (ack : C.Ticket) (index : Nat)
      (selected : syncAction maximum id provenance tags s = .advance op ack index) :
      SyncStep maximum id provenance tags resources s s .more
  | innerFailure (s t : C.State) (op : C.Operation) (ack : C.Ticket) (index : Nat)
      (selected : syncAction maximum id provenance tags s = .advance op ack index)
      /- The actual error cut supplies its partial state, including any nested
      cleanup. No normal-run or conservation claim is made for this edge. -/
      (error : AvailabilityError) :
      SyncStep maximum id provenance tags resources s t (.failed error)
  | deliver (s : C.State) (op : C.Operation) (ack : C.Ticket) (index transitions : Nat)
      (selected : syncAction maximum id provenance tags s = .deliver op ack index transitions)
      (undoReserved : ackReady resources = true) :
      SyncStep maximum id provenance tags resources s
        (release resources id (delivered s id op)) .delivered

theorem synchronous_normal_control
    {maximum id : Nat} {provenance : Provenance} {tags : Nat → Option Provenance}
    {resources : Resources} {s t : C.State} {outcome : SyncOutcome}
    (step : SyncStep maximum id provenance tags resources s t outcome)
    (normal : ∀ error, outcome ≠ .failed error) : C.Run s t := by
  cases step with
  | start op child selected live _ _ =>
      exact .snoc (.nil _) (sync_start_exact selected live)
  | noChild op selected _ => exact sync_no_child_exact selected resources
  | advance _ _ _ _ _ event => exact .snoc (.nil _) event
  | tick => exact .nil _
  | deliver op ack index count selected _ =>
      exact NativeValueDrain.control_run_trans (.snoc (.nil _) (sync_deliver_exact selected).2.2)
        (release_control resources id _)
  | _ => exact False.elim (normal _ rfl)

/-- Finite actual Some-consumer executions. No constructor or theorem asserts
that a Running child eventually leaves this loop. Per-step resources and raw
frame metadata are read from the current state, as in the native call. -/
inductive SyncConsume (maximum id : Nat) (provenance : Provenance)
    (tags : C.State → Nat → Option Provenance) (resources : C.State → Resources) :
    C.State → C.State → SyncOutcome → Prop
  | stop {s t : C.State} {outcome : SyncOutcome}
      (step : SyncStep maximum id provenance (tags s) (resources s) s t outcome)
      (terminal : outcome ≠ .more) : SyncConsume maximum id provenance tags resources s t outcome
  | more {s t u : C.State} {outcome : SyncOutcome}
      (step : SyncStep maximum id provenance (tags s) (resources s) s t .more)
      (rest : SyncConsume maximum id provenance tags resources t u outcome) :
      SyncConsume maximum id provenance tags resources s u outcome

theorem synchronous_consume_normal_control
    {maximum id : Nat} {provenance : Provenance}
    {tags : C.State → Nat → Option Provenance} {resources : C.State → Resources}
    {s t : C.State} {outcome : SyncOutcome}
    (run : SyncConsume maximum id provenance tags resources s t outcome)
    (normal : ∀ error, outcome ≠ .failed error) : C.Run s t := by
  induction run with
  | stop step _ => exact synchronous_normal_control step normal
  | more step _ ih =>
      exact NativeValueDrain.control_run_trans
        (synchronous_normal_control step (by intro error; simp)) (ih normal)

/-- The outer drive test after consume returns. Some/NoChild without a retired
Idle operation is an error; None/NoChild is the ordinary Queued result. -/
def driveReturn (ordinary transferred : Bool) (id : Nat) (s : C.State) : Outcome :=
  match s.operations id with
  | none => .complete
  | some op =>
      if op.retired = true ∧ op.waiting = .idle then .complete
      else if transferred then .more
      else if ordinary then .queued else .failed

structure ProcessingState where
  control : C.State
  task : Option Nat
  relation : Option Nat

structure SavedCall where
  frameCount : Nat
  task : Option Nat
  relation : Option Nat

def saveCall (s : ProcessingState) : SavedCall := ⟨s.control.frames.length, s.task, s.relation⟩

/-- Exact error epilogue of consume_replay_child(Some). Native truncate keeps
the oldest saved frames. If the post-truncate operation lookup itself fails,
Rust's `?` returns before restoring the processing globals; retain that case. -/
def cleanup (id : Nat) (saved : SavedCall) (error : AvailabilityError)
    (s : ProcessingState) : ProcessingState × AvailabilityError :=
  if s.control.frames.length > saved.frameCount then
    let cut := {s.control with frames := s.control.frames.drop (s.control.frames.length - saved.frameCount)}
    match cut.operations id with
    | none => ({s with control := cut}, .identityExhausted)
    | some op =>
        (⟨{cut with operations := C.put cut.operations id {op with waiting := .idle}},
          saved.task, saved.relation⟩, error)
  else (⟨s.control, saved.task, saved.relation⟩, error)

theorem cleanup_keeps_worklist (id : Nat) (saved : SavedCall) (error : AvailabilityError)
    (s : ProcessingState) : (cleanup id saved error s).1.control.queue = s.control.queue := by
  unfold cleanup
  split <;> simp only
  · cases s.control.operations id <;> rfl

theorem cleanup_restores_processing {id : Nat} {saved : SavedCall} {error : AvailabilityError}
    {s : ProcessingState}
    (lookup : s.control.frames.length > saved.frameCount → ∃ op, s.control.operations id = some op) :
    (cleanup id saved error s).1.task = saved.task ∧
      (cleanup id saved error s).1.relation = saved.relation ∧
      (cleanup id saved error s).2 = error := by
  unfold cleanup
  split
  · rename_i more
    obtain ⟨op, found⟩ := lookup more
    simp [found]
  · exact ⟨rfl, rfl, rfl⟩

/-! ### The actual physical RelationId and all four native Function ports -/

namespace V
export NativeValueRelationExecution (Funding Store State start origin drive)
end V

/-- This keeps the computed physical interner, native port admission and
shared enqueue run joined all the way to the first empty Transport boundary.
The preexisting port driver's local fuel is only an execution witness; this
theorem does not use it to claim original inference termination. -/
theorem physical_children_before_empty
    {resources : Nat → V.Funding} {views : Nat → Option (Option Nat)}
    {qv qe : Nat → Nat} {parent : Key} {post : Nat} {derived : Bool}
    {store : V.Store} {children : List NativeValuePorts.Child} {control : C.State}
    {tasks : List Pair} {fuel : Nat} {emitted : V.State}
    (history : NativeRelationInterner.NativeHistory store.native)
    (indexed : Indexed control.frames)
    (active : NativeValueDrain.Active parent
      (NativeValueDrain.start (V.origin store children control tasks)))
    (computed : V.drive resources views qv qe parent post derived fuel
      (V.start store children control tasks) = some emitted) :
    NativeRelationInterner.NativeHistory emitted.store.native ∧
    C.Run control emitted.control ∧
    ∃ jobs : List NativeValueDrain.Issuance,
      jobs.map (fun job => job.port.source) = children ∧
      (∀ job ∈ jobs,
        job.matches emitted.tasks ∧
        NativeValuePorts.AdmissionResult emitted.store.arena views qv qe parent post derived
          job.port.source job.port.receipt ∧
        emitted.store.native.store.readback job.port.receipt.relation = some job.port.receipt.child ∧
        job.occurrence ∈ emitted.control.queue) ∧
      ∀ last frame rest, BeforeReturn rest.length emitted.control last →
        last.queue = [] → last.frames = frame :: rest → frame.current = none →
        ∀ job ∈ jobs, Processed last job.occurrence := by
  obtain ⟨physical, pure⟩ := NativeValueRelationExecution.drive_refines_emit history computed
  rw [NativeValueRelationExecution.start_decoded] at pure
  have initial := NativeValueDrain.start_invariant views qv qe parent post derived
    (V.origin store children control tasks) active
  obtain ⟨run, done⟩ := NativeValueDrain.emit_constructs_run initial pure
  have valid := NativeValueDrain.run_invariant run initial
  obtain ⟨_, jobs, sources, queue, _, every⟩ := NativeValueDrain.completed_issuance valid done
  have controlRun := NativeValueDrain.run_control run
  have pending : ∀ job ∈ jobs, job.occurrence ∈ emitted.control.queue := by
    intro job member
    change job.occurrence ∈ emitted.decoded.control.queue
    rw [queue]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨job, member, rfl⟩)
  refine ⟨physical, controlRun, jobs, sources, ?_, ?_⟩
  · intro job member
    obtain ⟨matched, checked⟩ := every job member
    exact ⟨matched, checked,
      NativeValueRelationExecution.registered_is_physical_readback physical checked.registered,
      pending job member⟩
  · intro last frame rest continuation empty top current job member
    exact queued_before_empty_transport continuation (run_indexed controlRun indexed)
      (pending job member) empty top rfl current

/-- Native Function contravariance includes BOTH Effect ports. Selecting the
argument port keeps the exact raw receiving-row task and physical relation ID.
No invented Value-only child vector is used by this specialization. -/
theorem function_four_ports_before_empty
    {resources : Nat → V.Funding} {views : Nat → Option (Option Nat)}
    {qv qe : Nat → Nat} {parent : Key} {post : Nat} {derived : Bool}
    {store : V.Store} {control : C.State} {tasks : List Pair} {fuel : Nat}
    {emitted : V.State} (terms : NativeValuePorts.TermEndpoints)
    (lower upper : NativeValuePorts.FunctionTerms)
    (history : NativeRelationInterner.NativeHistory store.native)
    (indexed : Indexed control.frames)
    (active : NativeValueDrain.Active parent (NativeValueDrain.start
      (V.origin store (NativeValuePorts.functionChildren terms lower upper) control tasks)))
    (computed : V.drive resources views qv qe parent post derived fuel
      (V.start store (NativeValuePorts.functionChildren terms lower upper) control tasks) = some emitted) :
    ∃ jobs : List NativeValueDrain.Issuance,
      jobs.map (fun job => job.port.source) = NativeValuePorts.functionChildren terms lower upper ∧
      jobs.map (fun job => job.port.source.port) =
        [.function .argument, .function .argumentEffect,
         .function .resultEffect, .function .result] ∧
      jobs.length = 4 ∧
      (∀ job ∈ jobs,
        emitted.tasks[job.occurrence.task]? = some job.port.source.task ∧
        job.occurrence.relation = job.port.receipt.relation ∧
        emitted.store.native.store.readback job.occurrence.relation = some job.port.receipt.child ∧
        job.port.receipt.child.pair = job.port.source.task.rename qv qe) ∧
      ∀ last frame rest, BeforeReturn rest.length emitted.control last →
        last.queue = [] → last.frames = frame :: rest → frame.current = none →
        ∀ job ∈ jobs, Processed last job.occurrence := by
  obtain ⟨_, _, jobs, sources, exactJobs, completed⟩ :=
    physical_children_before_empty history indexed active computed
  refine ⟨jobs, sources, ?_, ?_, ?_, completed⟩
  · have ports := congrArg (List.map NativeValuePorts.Child.port) sources
    simpa [List.map_map, Function.comp_def, NativeValuePorts.functionChildren] using ports
  · have size := congrArg List.length sources
    simpa [NativeValuePorts.functionChildren] using size
  · intro job member
    obtain ⟨matched, checked, readback, _⟩ := exactJobs job member
    exact ⟨matched.1, matched.2.1, by simpa [matched.2.1] using readback, checked.pair_exact⟩

/-- The production Replay vector is a list of raw RelationIds with one fixed
task, unlike the general control model's harmless per-child task view. -/
def replayChildren (task : Nat) (relations : List Nat) : List C.Child :=
  relations.map fun relation => ⟨task, relation⟩

theorem replay_child_exact (task : Nat) (relations : List Nat) (index relation : Nat)
    (found : relations[index]? = some relation) :
    (replayChildren task relations)[index]? = some ⟨task, relation⟩ := by
  simp [replayChildren, List.getElem?_map, found]

/-- There is no RelationId-to-task substitution at ordinary enqueue: the
same physical integer returned by the Replay producer remains the occurrence
origin even when Transport changes a frame's mutable processing relation. -/
theorem replay_relation_processed
    (s : C.State) (task : Nat) (relations : List Nat) (resources : C.State → Resources)
    (active : ∃ frame rest, s.frames = frame :: rest ∧ frame.phase = .working)
    (indexed : Indexed s.frames)
    {last : C.State} {frame : C.Frame} {rest : List C.Frame}
    (normal : (ordinaryDrive resources s.nextOperation
      (begin s task (replayChildren task relations))).2 = .complete ∨
      (ordinaryDrive resources s.nextOperation
      (begin s task (replayChildren task relations))).2 = .queued)
    (continuation : BeforeReturn rest.length
      (ordinaryDrive resources s.nextOperation (begin s task (replayChildren task relations))).1 last)
    (empty : last.queue = []) (top : last.frames = frame :: rest) (current : frame.current = none)
    {index relation : Nat} (found : relations[index]? = some relation) :
    ∃ work, work.task = task ∧ work.relation = relation ∧
      work.ticket = some ⟨s.nextBirth, s.nextOperation, index, relation⟩ ∧ Processed last work := by
  have childAt := replay_child_exact task relations index relation found
  have below := (List.getElem?_eq_some_iff.mp childAt).1
  obtain ⟨child, actual, work, taskMatch, origin, ticket, processed⟩ :=
    ordinary_children_processed s task (replayChildren task relations) resources active indexed
      normal continuation empty top current index below
  have same : child = ⟨task, relation⟩ := by simpa [childAt] using actual.symm
  subst child
  exact ⟨work, taskMatch, origin, ticket, processed⟩

end YulangClosure.OriginalReplayDrain
