import Std

/-! Shared worklist/frame/Replay ownership through successful drain events.
The relation and task fields retain native identities; this module does not
interpret their source types. A dispatch exit is not a semantic subtyping proof.
The complete event trace, not independently chosen cursor/frame histories, is
the input to the conservation and diagnosed-quiescence theorems.
-/
namespace YulangClosure.NativeDrainOwnership

structure Ticket where
  birth : Nat
  operation : Nat
  index : Nat
  relation : Nat
  deriving DecidableEq, Repr

inductive Wait where
  | idle
  | running (ticket : Ticket) (frame : Nat)
  | ready (ticket : Ticket) (frame transitions : Nat)
  deriving DecidableEq, Repr

structure Child where
  task : Nat
  relation : Nat
  deriving DecidableEq, Repr

structure Operation where
  birth : Nat
  task : Nat
  children : List Child
  queued : Nat := 0
  consumed : Nat := 0
  retired : Bool := false
  waiting : Wait := .idle
  deriving DecidableEq, Repr

structure Work where
  serial : Nat
  task : Nat
  relation : Nat
  ticket : Option Ticket
  deriving DecidableEq, Repr

inductive Phase where
  | working | diagnostics | acknowledgements | returnReady
  deriving DecidableEq, Repr

structure Frame where
  birth : Nat
  index : Nat
  current : Option Work := none
  processing : Option Nat := none
  processed : List Work := []
  done : List Ticket := []
  pending : List Ticket := []
  prepared : Nat := 0
  phase : Phase := .working
  diagnosed : Bool := false
  destination : Option Ticket := none
  transitions : Nat := 0
  deriving DecidableEq, Repr

/-- The split is an exact view of the native vector and completed cursor. -/
def Frame.acks (f : Frame) : List Ticket := f.done ++ f.pending
def Frame.completed (f : Frame) : Nat := f.done.length

structure ReturnReceipt where
  frame : Frame
  deriving DecidableEq, Repr

structure AckReceipt where
  ticket : Ticket
  frameBirth : Nat
  frameIndex : Nat
  diagnosed : Bool
  deriving DecidableEq, Repr

structure State where
  operations : Nat → Option Operation
  nextOperation : Nat
  nextBirth : Nat
  nextWork : Nat
  queue : List Work
  frames : List Frame
  issued : List Work
  transferred : List Ticket
  acknowledgements : List AckReceipt
  returns : List ReturnReceipt

def initial : State := ⟨fun _ => none, 0, 0, 0, [], [], [], [], [], []⟩

def put (table : Nat → Option Operation) (id : Nat) (op : Operation) :
    Nat → Option Operation := fun other => if other = id then some op else table other

def queueTicket (a : Ticket) (xs : List Work) : Prop := ∃ w ∈ xs, w.ticket = some a
def frameWork (w : Work) (f : Frame) : Prop := f.current = some w ∨ w ∈ f.processed
def stackWork (w : Work) (fs : List Frame) : Prop := ∃ f ∈ fs, frameWork w f
def stackTicket (a : Ticket) (fs : List Frame) : Prop := ∃ f ∈ fs, a ∈ f.acks
def returnedWork (w : Work) (rs : List ReturnReceipt) : Prop :=
  ∃ r ∈ rs, w ∈ r.frame.processed
def received (a : Ticket) (rs : List AckReceipt) : Prop := ∃ r ∈ rs, r.ticket = a

def TaskCovered (s : State) (w : Work) : Prop :=
  w ∈ s.queue ∨ stackWork w s.frames ∨ returnedWork w s.returns
def TicketCovered (s : State) (a : Ticket) : Prop :=
  queueTicket a s.queue ∨ stackTicket a s.frames ∨ received a s.acknowledgements

structure Invariant (s : State) : Prop where
  tasks : ∀ w ∈ s.issued, TaskCovered s w
  tickets : ∀ a ∈ s.transferred, TicketCovered s a
  done : ∀ f ∈ s.frames, ∀ a ∈ f.done, received a s.acknowledgements
  returned : ∀ r ∈ s.returns, r.frame.phase = .returnReady ∧
    r.frame.diagnosed = true ∧ r.frame.pending = [] ∧ r.frame.current = none
  acknowledgements : ∀ r ∈ s.acknowledgements, r.diagnosed = true

def work (s : State) (task relation : Nat) (ticket : Option Ticket) : Work :=
  ⟨s.nextWork, task, relation, ticket⟩

def pushWork (s : State) (w : Work) (front : Bool) : State :=
  { s with
    queue := if front then w :: s.queue else s.queue ++ [w]
    issued := s.issued ++ [w], nextWork := s.nextWork + 1 }

def newFrame (s : State) (destination : Option Ticket) : Frame :=
  { birth := s.nextBirth, index := s.frames.length, destination := destination }

def selectedTicket (id : Nat) (op : Operation) (index relation : Nat) : Ticket :=
  ⟨op.birth, id, index, relation⟩

/-- Native completion-wait guards, including the exact synchronous owner. -/
def completionWait (op : Operation) (a : Ticket) : Prop :=
  op.waiting = .idle ∨ ∃ index, op.waiting = .running a index ∧ op.queued = a.index + 1

def completedOperation (op : Operation) : Operation :=
  let consumed := if op.consumed < op.children.length then op.consumed + 1 else op.consumed
  { op with
    consumed := consumed
    retired := op.retired || decide (consumed = op.children.length) }

def consumedFrame (f : Frame) (a : Ticket) (remaining : List Ticket) : Frame :=
  { f with
    done := f.done ++ [a], pending := remaining
    phase := if remaining = [] then .returnReady else .acknowledgements }

def receipt (f : Frame) (a : Ticket) : AckReceipt :=
  ⟨a, f.birth, f.index, f.diagnosed⟩

/-! Each constructor records one successful source-owner cut. Counter tests,
lookups and vector positions are raw execution guards, never child typing.
`dispatch` records the actual end of Context/operand/structured dispatch; its
semantic installed body is a separate owner, not supplied by this control event.
-/
inductive Step : State → State → Prop
  | allocate (s : State) (task : Nat) (children : List Child) :
      Step s { s with
        operations := put s.operations s.nextOperation { birth := s.nextBirth, task := task, children := children }
        nextOperation := s.nextOperation + 1, nextBirth := s.nextBirth + 1 }
  | reserveOther (s : State) :
      Step s { s with nextOperation := s.nextOperation + 1, nextBirth := s.nextBirth + 1 }
  | begin (s : State) (task relation : Nat) (empty : s.queue = []) :
      Step s { pushWork s (work s task relation none) false with
        frames := newFrame s none :: s.frames, nextBirth := s.nextBirth + 1 }
  | enqueuePlain (s : State) (f : Frame) (fs : List Frame) (task relation : Nat)
      (front : Bool) (top : s.frames = f :: fs) (phase : f.phase = .working) :
      Step s (pushWork s (work s task relation none) front)
  | enqueueReplay (s : State) (f : Frame) (fs : List Frame) (id index task relation : Nat)
      (op : Operation) (front : Bool) (top : s.frames = f :: fs)
      (phase : f.phase = .working) (owner : s.operations id = some op)
      (idle : op.waiting = .idle) (live : op.retired = false)
      (child : op.children[index]? = some ⟨task, relation⟩)
      (lower : op.consumed ≤ index) (upper : index ≤ op.queued) :
      Step s (let a := selectedTicket id op index relation
        { pushWork s (work s task relation (some a)) front with
        operations := put s.operations id
          { op with queued := if index = op.queued then op.queued + 1 else op.queued }
        transferred := s.transferred ++ [a] })
  | startReplay (s : State) (id task relation : Nat) (op : Operation)
      (owner : s.operations id = some op) (empty : s.queue = [])
      (idle : op.waiting = .idle) (live : op.retired = false)
      (same : op.queued = op.consumed)
      (child : op.children[op.consumed]? = some ⟨task, relation⟩) :
      Step s (let a := selectedTicket id op op.consumed relation
        { pushWork s (work s task relation (some a)) false with
        operations := put s.operations id
          { op with queued := op.queued + 1, waiting := .running a s.frames.length }
        frames := newFrame s (some a) :: s.frames, nextBirth := s.nextBirth + 1
        transferred := s.transferred ++ [a] })
  | takePlain (s : State) (f : Frame) (fs : List Frame) (w : Work) (ws : List Work)
      (top : s.frames = f :: fs) (head : s.queue = w :: ws)
      (phase : f.phase = .working) (current : f.current = none) (plain : w.ticket = none) :
      Step s { s with queue := ws, frames := { f with current := some w, processing := some w.relation } :: fs }
  | takeReplay (s : State) (f : Frame) (fs : List Frame) (w : Work) (ws : List Work)
      (a : Ticket) (op : Operation)
      (top : s.frames = f :: fs) (head : s.queue = w :: ws)
      (phase : f.phase = .working) (current : f.current = none)
      (ack : w.ticket = some a) (owner : s.operations a.operation = some op)
      (lower : op.consumed ≤ a.index) (upper : a.index < op.queued)
      (wait : completionWait op a) (prepared : f.prepared = f.acks.length) :
      Step s { s with queue := ws, frames :=
        { f with
          current := some w, processing := some w.relation,
          pending := f.pending ++ [a], prepared := f.prepared + 1 } :: fs }
  | transport (s : State) (f : Frame) (fs : List Frame) (w : Work) (relation : Nat)
      (top : s.frames = f :: fs) (phase : f.phase = .working)
      (current : f.current = some w) :
      Step s { s with frames := { f with processing := some relation } :: fs }
  | dispatch (s : State) (f : Frame) (fs : List Frame) (w : Work) (transitions : Nat)
      (top : s.frames = f :: fs) (phase : f.phase = .working)
      (current : f.current = some w) :
      Step s { s with frames :=
        { f with
          current := none, processing := none,
          processed := f.processed ++ [w], transitions := transitions } :: fs }
  | prepare (s : State) (f : Frame) (fs : List Frame) (a : Ticket) (op : Operation)
      (top : s.frames = f :: fs) (position : f.acks[f.prepared]? = some a)
      (owner : s.operations a.operation = some op)
      (lower : op.consumed ≤ a.index) (upper : a.index < op.queued)
      (wait : completionWait op a) :
      Step s { s with frames := { f with prepared := f.prepared + 1 } :: fs }
  | enterDiagnostics (s : State) (f : Frame) (fs : List Frame)
      (top : s.frames = f :: fs) (phase : f.phase = .working)
      (current : f.current = none) (empty : s.queue = []) :
      Step s { s with frames := { f with phase := .diagnostics } :: fs }
  | diagnostics (s : State) (f : Frame) (fs : List Frame)
      (top : s.frames = f :: fs) (phase : f.phase = .diagnostics) :
      Step s { s with frames :=
        { f with phase := .acknowledgements, diagnosed := true } :: fs }
  | acknowledge (s : State) (f : Frame) (fs : List Frame) (a : Ticket)
      (rest : List Ticket) (op : Operation)
      (top : s.frames = f :: fs) (phase : f.phase = .acknowledgements)
      (diagnosed : f.diagnosed = true) (pending : f.pending = a :: rest)
      (prepared : f.completed < f.prepared)
      (owner : s.operations a.operation = some op) (ordered : op.consumed = a.index)
      (wait : completionWait op a) :
      Step s { s with
        operations := put s.operations a.operation (completedOperation op),
        frames := consumedFrame f a rest :: fs,
        acknowledgements := s.acknowledgements ++ [receipt f a] }
  | emptyReady (s : State) (f : Frame) (fs : List Frame)
      (top : s.frames = f :: fs) (phase : f.phase = .acknowledgements)
      (empty : f.pending = []) :
      Step s { s with frames := { f with phase := .returnReady } :: fs }
  | popPlain (s : State) (f : Frame) (fs : List Frame)
      (top : s.frames = f :: fs) (phase : f.phase = .returnReady)
      (index : f.index = fs.length) (empty : f.pending = [])
      (current : f.current = none) (diagnosed : f.diagnosed = true)
      (destination : f.destination = none) :
      Step s { s with frames := fs, returns := s.returns ++ [⟨f⟩] }
  | popReplay (s : State) (f : Frame) (fs : List Frame) (a : Ticket) (op : Operation)
      (top : s.frames = f :: fs) (phase : f.phase = .returnReady)
      (index : f.index = fs.length) (empty : f.pending = [])
      (current : f.current = none) (diagnosed : f.diagnosed = true)
      (destination : f.destination = some a) (owner : s.operations a.operation = some op)
      (wait : op.waiting = .running a f.index)
      (consumed : op.consumed = a.index + 1) (queued : op.queued = a.index + 1) :
      Step s { s with
        frames := fs, returns := s.returns ++ [⟨f⟩]
        operations := put s.operations a.operation
          { op with waiting := .ready a f.index f.transitions } }
  | delivered (s : State) (id : Nat) (op : Operation) (a : Ticket) (index transitions : Nat)
      (owner : s.operations id = some op) (same : a.operation = id)
      (wait : op.waiting = .ready a index transitions)
      (consumed : op.consumed = a.index + 1) (queued : op.queued = a.index + 1)
      (popped : s.frames.length = index) :
      Step s { s with operations := put s.operations id { op with waiting := .idle } }
  | noChild (s : State) (id : Nat) (op : Operation)
      (owner : s.operations id = some op) (idle : op.waiting = .idle)
      (same : op.queued = op.consumed) (missing : op.children[op.queued]? = none) :
      Step s { s with operations := put s.operations id (completedOperation op) }
  | reclaim (s : State) (id : Nat) (op : Operation)
      (owner : s.operations id = some op) (idle : op.waiting = .idle)
      (retired : op.retired = true) :
      Step s { s with operations := fun key => if key = id then none else s.operations key }

  | commit (s : State) :
      Step s { s with frames := s.frames.map fun f => { f with prepared := f.completed } }

theorem initial_invariant : Invariant initial := by
  constructor <;> simp [initial]

private theorem frameWork_cons (w : Work) (f : Frame) (fs : List Frame) :
    stackWork w (f :: fs) ↔ frameWork w f ∨ stackWork w fs := by
  simp [stackWork]

private theorem stackTicket_cons (a : Ticket) (f : Frame) (fs : List Frame) :
    stackTicket a (f :: fs) ↔ a ∈ f.acks ∨ stackTicket a fs := by
  simp [stackTicket]

private theorem queueTicket_cons (a : Ticket) (w : Work) (ws : List Work) :
    queueTicket a (w :: ws) ↔ w.ticket = some a ∨ queueTicket a ws := by
  simp [queueTicket]

private theorem queueTicket_append (a : Ticket) (xs ys : List Work) :
    queueTicket a (xs ++ ys) ↔ queueTicket a xs ∨ queueTicket a ys := by
  simp [queueTicket, or_and_right, exists_or]

private theorem received_append (a : Ticket) (xs ys : List AckReceipt) :
    received a (xs ++ ys) ↔ received a xs ∨ received a ys := by
  simp [received, or_and_right, exists_or]

private theorem returnedWork_append (w : Work) (xs ys : List ReturnReceipt) :
    returnedWork w (xs ++ ys) ↔ returnedWork w xs ∨ returnedWork w ys := by
  simp [returnedWork, or_and_right, exists_or]

theorem step_invariant {s t : State} (step : Step s t) (inv : Invariant s) : Invariant t := by
  rcases inv with ⟨tasks, tickets, done, returned, acknowledgements⟩
  cases step with
  | enqueuePlain f fs task relation front top phase =>
    cases front <;> constructor <;>
      simp_all [TaskCovered, TicketCovered, pushWork, work, Frame.acks,
        frameWork, stackWork, stackTicket, queueTicket, received, returnedWork,
        List.mem_append, List.mem_cons, or_and_right, exists_or] <;> grind
  | enqueueReplay f fs id index task relation op front top phase owner idle live child lower upper =>
    cases front <;> constructor <;>
      simp_all [TaskCovered, TicketCovered, pushWork, work, Frame.acks,
        frameWork, stackWork, stackTicket, queueTicket, received, returnedWork,
        List.mem_append, List.mem_cons, or_and_right, exists_or] <;> grind
  | _ =>
    constructor <;>
      simp_all [TaskCovered, TicketCovered, pushWork, newFrame, work, consumedFrame,
        receipt, Frame.acks, Frame.completed, frameWork, stackWork, stackTicket,
        queueTicket, received, returnedWork, List.mem_append, List.mem_cons,
        or_and_right, exists_or] <;> grind

/-- Facts established by the actual stage transitions, including the prepared
cursor interval. Diagnostic completion does not assert absence of conflicts. -/
def Frame.coherent (f : Frame) : Prop :=
  (f.phase ≠ .working → f.current = none) ∧
  ((f.phase = .acknowledgements ∨ f.phase = .returnReady) → f.diagnosed = true) ∧
  (f.phase = .returnReady → f.pending = []) ∧
  f.completed ≤ f.prepared ∧ f.prepared ≤ f.acks.length

def Coherent (s : State) : Prop := ∀ f ∈ s.frames, f.coherent

theorem initial_coherent : Coherent initial := by simp [Coherent, initial]

theorem step_coherent {s t : State} (step : Step s t) (h : Coherent s) : Coherent t := by
  cases step <;>
    simp_all [Coherent, Frame.coherent, Frame.completed, Frame.acks,
      pushWork, newFrame, consumedFrame] <;> grind

inductive Run : State → State → Prop
  | nil (s) : Run s s
  | snoc {s t u} : Run s t → Step t u → Run s u

theorem run_invariant {s t : State} (run : Run s t) (inv : Invariant s) : Invariant t := by
  induction run with
  | nil => exact inv
  | snoc _ step ih => exact step_invariant step ih

theorem reachable_invariant {s : State} (run : Run initial s) : Invariant s :=
  run_invariant run initial_invariant

theorem run_coherent {s t : State} (run : Run s t) (h : Coherent s) : Coherent t := by
  induction run with
  | nil => exact h
  | snoc _ step ih => exact step_coherent step ih

theorem reachable_coherent {s : State} (run : Run initial s) : Coherent s :=
  run_coherent run initial_coherent

/-- The extra facts used at the return cut follow from the preceding shared
history, not from an independent terminal-frame certificate. -/
theorem ready_frame_readback {s : State} (run : Run initial s)
    {f : Frame} (member : f ∈ s.frames) (ready : f.phase = .returnReady) :
    f.current = none ∧ f.diagnosed = true ∧ f.pending = [] ∧
    f.completed = f.prepared ∧ f.prepared = f.acks.length := by
  have h := reachable_coherent run f member
  rcases h with ⟨current, diagnosed, pending, lower, upper⟩
  have empty := pending ready
  have phase : f.phase ≠ .working := by simp [ready]
  have length : f.acks.length = f.completed := by simp [Frame.acks, Frame.completed, empty]
  exact ⟨current phase, diagnosed (.inr ready), empty, by omega, by omega⟩

/-- No supplied conservation, separate frame history or cursor history. -/
theorem quiescent_work_returned {s : State} (run : Run initial s)
    (queue : s.queue = []) (stack : s.frames = []) :
    ∀ w ∈ s.issued, ∃ r ∈ s.returns, w ∈ r.frame.processed ∧
      r.frame.diagnosed = true ∧ r.frame.phase = .returnReady ∧
      r.frame.pending = [] ∧ r.frame.current = none := by
  intro w issued
  have inv := reachable_invariant run
  have covered := inv.tasks w issued
  simp [TaskCovered, queue, stack, stackWork, returnedWork] at covered
  obtain ⟨r, member, processed⟩ := covered
  obtain ⟨phase, diagnosed, pending, current⟩ := inv.returned r member
  exact ⟨r, member, processed, diagnosed, phase, pending, current⟩

theorem quiescent_replay_acknowledged {s : State} (run : Run initial s)
    (queue : s.queue = []) (stack : s.frames = []) :
    ∀ a ∈ s.transferred, ∃ r ∈ s.acknowledgements,
      r.ticket = a ∧ r.diagnosed = true := by
  intro a transferred
  have inv := reachable_invariant run
  have covered := inv.tickets a transferred
  simp [TicketCovered, queue, stack, queueTicket, stackTicket, received] at covered
  obtain ⟨r, member, exactTicket⟩ := covered
  exact ⟨r, member, exactTicket, inv.acknowledgements r member⟩

theorem outstanding_ticket_has_owner {s : State} (run : Run initial s)
    {a : Ticket} (transferred : a ∈ s.transferred)
    (unacknowledged : ¬ received a s.acknowledgements) :
    queueTicket a s.queue ∨ stackTicket a s.frames := by
  have h := (reachable_invariant run).tickets a transferred
  exact h.elim Or.inl (fun h => h.elim Or.inr (False.elim ∘ unacknowledged))

theorem frame_prefix_has_real_receipts {s : State} (run : Run initial s)
    {f : Frame} (frame : f ∈ s.frames) :
    ∀ a ∈ f.done, ∃ r ∈ s.acknowledgements, r.ticket = a ∧ r.diagnosed = true := by
  intro a done
  have inv := reachable_invariant run
  obtain ⟨r, member, ticket⟩ := inv.done f frame a done
  exact ⟨r, member, ticket, inv.acknowledgements r member⟩

theorem frame_split_exact (f : Frame) :
    f.acks.take f.completed = f.done ∧ f.acks.drop f.completed = f.pending := by
  simp [Frame.acks, Frame.completed]

theorem empty_pending_iff_completed (f : Frame) :
    f.pending = [] ↔ f.completed = f.acks.length := by
  simp [Frame.completed, Frame.acks]

namespace Witness

/-- One Replay child runs in its synchronous owned drain; the
transported processing relation differs from its immutable admitted origin. -/
def ticket : Ticket := ⟨0, 0, 0, 42⟩
def operation : Operation := { birth := 0, task := 7, children := [⟨7, 42⟩] }
def occurrence : Work := ⟨0, 7, 42, some ticket⟩
def allocated : State :=
  { initial with
    operations := put initial.operations 0 operation,
    nextOperation := 1, nextBirth := 1 }
def runningOperation : Operation :=
  { operation with queued := 1, waiting := .running ticket 0 }
def frame : Frame := { birth := 1, index := 0, destination := some ticket }
def started : State :=
  { pushWork allocated occurrence false with
    operations := put allocated.operations 0 runningOperation,
    frames := [frame], nextBirth := 2, transferred := [ticket] }
def takenFrame : Frame :=
  { frame with
    current := some occurrence, processing := some 42,
    pending := [ticket], prepared := 1 }
def taken : State := { started with queue := [], frames := [takenFrame] }
def transportedFrame : Frame := { takenFrame with processing := some 99 }
def transported : State := { taken with frames := [transportedFrame] }
def dispatchedFrame : Frame :=
  { transportedFrame with
    current := none, processing := none,
    processed := [occurrence], transitions := 7 }
def dispatched : State := { transported with frames := [dispatchedFrame] }
def diagnosticFrame : Frame := { dispatchedFrame with phase := .diagnostics }
def diagnostic : State := { dispatched with frames := [diagnosticFrame] }
def diagnosedFrame : Frame :=
  { diagnosticFrame with phase := .acknowledgements, diagnosed := true }
def diagnosed : State := { diagnostic with frames := [diagnosedFrame] }
def completedFrame : Frame := consumedFrame diagnosedFrame ticket []
def completedOp : Operation := completedOperation runningOperation
def acknowledged : State :=
  { diagnosed with
    operations := put diagnosed.operations 0 completedOp,
    frames := [completedFrame], acknowledgements := [receipt diagnosedFrame ticket] }
def readyOp : Operation := { completedOp with waiting := .ready ticket 0 7 }
def returned : State :=
  { acknowledged with
    frames := [], returns := [⟨completedFrame⟩],
    operations := put acknowledged.operations 0 readyOp }
def delivered : State :=
  { returned with operations := put returned.operations 0 { readyOp with waiting := .idle } }

private theorem running_wait : completionWait runningOperation ticket :=
  .inr ⟨0, rfl, rfl⟩

theorem synchronous_transport_run : Run initial delivered := by
  have h1 : Step initial allocated := .allocate initial 7 [⟨7, 42⟩]
  have h2 : Step allocated started :=
    .startReplay allocated 0 7 42 operation rfl rfl rfl rfl rfl rfl
  have h3 : Step started taken :=
    .takeReplay started frame [] occurrence [] ticket runningOperation
      rfl rfl rfl rfl rfl rfl (by decide) (by decide) running_wait rfl
  have h4 : Step taken transported :=
    .transport taken takenFrame [] occurrence 99 rfl rfl rfl
  have h5 : Step transported dispatched :=
    .dispatch transported transportedFrame [] occurrence 7 rfl rfl rfl
  have h6 : Step dispatched diagnostic :=
    .enterDiagnostics dispatched dispatchedFrame [] rfl rfl rfl rfl
  have h7 : Step diagnostic diagnosed :=
    .diagnostics diagnostic diagnosticFrame [] rfl rfl
  have h8 : Step diagnosed acknowledged :=
    .acknowledge diagnosed diagnosedFrame [] ticket [] runningOperation
      rfl rfl rfl rfl (by decide) rfl rfl running_wait
  have h9 : Step acknowledged returned :=
    .popReplay acknowledged completedFrame [] ticket completedOp
      rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have h10 : Step returned delivered :=
    .delivered returned 0 readyOp ticket 0 7 rfl rfl rfl rfl rfl rfl
  exact ((((((((((Run.nil initial).snoc h1).snoc h2).snoc h3).snoc h4).snoc h5).snoc h6).snoc h7).snoc h8).snoc h9).snoc h10

/-- The same operation is acknowledged once, returned and delivered; delivery
itself performs no second acknowledgement. The processing relation changed. -/
theorem synchronous_transport_readback :
    transported.frames.head?.map Frame.processing = some (some 99) ∧
    delivered.issued = [occurrence] ∧ delivered.transferred = [ticket] ∧
    delivered.queue = [] ∧ delivered.frames = [] ∧
    delivered.acknowledgements = [receipt diagnosedFrame ticket] ∧
    delivered.acknowledgements = returned.acknowledgements ∧
    delivered.returns = [⟨completedFrame⟩] ∧
    delivered.operations 0 = some { completedOp with waiting := .idle } ∧
    completedOp.consumed = 1 ∧ completedOp.queued = 1 := by decide

end Witness

end YulangClosure.NativeDrainOwnership
