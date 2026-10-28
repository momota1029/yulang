import YulangClosure.NativeValuePorts
import YulangClosure.NativeDrainOwnership
import YulangClosure.NativeValueStructure

/-!
The actual structured-child enqueue is the creation of its immutable drain
occurrence.  Admission and enqueue remain two distinct events.  The control
history is constructed from that same execution, not supplied independently.
Task indices below are ghost names for complete raw native task payloads; the
native implementation does not allocate this additional naming table.
-/
namespace YulangClosure.NativeValueDrain

open NativeValuePorts (Arena Key Pair Child Cursor Receipt AdmissionResult)
open NativeDrainOwnership (Frame)

abbrev Control := NativeDrainOwnership.State
abbrev NativeOccurrence := NativeDrainOwnership.Work
abbrev PortWork := NativeValuePorts.Work

def waitReady (operation : NativeDrainOwnership.Operation)
    (ticket : NativeDrainOwnership.Ticket) : Bool :=
  match operation.waiting with
  | .idle => true
  | .running actual _ => decide (actual = ticket ∧ operation.queued = ticket.index + 1)
  | .ready _ _ _ => false

theorem wait_ready_exact (operation : NativeDrainOwnership.Operation)
    (ticket : NativeDrainOwnership.Ticket) :
    waitReady operation ticket = true ↔ NativeDrainOwnership.completionWait operation ticket := by
  cases waiting : operation.waiting <;>
    simp [waitReady, NativeDrainOwnership.completionWait, waiting]

/-- The native top-frame/cursor guard after prepare_nonterminal_drain. -/
def ready (state : Control) : Bool :=
  match state.frames with
  | [] => false
  | frame :: rest => decide (frame.index = rest.length ∧
      frame.completed ≤ frame.prepared ∧ frame.prepared = frame.acks.length)

def prepareOne (state : Control) : Option Control := do
  let frame :: rest := state.frames | none
  if frame.index = rest.length ∧ frame.completed ≤ frame.prepared ∧
      frame.prepared < frame.acks.length then
    let ticket ← frame.acks[frame.prepared]?
    let operation ← state.operations ticket.operation
    if operation.consumed ≤ ticket.index ∧ ticket.index < operation.queued ∧
        waitReady operation ticket = true then
      some {state with frames := {frame with prepared := frame.prepared + 1} :: rest}
    else none
  else none

def prepareAll : Nat → Control → Option Control
  | 0, state => if ready state then some state else none
  | fuel + 1, state =>
      if ready state then some state
      else (prepareOne state).bind (prepareAll fuel)

theorem ready_preparation (fuel : Nat) (state : Control) (prepared : ready state = true) :
    prepareAll fuel state = some state := by
  cases fuel <;> simp [prepareAll, prepared]

theorem prepare_one_step {before after : Control} (computed : prepareOne before = some after) :
    NativeDrainOwnership.Step before after ∧
    ∃ frame rest, before.frames = frame :: rest ∧
      after = {before with frames := {frame with prepared := frame.prepared + 1} :: rest} := by
  cases top : before.frames with
  | nil => simp [prepareOne, top] at computed
  | cons frame rest =>
      simp only [prepareOne, top] at computed
      split at computed
      · obtain ⟨ticket, selected, more⟩ := Option.bind_eq_some_iff.mp computed
        obtain ⟨operation, owner, more⟩ := Option.bind_eq_some_iff.mp more
        split at more
        · rename_i guards
          cases more
          exact ⟨.prepare before frame rest ticket operation top selected owner guards.1 guards.2.1
            ((wait_ready_exact operation ticket).mp guards.2.2), frame, rest, rfl, rfl⟩
        · cases more
      · cases computed

theorem control_run_trans {first middle last : Control}
    (left : NativeDrainOwnership.Run first middle)
    (right : NativeDrainOwnership.Run middle last) :
    NativeDrainOwnership.Run first last := by
  induction right with
  | nil => exact left
  | snoc _ next ih => exact ih.snoc next

/-- Every successful preparation computes the complete cursor and its exact
frame update; all other shared control fields remain the original ones. -/
theorem prepare_all_exact {fuel : Nat} {before after : Control}
    (computed : prepareAll fuel before = some after) :
    NativeDrainOwnership.Run before after ∧ ready after = true ∧
    ∃ frame rest, before.frames = frame :: rest ∧
      after = {before with frames := {frame with prepared := frame.acks.length} :: rest} := by
  induction fuel generalizing before after with
  | zero =>
      simp only [prepareAll] at computed
      split at computed
      · rename_i prepared
        cases computed
        cases top : before.frames with
        | nil => simp [ready, top] at prepared
        | cons frame rest =>
            have complete : frame.prepared = frame.acks.length := by
              have guards := prepared
              simp only [ready, top, decide_eq_true_eq] at guards
              exact guards.2.2
            refine ⟨.nil _, prepared, frame, rest, rfl, ?_⟩
            simp only [← complete, ← top]
      · cases computed
  | succ fuel ih =>
      simp only [prepareAll] at computed
      split at computed
      · rename_i prepared
        cases computed
        cases top : before.frames with
        | nil => simp [ready, top] at prepared
        | cons frame rest =>
            have complete : frame.prepared = frame.acks.length := by
              have guards := prepared
              simp only [ready, top, decide_eq_true_eq] at guards
              exact guards.2.2
            refine ⟨.nil _, prepared, frame, rest, rfl, ?_⟩
            simp only [← complete, ← top]
      · obtain ⟨middle, one, more⟩ := Option.bind_eq_some_iff.mp computed
        obtain ⟨step, frame, rest, top, changed⟩ := prepare_one_step one
        obtain ⟨run, prepared, nextFrame, nextRest, nextTop, normalized⟩ := ih more
        have aligned : nextFrame = {frame with prepared := frame.prepared + 1} ∧ nextRest = rest := by
          simpa [changed] using nextTop.symm
        rw [aligned.1, aligned.2] at normalized
        refine ⟨control_run_trans ((NativeDrainOwnership.Run.nil before).snoc step) run,
          prepared, frame, rest, top, ?_⟩
        simpa [changed, NativeDrainOwnership.Frame.acks] using normalized

structure Issuance where
  port : PortWork
  occurrence : NativeOccurrence
  deriving DecidableEq, Repr

def Issuance.matches (tasks : List Pair) (record : Issuance) : Prop :=
  tasks[record.occurrence.task]? = some record.port.source.task ∧
  record.occurrence.relation = record.port.receipt.relation ∧
  record.occurrence.ticket = none

theorem issuance_kept {before after : List Pair}
    (extension : NativeValuePorts.Extends before after) {record : Issuance}
    (valid : record.matches before) : record.matches after :=
  ⟨extension _ _ valid.1, valid.2⟩

structure State where
  cursor : Cursor
  control : Control
  tasks : List Pair
  receipts : List Issuance := []

structure Origin where
  arena : Arena
  children : List Child
  control : Control
  tasks : List Pair := []

/-- The cursor's queue is the new-child prefix.  The arbitrary old native
queue remains in control; no premise requires it to be empty or plain. -/
def start (origin : Origin) : State :=
  ⟨NativeValuePorts.initialCursor origin.arena origin.children [],
    origin.control, origin.tasks, []⟩

/-- The actual active parent may have been transported: processing is read
separately from the immutable admitted occurrence's relation. -/
def ParentPresent (parent : Key) (state : State) : Prop :=
  ∃ frame rest work processing,
    state.control.frames = frame :: rest ∧ frame.phase = .working ∧
    frame.current = some work ∧ frame.processing = some processing ∧
    state.cursor.arena.relations[processing]? = some parent

def Active (parent : Key) (state : State) : Prop :=
  ParentPresent parent state ∧ ready state.control = true

theorem preflight_parent_active {parent : Key} {origin : Origin} {fuel : Nat}
    {prepared : Control} (present : ParentPresent parent (start origin))
    (computed : prepareAll fuel origin.control = some prepared) :
    Active parent (start {origin with control := prepared}) := by
  obtain ⟨_, complete, frame, rest, top, normalized⟩ := prepare_all_exact computed
  obtain ⟨old, oldRest, work, processing, oldTop, phase, current, selected, found⟩ := present
  have aligned : old = frame ∧ oldRest = rest := by
    change origin.control.frames = old :: oldRest at oldTop
    simpa [top] using oldTop.symm
  obtain ⟨frameEq, restEq⟩ := aligned
  subst old
  subst oldRest
  refine ⟨⟨{frame with prepared := frame.acks.length}, rest, work, processing,
    ?_, phase, current, selected, found⟩, complete⟩
  change prepared.frames = _
  simp only [normalized]

def State.admitted (state : State) (arena : Arena) (receipt : Receipt) : State :=
  { state with cursor := state.cursor.admitted arena receipt }

def State.enqueued (state : State) (child : Child) (rest : List Child)
    (receipt : Receipt) : State :=
  let named := NativeValuePorts.intern state.tasks child.task
  let occurrence := NativeDrainOwnership.work state.control named.2 receipt.relation none
  { cursor := state.cursor.enqueued child rest receipt
    control := NativeDrainOwnership.pushWork state.control occurrence true
    tasks := named.1
    receipts := state.receipts ++ [⟨⟨child, receipt⟩, occurrence⟩] }

theorem active_after_admission {parent : Key} {state : State} {arena : Arena}
    {receipt : Receipt} (active : Active parent state)
    (extension : state.cursor.arena.Extends arena) :
    Active parent (state.admitted arena receipt) := by
  obtain ⟨frame, rest, work, processing, top, phase, current, selected, found⟩ := active.1
  exact ⟨⟨frame, rest, work, processing, top, phase, current, selected,
    extension.2.2 _ _ found⟩, active.2⟩

theorem active_after_enqueue {parent : Key} {state : State} {child : Child}
    {rest : List Child} {receipt : Receipt} (active : Active parent state) :
    Active parent (state.enqueued child rest receipt) := by
  exact active

inductive Step (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : Key) (post : Nat) (derived : Bool) : State → State → Prop where
  | admit {state : State} {child : Child} {rest : List Child}
      {arena : Arena} {receipt : Receipt}
      (active : Active parent state) (idle : state.cursor.pending = none)
      (next : state.cursor.todo = child :: rest)
      (computed : NativeValuePorts.admit state.cursor.arena views qv qe parent post derived child =
        some (arena, receipt)) :
      Step views qv qe parent post derived state (state.admitted arena receipt)
  | enqueue {state : State} {child : Child} {rest : List Child} {receipt : Receipt}
      (active : Active parent state) (next : state.cursor.todo = child :: rest)
      (pending : state.cursor.pending = some receipt) :
      Step views qv qe parent post derived state (state.enqueued child rest receipt)

inductive Run (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : Key) (post : Nat) (derived : Bool) : State → State → Prop where
  | refl (state : State) : Run views qv qe parent post derived state state
  | step {first middle last : State}
      (next : Step views qv qe parent post derived first middle)
      (rest : Run views qv qe parent post derived middle last) :
      Run views qv qe parent post derived first last

theorem step_control {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {first last : State}
    (step : Step views qv qe parent post derived first last) :
    NativeDrainOwnership.Run first.control last.control := by
  cases step with
  | admit => exact .nil _
  | @enqueue child rest receipt active next pending =>
      obtain ⟨frame, frames, work, processing, top, phase, _⟩ := active.1
      exact (NativeDrainOwnership.Run.nil first.control).snoc
        (.enqueuePlain first.control frame frames
          (NativeValuePorts.intern first.tasks child.task).2 receipt.relation true top phase)

theorem run_control {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {first last : State}
    (run : Run views qv qe parent post derived first last) :
    NativeDrainOwnership.Run first.control last.control := by
  induction run with
  | refl => exact .nil _
  | step next _ ih => exact control_run_trans (step_control next) ih

theorem step_cursor {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {first last : State}
    (step : Step views qv qe parent post derived first last) :
    NativeValuePorts.DispatchStep views qv qe parent post derived first.cursor last.cursor := by
  cases step with
  | admit _ idle next computed => exact .admit idle next computed
  | enqueue _ next pending => exact .enqueue next pending

theorem run_cursor {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {first last : State}
    (run : Run views qv qe parent post derived first last) :
    NativeValuePorts.DispatchRun views qv qe parent post derived first.cursor last.cursor := by
  induction run with
  | refl => exact .refl _
  | step next _ ih => exact .step (step_cursor next) ih

structure Invariant (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : Key) (post : Nat) (derived : Bool) (origin : Origin) (state : State) : Prop where
  cursor : NativeValuePorts.CursorValid views qv qe parent post derived
    origin.children [] state.cursor
  records : state.receipts.map Issuance.port = state.cursor.records
  mapped : ∀ record ∈ state.receipts, record.matches state.tasks
  issued : state.control.issued = origin.control.issued ++ state.receipts.map Issuance.occurrence
  queue : state.control.queue = state.receipts.reverse.map Issuance.occurrence ++ origin.control.queue
  frames : state.control.frames = origin.control.frames
  next : state.control.nextWork = origin.control.nextWork + state.receipts.length
  serials : state.receipts.map (fun record => record.occurrence.serial) =
    List.range' origin.control.nextWork state.receipts.length
  tasks : NativeValuePorts.Extends origin.tasks state.tasks
  arena : origin.arena.Extends state.cursor.arena
  active : Active parent state

theorem start_invariant (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : Key) (post : Nat) (derived : Bool) (origin : Origin)
    (active : Active parent (start origin)) :
    Invariant views qv qe parent post derived origin (start origin) := by
  refine ⟨NativeValuePorts.initial_cursor_valid _ _ _ _ _ _ _ _ _, rfl, ?_, ?_, ?_,
    rfl, ?_, rfl, NativeValuePorts.extends_refl _, NativeValuePorts.arena_extends_refl _, active⟩
  · simp [start]
  · simp [start]
  · simp [start]
  · simp [start]

theorem step_invariant {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {origin : Origin} {first last : State}
    (step : Step views qv qe parent post derived first last)
    (valid : Invariant views qv qe parent post derived origin first) :
    Invariant views qv qe parent post derived origin last := by
  have portProof := NativeValuePorts.dispatch_step_valid (step_cursor step) valid.cursor
  cases step with
  | @admit child rest arena receipt active idle next computed =>
      have extension := (NativeValuePorts.admit_constructs computed).1
      exact ⟨portProof, valid.records, valid.mapped, valid.issued, valid.queue, valid.frames,
        valid.next, valid.serials, valid.tasks,
        NativeValuePorts.arena_extends_trans valid.arena extension,
        active_after_admission active extension⟩
  | @enqueue child rest receipt active next pending =>
      refine ⟨portProof, ?_, ?_, ?_, ?_, valid.frames, ?_, ?_, ?_, valid.arena,
        active_after_enqueue active⟩
      · simp [State.enqueued, NativeValuePorts.Cursor.enqueued, valid.records]
      · intro record member
        simp only [State.enqueued, List.mem_append, List.mem_singleton] at member
        rcases member with old | rfl
        · exact issuance_kept (NativeValuePorts.intern_extends _ _) (valid.mapped record old)
        · exact ⟨NativeValuePorts.intern_found _ _, rfl, rfl⟩
      · simp [State.enqueued, NativeDrainOwnership.pushWork, valid.issued, List.append_assoc]
      · simp [State.enqueued, NativeDrainOwnership.pushWork, valid.queue]
      · simp [State.enqueued, NativeDrainOwnership.pushWork, valid.next, Nat.add_assoc]
      · simp only [State.enqueued, List.map_append, List.map_singleton, List.length_append,
          List.length_singleton, NativeDrainOwnership.work]
        rw [valid.serials, valid.next]
        simpa using (List.range'_append_1 (s := origin.control.nextWork)
          (m := first.receipts.length) (n := 1))
      · exact NativeValuePorts.extends_trans valid.tasks (NativeValuePorts.intern_extends _ _)

theorem run_invariant {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {origin : Origin} {first last : State}
    (run : Run views qv qe parent post derived first last)
    (valid : Invariant views qv qe parent post derived origin first) :
    Invariant views qv qe parent post derived origin last := by
  induction run with
  | refl => exact valid
  | step next _ ih => exact ih (step_invariant next valid)

/-- The repeated preflight at each native child stage has no further control
mutation: this scan appends no Replay acknowledgement. Resource reservation
and the native journal projection are separate allocation-success owners. -/
theorem emission_preparation_stays_complete {views : Nat → Option (Option Nat)}
    {qv qe : Nat → Nat} {parent : Key} {post : Nat} {derived : Bool}
    {origin : Origin} {first last : State}
    (run : Run views qv qe parent post derived first last)
    (valid : Invariant views qv qe parent post derived origin first) (fuel : Nat) :
    prepareAll fuel last.control = some last.control :=
  ready_preparation fuel last.control (run_invariant run valid).active.2

/-- This computes both the already checked port cursor and the actual enqueue
occurrence.  The active-frame condition is the raw caller guard, below; no
return/completion or child typing premise is needed. -/
def emit (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : Key) (post : Nat) (derived : Bool) : Nat → State → Option State
  | 0, state => if state.cursor.todo = [] then some state else none
  | fuel + 1, state =>
      match state.cursor.todo with
      | [] => some state
      | child :: rest =>
          match state.cursor.pending with
          | none => do
              let (arena, receipt) ← NativeValuePorts.admit state.cursor.arena
                views qv qe parent post derived child
              emit views qv qe parent post derived fuel (state.admitted arena receipt)
          | some receipt =>
              emit views qv qe parent post derived fuel (state.enqueued child rest receipt)

theorem emit_constructs_run {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {fuel : Nat} {origin : Origin}
    {first last : State}
    (valid : Invariant views qv qe parent post derived origin first)
    (computed : emit views qv qe parent post derived fuel first = some last) :
    Run views qv qe parent post derived first last ∧ last.cursor.todo = [] := by
  induction fuel generalizing first last with
  | zero =>
      unfold emit at computed
      split at computed
      · cases computed; exact ⟨.refl _, ‹first.cursor.todo = []›⟩
      · cases computed
  | succ fuel ih =>
      cases next : first.cursor.todo with
      | nil =>
          simp only [emit, next, Option.some.injEq] at computed
          subst last
          exact ⟨.refl _, next⟩
      | cons child rest =>
          cases pending : first.cursor.pending with
          | none =>
              simp only [emit, next, pending] at computed
              obtain ⟨⟨arena, receipt⟩, admitted, remaining⟩ := Option.bind_eq_some_iff.mp computed
              have step : Step views qv qe parent post derived first (first.admitted arena receipt) :=
                .admit valid.active pending next admitted
              obtain ⟨run, finished⟩ := ih (step_invariant step valid) remaining
              exact ⟨.step step run, finished⟩
          | some receipt =>
              simp only [emit, next, pending] at computed
              have step : Step views qv qe parent post derived first (first.enqueued child rest receipt) :=
                .enqueue valid.active next pending
              obtain ⟨run, finished⟩ := ih (step_invariant step valid) computed
              exact ⟨.step step run, finished⟩

theorem emit_cursor_exact (views : Nat → Option (Option Nat)) (qv qe : Nat → Nat)
    (parent : Key) (post : Nat) (derived : Bool) (fuel : Nat) (state : State) :
    (emit views qv qe parent post derived fuel state).map State.cursor =
      NativeValuePorts.drive views qv qe parent post derived fuel state.cursor := by
  induction fuel generalizing state with
  | zero => simp only [emit, NativeValuePorts.drive]; split <;> rfl
  | succ fuel ih =>
      cases next : state.cursor.todo with
      | nil => simp [emit, NativeValuePorts.drive, next]
      | cons child rest =>
          cases pending : state.cursor.pending with
          | some receipt =>
              simpa [emit, NativeValuePorts.drive, next, pending, State.enqueued] using
                ih (state.enqueued child rest receipt)
          | none =>
              simp only [emit, NativeValuePorts.drive, next, pending]
              cases admitted : NativeValuePorts.admit state.cursor.arena
                  views qv qe parent post derived child with
              | none => rfl
              | some pair =>
                  obtain ⟨arena, receipt⟩ := pair
                  simpa [Option.bind, Option.map, State.admitted] using ih (state.admitted arena receipt)

/-- The existing native-port computation itself supplies the coupled history.
No independently chosen matching final control state is an input. -/
theorem native_drive_constructs_common_run {views : Nat → Option (Option Nat)}
    {qv qe : Nat → Nat} {parent : Key} {post : Nat} {derived : Bool}
    {origin : Origin} {fuel : Nat} {cursor : Cursor}
    (active : Active parent (start origin))
    (computed : NativeValuePorts.drive views qv qe parent post derived fuel
      (NativeValuePorts.initialCursor origin.arena origin.children []) = some cursor) :
    ∃ state,
      emit views qv qe parent post derived fuel (start origin) = some state ∧
      state.cursor = cursor ∧ Run views qv qe parent post derived (start origin) state ∧
      state.cursor.todo = [] := by
  have projected := emit_cursor_exact views qv qe parent post derived fuel (start origin)
  change (emit views qv qe parent post derived fuel (start origin)).map State.cursor =
    NativeValuePorts.drive views qv qe parent post derived fuel
      (NativeValuePorts.initialCursor origin.arena origin.children []) at projected
  rw [computed] at projected
  cases result : emit views qv qe parent post derived fuel (start origin) with
  | none => simp [result] at projected
  | some state =>
      have same : state.cursor = cursor := by simpa [result] using projected
      obtain ⟨run, finished⟩ := emit_constructs_run
        (start_invariant views qv qe parent post derived origin active) result
      exact ⟨state, rfl, same, run, finished⟩

theorem completed_issuance {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {origin : Origin} {state : State}
    (valid : Invariant views qv qe parent post derived origin state)
    (finished : state.cursor.todo = []) :
    state.cursor.pending = none ∧
    ∃ jobs : List Issuance,
      jobs.map (fun job => job.port.source) = origin.children ∧
      state.control.queue = jobs.map Issuance.occurrence ++ origin.control.queue ∧
      state.control.issued = origin.control.issued ++ jobs.reverse.map Issuance.occurrence ∧
      (∀ job ∈ jobs, job.matches state.tasks ∧
        AdmissionResult state.cursor.arena views qv qe parent post derived
          job.port.source job.port.receipt) := by
  have done : state.cursor.done = origin.children.reverse := by
    simpa [finished] using valid.cursor.split
  refine ⟨NativeValuePorts.finished_pending_none valid.cursor finished,
    state.receipts.reverse, ?_, valid.queue, ?_, ?_⟩
  · have sourced : state.receipts.map (fun job => job.port.source) = state.cursor.done := by
      calc
        _ = (state.receipts.map Issuance.port).map NativeValuePorts.Work.source := by
          simp only [List.map_map, Function.comp_def]
        _ = _ := by rw [valid.records, valid.cursor.records]
    rw [List.map_reverse, sourced, done, List.reverse_reverse]
  · simpa using valid.issued
  · intro job member
    have old := List.mem_reverse.mp member
    refine ⟨valid.mapped job old, valid.cursor.checked _ ?_⟩
    rw [← valid.records]
    exact List.mem_map.mpr ⟨job, old, rfl⟩

theorem step_keeps_issued {first last : Control} (step : NativeDrainOwnership.Step first last)
    {work : NativeOccurrence} (member : work ∈ first.issued) : work ∈ last.issued := by
  cases step <;> simp_all [NativeDrainOwnership.pushWork]

theorem run_keeps_issued {first last : Control} (run : NativeDrainOwnership.Run first last)
    {work : NativeOccurrence} (member : work ∈ first.issued) : work ∈ last.issued := by
  induction run with
  | nil => exact member
  | snoc _ step ih => exact step_keeps_issued step ih

/-- Every child produced by the computed builder reaches a diagnosed return
in the SAME prefix / constructed enqueue / continuation history.  Diagnostic
execution here does not assert that the diagnostic vector was conflict-free. -/
theorem emitted_children_returned {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {origin : Origin} {fuel : Nat}
    {emitted : State} {last : Control}
    (priorRun : NativeDrainOwnership.Run NativeDrainOwnership.initial origin.control)
    (active : Active parent (start origin))
    (computed : emit views qv qe parent post derived fuel (start origin) = some emitted)
    (continuation : NativeDrainOwnership.Run emitted.control last)
    (queue : last.queue = []) (stack : last.frames = []) :
    ∃ jobs : List Issuance,
      jobs.map (fun job => job.port.source) = origin.children ∧
      ∀ job ∈ jobs,
        job.matches emitted.tasks ∧
        AdmissionResult emitted.cursor.arena views qv qe parent post derived
          job.port.source job.port.receipt ∧
        ∃ returned ∈ last.returns, job.occurrence ∈ returned.frame.processed ∧
          returned.frame.diagnosed = true ∧ returned.frame.phase = .returnReady ∧
          returned.frame.pending = [] ∧ returned.frame.current = none := by
  have initial := start_invariant views qv qe parent post derived origin active
  obtain ⟨run, finished⟩ := emit_constructs_run initial computed
  have valid := run_invariant run initial
  obtain ⟨_, jobs, sources, _, issued, matched⟩ := completed_issuance valid finished
  have whole := control_run_trans (control_run_trans priorRun (run_control run)) continuation
  refine ⟨jobs, sources, ?_⟩
  intro job member
  obtain ⟨task, checked⟩ := matched job member
  have original : job.occurrence ∈ emitted.control.issued := by
    rw [issued]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨job, List.mem_reverse.mpr member, rfl⟩)
  exact ⟨task, checked, NativeDrainOwnership.quiescent_work_returned whole queue stack
    job.occurrence (run_keeps_issued continuation original)⟩

/-- Native preflight and the existing port drive construct the actual middle
state and all its future child-return conclusions.  No preprepared-frame or
independently matching middle-control state is assumed. -/
theorem native_children_pipeline {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat}
    {parent : Key} {post : Nat} {derived : Bool} {origin : Origin}
    {preparationFuel portFuel : Nat} {prepared : Control} {cursor : Cursor}
    (priorRun : NativeDrainOwnership.Run NativeDrainOwnership.initial origin.control)
    (present : ParentPresent parent (start origin))
    (preparation : prepareAll preparationFuel origin.control = some prepared)
    (computed : NativeValuePorts.drive views qv qe parent post derived portFuel
      (NativeValuePorts.initialCursor origin.arena origin.children []) = some cursor) :
    ∃ emitted : State, emitted.cursor = cursor ∧
      NativeDrainOwnership.Run NativeDrainOwnership.initial emitted.control ∧
      ∀ last, NativeDrainOwnership.Run emitted.control last → last.queue = [] → last.frames = [] →
        ∃ jobs : List Issuance,
          jobs.map (fun job => job.port.source) = origin.children ∧
          ∀ job ∈ jobs,
            job.matches emitted.tasks ∧
            AdmissionResult emitted.cursor.arena views qv qe parent post derived
              job.port.source job.port.receipt ∧
            ∃ returned ∈ last.returns, job.occurrence ∈ returned.frame.processed ∧
              returned.frame.diagnosed = true ∧ returned.frame.phase = .returnReady ∧
              returned.frame.pending = [] ∧ returned.frame.current = none := by
  have active := preflight_parent_active present preparation
  have prior := control_run_trans priorRun (prepare_all_exact preparation).1
  obtain ⟨emitted, executed, same, run, _⟩ := native_drive_constructs_common_run
    (origin := {origin with control := prepared}) active computed
  refine ⟨emitted, same, control_run_trans prior (run_control run), ?_⟩
  intro last continuation queue stack
  exact emitted_children_returned (origin := {origin with control := prepared})
    prior active executed continuation queue stack

/-- The original outer Context/Value computation supplies the actual children
and the actual port-drive equation, rather than a separately chosen child list. -/
theorem context_execution_native_drive
    {contexts : NativeContextExpansion.Tables} {contextFuel : Nat}
    {tables : NativeValueStructure.Tables} {routing : NativeValueStructure.Routing}
    {request : NativeValueStructure.Request}
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {post : Nat}
    {derived : Bool} {portFuel : Nat} {arena : Arena} {cursor : Cursor}
    (computed : NativeValueStructure.executeAfterContext contexts contextFuel tables routing
      request views qv qe post derived portFuel arena [] = some cursor) :
    request.transformer = 0 ∧ routing.candidate = true ∧
    ∃ family items,
      NativeValueStructure.dispatch tables routing request = .body (.children family items) ∧
      NativeValuePorts.drive views qv qe request.key post derived portFuel
        (NativeValuePorts.initialCursor arena items []) = some cursor := by
  unfold NativeValueStructure.executeAfterContext at computed
  cases checked : NativeContextExpansion.valueContext contexts contextFuel request with
  | none => simp [checked] at computed
  | some forwarded =>
      have facts := NativeContextExpansion.value_context_exact checked
      simp only [checked, Option.bind_some, facts.1] at computed
      have candidate := NativeValueStructure.executed_candidate computed
      obtain ⟨family, items, branch, _⟩ := NativeValueStructure.executed_children_readback computed
      refine ⟨facts.2, candidate, family, items, branch, ?_⟩
      simpa only [NativeValueStructure.executeChildren, candidate, Bool.true_eq, ite_true,
        branch] using computed

/-- A computed native outer structural branch, its actual preflight and its
child loop construct one drain prefix and every ensuing quiescent child return.
The incoming origin.children field is replaced by the computed branch's items. -/
theorem context_value_pipeline
    {contexts : NativeContextExpansion.Tables} {contextFuel : Nat}
    {tables : NativeValueStructure.Tables} {routing : NativeValueStructure.Routing}
    {request : NativeValueStructure.Request}
    {views : Nat → Option (Option Nat)} {qv qe : Nat → Nat} {post : Nat}
    {derived : Bool} {origin : Origin} {preparationFuel portFuel : Nat}
    {prepared : Control} {cursor : Cursor}
    (priorRun : NativeDrainOwnership.Run NativeDrainOwnership.initial origin.control)
    (present : ParentPresent request.key (start origin))
    (preparation : prepareAll preparationFuel origin.control = some prepared)
    (computed : NativeValueStructure.executeAfterContext contexts contextFuel tables routing
      request views qv qe post derived portFuel origin.arena [] = some cursor) :
    request.transformer = 0 ∧ routing.candidate = true ∧
    ∃ family items, ∃ emitted : State,
      NativeValueStructure.dispatch tables routing request = .body (.children family items) ∧
      emitted.cursor = cursor ∧
      NativeDrainOwnership.Run NativeDrainOwnership.initial emitted.control ∧
      ∀ last, NativeDrainOwnership.Run emitted.control last → last.queue = [] → last.frames = [] →
        ∃ jobs : List Issuance,
          jobs.map (fun job => job.port.source) = items ∧
          ∀ job ∈ jobs,
            job.matches emitted.tasks ∧
            AdmissionResult emitted.cursor.arena views qv qe request.key post derived
              job.port.source job.port.receipt ∧
            ∃ returned ∈ last.returns, job.occurrence ∈ returned.frame.processed ∧
              returned.frame.diagnosed = true ∧ returned.frame.phase = .returnReady ∧
              returned.frame.pending = [] ∧ returned.frame.current = none := by
  obtain ⟨identity, candidate, family, items, branch, drive⟩ :=
    context_execution_native_drive computed
  have actualParent : ParentPresent request.key (start {origin with children := items}) := present
  obtain ⟨emitted, same, run, returns⟩ := native_children_pipeline
    (origin := {origin with children := items}) priorRun actualParent preparation drive
  exact ⟨identity, candidate, family, items, emitted, branch, same, run, returns⟩

namespace Witness

open NativeDrainOwnership

def parentWork : NativeOccurrence := work initial 0 0 none
def parentFrame : Frame := newFrame initial none
def started : Control :=
  { pushWork initial parentWork false with frames := [parentFrame], nextBirth := 1 }
def activeFrame : Frame := { parentFrame with current := some parentWork, processing := some 0 }
def taken : Control := { started with queue := [], frames := [activeFrame] }

def origin : Origin :=
  ⟨NativeValuePorts.Witness.arena, NativeValuePorts.Witness.children,
    taken, [NativeValuePorts.Witness.parent.pair]⟩

theorem actual_parent_prefix : NativeDrainOwnership.Run initial origin.control := by
  have begins : NativeDrainOwnership.Step initial started := .begin initial 0 0 rfl
  have takes : NativeDrainOwnership.Step started taken :=
    .takePlain started parentFrame [] parentWork [] rfl rfl rfl rfl rfl
  exact ((NativeDrainOwnership.Run.nil initial).snoc begins).snoc takes

theorem actual_parent_lookup : Active NativeValuePorts.Witness.parent (start origin) := by
  exact ⟨⟨activeFrame, [], parentWork, 0, rfl, rfl, rfl, rfl, rfl⟩, rfl⟩

def completed : Option State :=
  emit NativeValuePorts.Witness.views id id NativeValuePorts.Witness.parent 1 true 8 (start origin)

def afterCommit : Control :=
  { NativeDrainOwnership.Witness.transported with
    frames := [{NativeDrainOwnership.Witness.transportedFrame with prepared := 0}] }

theorem commit_reprepares_actual_ack :
    ready afterCommit = false ∧
    prepareAll 1 afterCommit = some NativeDrainOwnership.Witness.transported := ⟨rfl, rfl⟩

theorem actual_commit_rearms :
    NativeDrainOwnership.Step NativeDrainOwnership.Witness.transported afterCommit :=
  .commit _

theorem actual_preparation_run :
    NativeDrainOwnership.Run afterCommit NativeDrainOwnership.Witness.transported :=
  (prepare_all_exact commit_reprepares_actual_ack.2).1

theorem four_ports_issued :
    (completed.map fun state =>
      (state.receipts.length,
       state.receipts.map (fun record => record.occurrence.serial),
       state.control.queue.map NativeDrainOwnership.Work.serial,
       state.control.nextWork,
       state.control.transferred)) = some (4, [1, 2, 3, 4], [4, 3, 2, 1], 5, []) := by decide

theorem original_native_drive_has_shared_history :
    ∃ state,
      completed = some state ∧
      NativeDrainOwnership.Run initial state.control ∧
      state.cursor.todo = [] := by
  obtain ⟨state, computed, _, run, finished⟩ := native_drive_constructs_common_run
    (views := NativeValuePorts.Witness.views) (qv := id) (qe := id)
    (parent := NativeValuePorts.Witness.parent) (post := 1) (derived := true)
    (origin := origin) (fuel := 8) actual_parent_lookup (by rfl)
  exact ⟨state, computed, control_run_trans actual_parent_prefix (run_control run), finished⟩

end Witness

end YulangClosure.NativeValueDrain
