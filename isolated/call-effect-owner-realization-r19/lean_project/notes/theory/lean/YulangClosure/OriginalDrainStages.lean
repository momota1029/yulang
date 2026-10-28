import YulangClosure.OriginalDrainBoundary

/-!
Executable projection of the fourteen native TypedDrainStage field updates.
The underlying Work/Frame identities are those of NativeDrainOwnership.
Semantic call results are explicit readbacks; this module does not execute
Context, extrusion, port admission, settlement, or diagnostic bodies.

The stage/current invariant is proved from initialization and the computed
updates, rather than supplied by a transition constructor. The extra Poll
field records the program counter around the settlement call, not another
native TypedDrainStage. Errors, panic cuts, and truncation are separate.
-/
namespace YulangClosure.OriginalDrainStages

namespace C
export NativeDrainOwnership (State Operation Work Ticket Frame Phase ReturnReceipt AckReceipt)
end C
namespace B
export OriginalDrainBoundary (Owner identity EmptyBoundary)
end B

inductive Stage where
  | transport | context | dispatch
  | functionAdmission | functionEnqueue
  | tupleAdmission | tupleEnqueue
  | recordAdmission | recordEnqueue
  | variantAdmission | variantEnqueue
  | diagnostics | acknowledgements | returnReady
  deriving DecidableEq, Repr

def Stage.phase : Stage → C.Phase
  | .diagnostics => .diagnostics
  | .acknowledgements => .acknowledgements
  | .returnReady => .returnReady
  | _ => .working

inductive Family where
  | function | tuple | record | variant
  deriving DecidableEq, Repr

def Family.admission : Family → Stage
  | .function => .functionAdmission
  | .tuple => .tupleAdmission
  | .record => .recordAdmission
  | .variant => .variantAdmission

def Family.enqueue : Family → Stage
  | .function => .functionEnqueue
  | .tuple => .tupleEnqueue
  | .record => .recordEnqueue
  | .variant => .variantEnqueue

structure Dispatch where
  /-- Exact child task vector; semantic port coordinates are erased here. -/
  children : List Nat
  next : Nat := 0
  pending : Option C.Work := none
  deriving DecidableEq, Repr

inductive Poll where
  | entry | settling | returned
  deriving DecidableEq, Repr

structure Frame where
  core : C.Frame
  stage : Stage := .transport
  contextConsumed : Option Bool := none
  function : Option Dispatch := none
  tuple : Option Dispatch := none
  record : Option Dispatch := none
  variant : Option Dispatch := none
  poll : Poll := .entry
  deriving DecidableEq, Repr

def Frame.project (frame : Frame) : C.Frame :=
  { frame.core with phase := frame.stage.phase }

def Frame.owner (frame : Frame) : B.Owner := B.identity frame.core

def Frame.get (frame : Frame) : Family → Option Dispatch
  | .function => frame.function
  | .tuple => frame.tuple
  | .record => frame.record
  | .variant => frame.variant

def Frame.set (frame : Frame) (family : Family) (dispatch : Option Dispatch) : Frame :=
  match family with
  | .function => {frame with function := dispatch}
  | .tuple => {frame with tuple := dispatch}
  | .record => {frame with record := dispatch}
  | .variant => {frame with variant := dispatch}

def fresh (birth index : Nat) (destination : Option C.Ticket) : Frame :=
  { core := { birth := birth, index := index, destination := destination } }

/-- This records actual current-item shape. It is not a constructor guard. -/
def Frame.Shape (frame : Frame) : Prop :=
  match frame.stage with
  | .transport => True
  | .diagnostics | .acknowledgements | .returnReady => frame.core.current = none
  | _ => ∃ work, frame.core.current = some work

theorem fresh_shape (birth index : Nat) (destination : Option C.Ticket) :
    (fresh birth index destination).Shape := by trivial

theorem working_empty_is_transport {frame : Frame} (shape : frame.Shape)
    (working : frame.project.phase = .working) (empty : frame.project.current = none) :
    frame.stage = .transport := by
  cases stage : frame.stage <;> simp_all [Frame.Shape, Frame.project, Stage.phase]

theorem terminal_current_empty {frame : Frame} (shape : frame.Shape)
    (terminal : frame.stage = .diagnostics ∨ frame.stage = .acknowledgements ∨
      frame.stage = .returnReady) : frame.core.current = none := by
  rcases terminal with stage | stage | stage <;> simpa [Frame.Shape, stage] using shape

inductive Failure where
  | unavailable (code : Nat)
  | missingFrame | staleOwner | invalidCurrent | missingContext | suspendedCall
  /-- Native unwrap/index/unreachable failures are not successful updates. -/
  | panic (code : Nat)
  deriving DecidableEq, Repr

inductive DispatchReturn where
  /-- Every successful dispatch branch that installs no structural continuation. -/
  | finished
  | children (family : Family) (tasks : List Nat)
  deriving DecidableEq, Repr

structure Readback where
  /-- Mutable relation returned by candidate_context_transport_task. -/
  relation : Option Nat
  consumed : Bool
  dispatch : DispatchReturn
  transitions : Nat
  /-- The actual successful port-admission work projection. -/
  admitted : C.Work
  deriving DecidableEq, Repr

structure Update where
  frame : Frame
  enqueue : Option C.Work := none
  take : Bool := false
  returned : Bool := false
  deriving DecidableEq, Repr

def completed (frame : Frame) : Frame :=
  { frame with
    core := {frame.core with
      current := none
      processing := none
      processed := match frame.core.current with
        | none => frame.core.processed
        | some work => frame.core.processed ++ [work] }
    contextConsumed := none
    stage := .transport }

def install (frame : Frame) (family : Family) (tasks : List Nat) : Frame :=
  { frame.set family (some ⟨tasks, 0, none⟩) with stage := family.admission }

/-- The caller checks all four retained dispatch fields after dispatch_live_item
returns. A plain result alone is not a certificate that these fields are empty. -/
def finishDispatch (frame : Frame) : Frame :=
  if frame.function = none ∧ frame.tuple = none ∧ frame.record = none ∧ frame.variant = none
  then completed frame else frame

theorem finish_dispatch_shape {frame : Frame} (shape : frame.Shape) :
    (finishDispatch frame).Shape := by
  unfold finishDispatch
  split
  · trivial
  · exact shape

/-- The four candidate_step_*_dispatch functions have these identical field
updates, with their own payload coordinates erased. Selection is reverse
vector order, and pending work is enqueued before next is advanced. -/
def structural (family : Family) (readback : Readback) (frame : Frame) : Except Failure Update :=
  match frame.get family with
  | none => .error (.panic 0)
  | some dispatch =>
      if dispatch.next = dispatch.children.length then
        .ok {frame := (completed frame).set family none}
      else match dispatch.pending with
        | some work =>
            .ok {frame := {frame.set family (some {dispatch with pending := none, next := dispatch.next + 1})
              with stage := family.admission}, enqueue := some work}
        | none =>
            if dispatch.next < dispatch.children.length then
              match dispatch.children[dispatch.children.length - 1 - dispatch.next]? with
              | none => .error (.panic 1)
              | some task =>
                  .ok {frame := {frame.set family (some {dispatch with
                    pending := some {readback.admitted with task := task}})
                    with stage := family.enqueue}}
            else .error (.panic 1)

/-- Successful native field updates after external calls have returned. The
Transport/None case is the actual post-settlement worklist pop; its ordering
relative to settlement is enforced by the state driver below. -/
def update (readback : Readback) (front : Option C.Work) (dirty : Bool)
    (frame : Frame) : Except Failure Update :=
  match frame.stage with
  | .transport => match frame.core.current with
    | none => match front with
      | some work => .ok {frame := {frame with
          core := {frame.core with
            current := some work
            processing := some work.relation
            pending := match work.ticket with
              | none => frame.core.pending
              | some ticket => frame.core.pending ++ [ticket]
            prepared := if work.ticket.isSome then frame.core.prepared + 1 else frame.core.prepared}
          poll := .entry}, take := true}
      | none => .ok {frame := {frame with
          stage := if dirty then .transport else .diagnostics
          poll := .entry}}
    | some _ => .ok {frame := {frame with
        core := {frame.core with processing := readback.relation}
        stage := .context}}
  | .context => match frame.core.current with
    | none => .error .invalidCurrent
    | some _ => .ok {frame := {frame with contextConsumed := some readback.consumed, stage := .dispatch}}
  | .dispatch => match frame.core.current, frame.contextConsumed with
    | none, _ => .error .invalidCurrent
    | _, none => .error .missingContext
    | some _, some _ =>
        let counted := {frame with core := {frame.core with transitions := readback.transitions}}
        match readback.dispatch with
        | .finished => .ok {frame := finishDispatch counted}
        | .children family tasks => .ok {frame := install counted family tasks}
  | .functionAdmission | .functionEnqueue => structural .function readback frame
  | .tupleAdmission | .tupleEnqueue => structural .tuple readback frame
  | .recordAdmission | .recordEnqueue => structural .record readback frame
  | .variantAdmission | .variantEnqueue => structural .variant readback frame
  | .diagnostics => .ok {frame := {frame with
      core := {frame.core with diagnosed := true}
      stage := .acknowledgements}}
  | .acknowledgements => match frame.core.pending with
    | [] => .ok {frame := {frame with stage := .returnReady}}
    | ticket :: rest => .ok {frame := {frame with
        core := {frame.core with done := frame.core.done ++ [ticket], pending := rest}
        stage := if rest = [] then .returnReady else .acknowledgements}}
  | .returnReady => .ok {frame := frame, returned := true}

private theorem set_core (frame : Frame) (family : Family) (dispatch : Option Dispatch) :
    (frame.set family dispatch).core = frame.core := by cases family <;> rfl

private theorem set_stage (frame : Frame) (family : Family) (dispatch : Option Dispatch) :
    (frame.set family dispatch).stage = frame.stage := by cases family <;> rfl

theorem structural_shape {family : Family} {readback : Readback} {frame : Frame}
    {result : Update} (current : ∃ work, frame.core.current = some work)
    (success : structural family readback frame = .ok result) : result.frame.Shape := by
  unfold structural at success
  split at success
  · cases success
  · split at success
    · cases success
      cases family <;> trivial
    · split at success
      · cases success
        cases family <;> simpa [Frame.Shape, Frame.set, Family.admission] using current
      · split at success
        · split at success
          · cases success
          · cases success
            cases family <;> simpa [Frame.Shape, Frame.set, Family.enqueue] using current
        · cases success

theorem update_shape {readback : Readback} {front : Option C.Work} {dirty : Bool}
    {frame : Frame} {result : Update} (shape : frame.Shape)
    (success : update readback front dirty frame = .ok result) : result.frame.Shape := by
  cases stage : frame.stage <;> simp only [update, stage] at success
  case transport =>
    split at success
    · split at success
      · cases success; trivial
      · cases success; cases dirty <;> simp_all [Frame.Shape]
    · cases success; simp_all [Frame.Shape]
  case context =>
    split at success
    · cases success
    · cases success; simp_all [Frame.Shape]
  case dispatch =>
    split at success
    · cases success
    · cases success
    · cases choice : readback.dispatch with
      | finished =>
        simp only [choice] at success
        cases success
        apply finish_dispatch_shape
        simp_all [Frame.Shape]
      | children family tasks =>
        simp only [choice] at success
        cases success
        cases family <;> simp_all [Frame.Shape, install, Frame.set, Family.admission]
  case functionAdmission | functionEnqueue | tupleAdmission | tupleEnqueue |
      recordAdmission | recordEnqueue | variantAdmission | variantEnqueue =>
    exact structural_shape (by simpa [Frame.Shape, stage] using shape) success
  case diagnostics =>
    cases success; simpa [Frame.Shape, stage] using shape
  case acknowledgements =>
    cases pending : frame.core.pending with
    | nil => simp only [pending] at success; cases success; simpa [Frame.Shape, stage] using shape
    | cons ticket rest =>
      simp only [pending] at success
      cases success
      cases rest <;> simpa [Frame.Shape, stage] using shape
  case returnReady => cases success; exact shape

theorem structural_owner {family : Family} {readback : Readback} {frame : Frame}
    {result : Update} (success : structural family readback frame = .ok result) :
    result.frame.owner = frame.owner := by
  unfold structural at success
  split at success
  · cases success
  · split at success
    · cases success
      cases family <;> rfl
    · split at success
      · cases success
        cases family <;> rfl
      · split at success
        · split at success
          · cases success
          · cases success
            cases family <;> rfl
        · cases success

theorem update_owner {readback : Readback} {front : Option C.Work} {dirty : Bool}
    {frame : Frame} {result : Update}
    (success : update readback front dirty frame = .ok result) :
    result.frame.owner = frame.owner := by
  cases stage : frame.stage <;> simp only [update, stage] at success
  case transport =>
    split at success
    · split at success <;> cases success <;> rfl
    · cases success; rfl
  case context => split at success <;> cases success <;> rfl
  case dispatch =>
    split at success
    · cases success
    · cases success
    · cases choice : readback.dispatch with
      | finished =>
        simp only [choice] at success
        cases success
        unfold finishDispatch
        split <;> rfl
      | children family tasks =>
        simp only [choice] at success
        cases success
        cases family <;> rfl
  case functionAdmission | functionEnqueue | tupleAdmission | tupleEnqueue |
      recordAdmission | recordEnqueue | variantAdmission | variantEnqueue =>
    exact structural_owner success
  case diagnostics => cases success; rfl
  case acknowledgements => split at success <;> cases success <;> rfl
  case returnReady => cases success; rfl

/-! ### Shared native stack and explicit program counter around settlement -/

/-- Fields outside this stage projection are carried as raw readbacks, never
used as stage/current assumptions. No independent control run is chosen. -/
structure Bookkeeping where
  operations : Nat → Option C.Operation := fun _ => none
  nextOperation : Nat := 0
  nextWork : Nat := 0
  issued : List C.Work := []
  transferred : List C.Ticket := []
  acknowledgements : List C.AckReceipt := []
  returns : List C.ReturnReceipt := []

structure State where
  bookkeeping : Bookkeeping := {}
  nextBirth : Nat := 0
  queue : List C.Work := []
  frames : List Frame := []
  dirty : Bool := false

def State.project (state : State) : C.State :=
  { operations := state.bookkeeping.operations
    nextOperation := state.bookkeeping.nextOperation
    nextBirth := state.nextBirth
    nextWork := state.bookkeeping.nextWork
    queue := state.queue
    frames := state.frames.map Frame.project
    issued := state.bookkeeping.issued
    transferred := state.bookkeeping.transferred
    acknowledgements := state.bookkeeping.acknowledgements
    returns := state.bookkeeping.returns }

def initial : State := {}

def Indexed : List Frame → Prop
  | [] => True
  | frame :: rest => frame.core.index = rest.length ∧ Indexed rest

structure Valid (state : State) : Prop where
  shapes : ∀ frame ∈ state.frames, frame.Shape
  indexed : Indexed state.frames
  births : ∀ frame ∈ state.frames, frame.core.birth < state.nextBirth

theorem initial_valid : Valid initial := by
  constructor <;> simp [initial, Indexed]

/-- Only these frame writes occur in successful stage stepping. Opaque
bookkeeping readbacks cannot write the queue, stack, stage, current, or birth
counter. Birth reservation models other native identity allocations. -/
inductive Event where
  | begin (destination : Option C.Ticket)
  | reserveBirth
  | enqueue (work : C.Work) (front : Bool)
  | bookkeeping (data : Bookkeeping)
  | advance (owner : B.Owner) (readback : Readback)
  | settle (owner : B.Owner)
  | settled (owner : B.Owner) (dirty : Bool)
  | prepare (owner : B.Owner) (prepared : Nat)

def nextQueue (queue : List C.Work) (result : Update) : List C.Work :=
  let remaining := if result.take then queue.tail else queue
  match result.enqueue with
  | none => remaining
  | some work => work :: remaining

def advanced (state : State) (rest : List Frame) (result : Update) : State :=
  { state with
    queue := nextQueue state.queue result
    frames := if result.returned then rest else result.frame :: rest
    bookkeeping := if result.returned then
      {state.bookkeeping with returns := state.bookkeeping.returns ++ [⟨result.frame.project⟩]}
      else state.bookkeeping }

/-- The head is the end of the native vector. Both the original slot and the
fresh ghost lifetime must match the suspended caller's saved owner. -/
def withTop (state : State) (owner : B.Owner)
    (body : Frame → List Frame → Except Failure State) : Except Failure State :=
  match state.frames with
  | [] => .error .missingFrame
  | frame :: rest =>
      if frame.owner = owner ∧ frame.core.index = rest.length then body frame rest
      else .error .staleOwner

def advance (state : State) (owner : B.Owner) (readback : Readback) : Except Failure State :=
  withTop state owner fun frame rest =>
    if frame.poll = .settling then .error .suspendedCall
    else if frame.stage = .transport ∧ frame.core.current = none ∧
        state.queue = [] ∧ frame.poll = .entry then .error .suspendedCall
    else match update readback state.queue.head? state.dirty frame with
      | .error failure => .error failure
      | .ok result => .ok (advanced state rest result)

/-- beginSettlement is the cut immediately before settle_candidate_intrusion.
The after-call dirty observation does not determine whether work was produced;
all queue changes are retained on the same State. -/
def apply (event : Event) (state : State) : Except Failure State :=
  match event with
  | .begin destination =>
      if state.queue = [] then
        .ok {state with
          frames := fresh state.nextBirth state.frames.length destination :: state.frames
          nextBirth := state.nextBirth + 1}
      else .error (.panic 2)
  | .reserveBirth => .ok {state with nextBirth := state.nextBirth + 1}
  | .enqueue work front =>
      .ok {state with queue := if front then work :: state.queue else state.queue ++ [work]}
  | .bookkeeping data => .ok {state with bookkeeping := data}
  | .advance owner readback => advance state owner readback
  | .settle owner => withTop state owner fun frame rest =>
      if frame.stage = .transport ∧ frame.core.current = none ∧
          state.queue = [] ∧ frame.poll = .entry then
        .ok {state with frames := {frame with poll := .settling} :: rest}
      else .error .suspendedCall
  | .settled owner dirty => withTop state owner fun frame rest =>
      if frame.poll = .settling then
        .ok {state with frames := {frame with poll := .returned} :: rest, dirty := dirty}
      else .error .suspendedCall
  | .prepare owner prepared => withTop state owner fun frame rest =>
      .ok {state with frames := {frame with core := {frame.core with prepared := prepared}} :: rest}

def execute : List Event → State → Except Failure State
  | [], state => .ok state
  | event :: rest, state => match apply event state with
    | .error failure => .error failure
    | .ok next => execute rest next

private theorem changed_head_valid {state : State} {frame changed : Frame} {rest : List Frame}
    (valid : Valid state) (top : state.frames = frame :: rest)
    (shape : changed.Shape) (owner : changed.owner = frame.owner) :
    Valid {state with frames := changed :: rest} := by
  have index := congrArg (fun identity : B.Owner => identity.index) owner
  have birth := congrArg (fun identity : B.Owner => identity.birth) owner
  change changed.core.index = frame.core.index at index
  change changed.core.birth = frame.core.birth at birth
  constructor
  · intro item member
    rcases List.mem_cons.mp member with rfl | later
    · exact shape
    · exact valid.shapes item (by simp [top, later])
  · simpa [Indexed, index, top] using valid.indexed
  · intro item member
    rcases List.mem_cons.mp member with rfl | later
    · rw [birth]
      exact valid.births frame (by simp [top])
    · exact valid.births item (by simp [top, later])

private theorem advanced_valid {state : State} {frame : Frame} {rest : List Frame}
    {result : Update} (valid : Valid state) (top : state.frames = frame :: rest)
    (shape : result.frame.Shape) (owner : result.frame.owner = frame.owner) :
    Valid (advanced state rest result) := by
  have replace := changed_head_valid valid top shape owner
  have old := valid.indexed
  rw [top] at old
  cases returned : result.returned
  · exact ⟨by simpa [advanced, returned] using replace.shapes,
      by simpa [advanced, returned] using replace.indexed,
      by simpa [advanced, returned] using replace.births⟩
  · constructor
    · intro item member
      exact valid.shapes item (by simp_all [advanced])
    · simpa [advanced, returned] using old.2
    · intro item member
      exact valid.births item (by simp_all [advanced])

theorem advance_valid {state after : State} {owner : B.Owner} {readback : Readback}
    (valid : Valid state) (success : advance state owner readback = .ok after) : Valid after := by
  unfold advance withTop at success
  split at success
  · cases success
  · rename_i frame rest top
    split at success
    · dsimp only at success
      split at success
      · cases success
      · split at success
        · cases success
        · split at success
          · cases success
          · rename_i result updated
            cases success
            exact advanced_valid valid top
              (update_shape (valid.shapes frame (by simp [top])) updated) (update_owner updated)
    · cases success

theorem apply_valid {state after : State} {event : Event} (valid : Valid state)
    (success : apply event state = .ok after) : Valid after := by
  cases event with
  | begin destination =>
    simp only [apply] at success
    split at success
    · cases success
      constructor
      · intro frame member
        rcases List.mem_cons.mp member with rfl | previous
        · exact fresh_shape _ _ _
        · exact valid.shapes frame previous
      · exact ⟨rfl, valid.indexed⟩
      · intro frame member
        rcases List.mem_cons.mp member with rfl | previous
        · simp [fresh]
        · exact Nat.lt_succ_of_lt (valid.births frame previous)
    · cases success
  | reserveBirth =>
    cases success
    exact ⟨valid.shapes, valid.indexed, fun frame member => Nat.lt_succ_of_lt (valid.births frame member)⟩
  | enqueue work front => cases success; exact ⟨valid.shapes, valid.indexed, valid.births⟩
  | bookkeeping data => cases success; exact ⟨valid.shapes, valid.indexed, valid.births⟩
  | advance owner readback => exact advance_valid valid success
  | settle owner =>
    simp only [apply, withTop] at success
    split at success
    · cases success
    · rename_i frame rest top
      split at success
      · split at success
        · cases success
          exact changed_head_valid (changed := {frame with poll := .settling})
            valid top (valid.shapes frame (by simp [top])) rfl
        · cases success
      · cases success
  | settled owner dirty =>
    simp only [apply, withTop] at success
    split at success
    · cases success
    · rename_i frame rest top
      split at success
      · split at success
        · cases success
          have kept := changed_head_valid (changed := {frame with poll := .returned})
            valid top (valid.shapes frame (by simp [top])) rfl
          exact ⟨kept.shapes, kept.indexed, kept.births⟩
        · cases success
      · cases success
  | prepare owner prepared =>
    simp only [apply, withTop] at success
    split at success
    · cases success
    · rename_i frame rest top
      split at success
      · cases success
        exact changed_head_valid (changed := {frame with core := {frame.core with prepared := prepared}})
          valid top (valid.shapes frame (by simp [top])) rfl
      · cases success

theorem execute_valid {events : List Event} {start last : State} (valid : Valid start)
    (success : execute events start = .ok last) : Valid last := by
  induction events generalizing start with
  | nil => cases success; exact valid
  | cons event events ih =>
    simp only [execute] at success
    cases step : apply event start with
    | error failure => simp [step] at success
    | ok next => exact ih (apply_valid valid step) (by simpa [step] using success)

theorem initialized_valid {events : List Event} {last : State}
    (success : execute events initial = .ok last) : Valid last :=
  execute_valid initial_valid success

/-! ### The original EmptyBoundary, with its actual indexed stage owner -/

theorem projected_empty_boundary_iff {state : State} {owner : B.Owner} (valid : Valid state) :
    B.EmptyBoundary owner state.project ↔
      ∃ frame rest, state.frames = frame :: rest ∧ frame.owner = owner ∧
        frame.stage = .transport ∧ frame.core.current = none ∧ state.queue = [] := by
  constructor
  · rintro ⟨projected, tail, top, same, working, emptyCurrent, emptyQueue⟩
    cases frames : state.frames with
    | nil => simp [State.project, frames] at top
    | cons frame rest =>
      have heads : frame.project = projected ∧ rest.map Frame.project = tail := by
        simpa [State.project, frames] using top
      rcases heads with ⟨rfl, rfl⟩
      exact ⟨frame, rest, rfl, same,
        working_empty_is_transport (valid.shapes frame (by simp [frames])) working emptyCurrent,
        emptyCurrent, emptyQueue⟩
  · rintro ⟨frame, rest, top, same, stage, current, empty⟩
    exact ⟨frame.project, rest.map Frame.project, by simp [State.project, top], same,
      by simp [Frame.project, stage, Stage.phase], current, empty⟩

/-- No complete native Run or stage invariant is an input: the actual finite
sequence of readback events is executed from initialization, then the frozen
boundary predicate identifies the same original birth/index frame. -/
theorem initialized_boundary_is_transport {events : List Event} {state : State} {owner : B.Owner}
    (executed : execute events initial = .ok state)
    (boundary : B.EmptyBoundary owner state.project) :
    ∃ frame rest, state.frames = frame :: rest ∧ frame.owner = owner ∧
      frame.core.index = rest.length ∧ frame.core.birth = owner.birth ∧
      frame.stage = .transport ∧ frame.core.current = none ∧ state.queue = [] := by
  have valid := initialized_valid executed
  obtain ⟨frame, rest, top, same, stage, current, empty⟩ :=
    (projected_empty_boundary_iff valid).mp boundary
  have ordered := valid.indexed
  rw [top] at ordered
  have birth := congrArg (fun identity : B.Owner => identity.birth) same
  exact ⟨frame, rest, top, same, ordered.1, birth, stage, current, empty⟩

/-- The exact successful entry to settlement records the already-empty
Transport cut. It does not wait for a clean/diagnosed settlement result. -/
theorem settlement_starts_at_boundary {state after : State} {owner : B.Owner}
    (success : apply (.settle owner) state = .ok after) :
    B.EmptyBoundary owner state.project := by
  simp only [apply, withTop] at success
  split at success
  · cases success
  · rename_i frame rest top
    split at success
    · rename_i same
      split at success
      · rename_i entry
        exact ⟨frame.project, rest.map Frame.project, by simp [State.project, top], same.1,
          by simp [Frame.project, entry.1, Stage.phase], entry.2.1, entry.2.2.1⟩
      · cases success
    · cases success

theorem boundary_enters_settlement {state : State} {frame : Frame} {rest : List Frame}
    (valid : Valid state) (top : state.frames = frame :: rest)
    (boundary : B.EmptyBoundary frame.owner state.project) (entry : frame.poll = .entry) :
    apply (.settle frame.owner) state =
      .ok {state with frames := {frame with poll := .settling} :: rest} := by
  obtain ⟨actual, tail, frames, same, stage, current, empty⟩ :=
    (projected_empty_boundary_iff valid).mp boundary
  rw [top] at frames
  obtain ⟨rfl, rfl⟩ := List.cons.inj frames
  have ordered := valid.indexed
  rw [top] at ordered
  simp [apply, withTop, top, ordered.1, stage, current, empty, entry]

/-- A dirty settlement with no work leaves Transport. This is the actual
branch that prevents replacing an empty boundary by Diagnostics. -/
theorem dirty_empty_stays_transport (readback : Readback) (frame : Frame)
    (stage : frame.stage = .transport) (current : frame.core.current = none) :
    update readback none true frame =
      .ok {frame := {frame with stage := .transport, poll := .entry}} := by
  simp [update, stage, current]

theorem clean_empty_enters_diagnostics (readback : Readback) (frame : Frame)
    (stage : frame.stage = .transport) (current : frame.core.current = none) :
    update readback none false frame =
      .ok {frame := {frame with stage := .diagnostics, poll := .entry}} := by
  simp [update, stage, current]

/-! ### Suspended callers retain the entire saved frame, not just its slot -/

theorem indexed_member {frames : List Frame} {frame : Frame}
    (indexed : Indexed frames) (member : frame ∈ frames) : frame.core.index < frames.length := by
  induction frames with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | later
    · simp [indexed.1]
    · exact Nat.lt_succ_of_lt (ih indexed.2 later)

theorem apply_keeps_suspended {state after : State} {event : Event}
    {head saved : Frame} {rest : List Frame}
    (top : state.frames = head :: rest) (held : saved ∈ rest)
    (success : apply event state = .ok after) : saved ∈ after.frames := by
  cases event with
  | begin destination =>
    simp only [apply] at success
    split at success
    · cases success; simp [top, held]
    · cases success
  | reserveBirth => cases success; simp [top, held]
  | enqueue work front => cases success; simp [top, held]
  | bookkeeping data => cases success; simp [top, held]
  | advance owner readback =>
    simp only [apply, advance, withTop, top] at success
    split at success
    · split at success
      · cases success
      · split at success
        · cases success
        · split at success
          · cases success
          · rename_i result updated
            cases success
            by_cases returned : result.returned = true <;> simp [advanced, returned, held]
    · cases success
  | settle owner =>
    simp only [apply, withTop, top] at success
    split at success
    · split at success
      · cases success; simp [held]
      · cases success
    · cases success
  | settled owner dirty =>
    simp only [apply, withTop, top] at success
    split at success
    · split at success
      · cases success; simp [held]
      · cases success
    · cases success
  | prepare owner prepared =>
    simp only [apply, withTop, top] at success
    split at success
    · cases success; simp [held]
    · cases success

def topOwner (state : State) : Option B.Owner := state.frames.head?.map Frame.owner

theorem same_top_is_saved_frame {state : State} {saved : Frame} (valid : Valid state)
    (held : saved ∈ state.frames) (same : topOwner state = some saved.owner) :
    ∃ rest, state.frames = saved :: rest := by
  cases top : state.frames with
  | nil => simp [top] at held
  | cons head rest =>
    have identified : head.owner = saved.owner := by simpa [topOwner, top] using same
    have ordered := valid.indexed
    rw [top] at ordered held
    rcases List.mem_cons.mp held with rfl | later
    · exact ⟨rest, rfl⟩
    · have below := indexed_member ordered.2 later
      have sameIndex := congrArg (fun identity : B.Owner => identity.index) identified
      change head.core.index = saved.core.index at sameIndex
      have position := ordered.1
      omega

/-- Execute the recorded nested native events until the original saved owner
is again the top frame. Exhausting the trace earlier is an error, not a claim
that a nested drain terminates. No later reuse of the same index is accepted. -/
def resume (owner : B.Owner) (events : List Event) (state : State) : Except Failure State :=
  if topOwner state = some owner then .ok state
  else match events with
    | [] => .error .suspendedCall
    | event :: rest => match apply event state with
      | .error failure => .error failure
      | .ok next => resume owner rest next
termination_by events.length

theorem resume_same_frame {events : List Event} {start last : State} {saved : Frame}
    (valid : Valid start) (held : saved ∈ start.frames)
    (success : resume saved.owner events start = .ok last) :
    ∃ rest, last.frames = saved :: rest := by
  induction events generalizing start with
  | nil =>
    rw [resume] at success
    split at success
    · rename_i same
      cases success
      exact same_top_is_saved_frame valid held same
    · cases success
  | cons event events ih =>
    rw [resume] at success
    split at success
    · rename_i same
      cases success
      exact same_top_is_saved_frame valid held same
    · rename_i suspended
      cases step : apply event start with
      | error failure => simp [step] at success
      | ok next =>
        have still : saved ∈ next.frames := by
          cases top : start.frames with
          | nil => simp [top] at held
          | cons head rest =>
            rw [top] at held
            rcases List.mem_cons.mp held with rfl | later
            · exact False.elim (suspended (by simp [topOwner, top]))
            · exact apply_keeps_suspended top later step
        exact ih (apply_valid valid step) still (by simpa [step] using success)

theorem initialized_resume_same_frame {history events : List Event}
    {start last : State} {saved : Frame}
    (initialized : execute history initial = .ok start)
    (held : saved ∈ start.frames)
    (returned : resume saved.owner events start = .ok last) :
    ∃ rest, last.frames = saved :: rest :=
  resume_same_frame (initialized_valid initialized) held returned

/-- The caller's actual Transport frame survives a completed nested call.
The boundary conclusion uses that exact saved frame, including its birth,
slot, stage and current value, rather than selecting one by final depth. -/
theorem resumed_transport_boundary {history events : List Event}
    {start last : State} {saved : Frame}
    (initialized : execute history initial = .ok start)
    (held : saved ∈ start.frames)
    (returned : resume saved.owner events start = .ok last)
    (stage : saved.stage = .transport) (current : saved.core.current = none)
    (empty : last.queue = []) : B.EmptyBoundary saved.owner last.project := by
  obtain ⟨rest, top⟩ := initialized_resume_same_frame initialized held returned
  exact ⟨saved.project, rest.map Frame.project, by simp [State.project, top], rfl,
    by simp [Frame.project, stage, Stage.phase], current, empty⟩

/-! ### Errors and cleanup are outside successful event histories -/

structure FailureCut where
  failure : Failure
  state : State

/-- Native Vec::truncate retains the oldest saved frames. The list is reversed
in the shared projection. No normal Run or quiescence claim crosses this cut;
the Some-replay operation lookup/global restoration is owned by ReplayDrain. -/
def truncateFailure (savedCount : Nat) (cut : FailureCut) : FailureCut :=
  {cut with state := {cut.state with
    frames := cut.state.frames.drop (cut.state.frames.length - savedCount)}}

theorem truncate_keeps_queue (savedCount : Nat) (cut : FailureCut) :
    (truncateFailure savedCount cut).state.queue = cut.state.queue := rfl

theorem truncate_survivor_is_original {savedCount : Nat} {cut : FailureCut} {frame : Frame}
    (survives : frame ∈ (truncateFailure savedCount cut).state.frames) :
    frame ∈ cut.state.frames :=
  List.mem_of_mem_drop survives

theorem truncate_survivor_shape {savedCount : Nat} {cut : FailureCut} {frame : Frame}
    (before : Valid cut.state)
    (survives : frame ∈ (truncateFailure savedCount cut).state.frames) : frame.Shape :=
  before.shapes frame (truncate_survivor_is_original survives)

end YulangClosure.OriginalDrainStages
