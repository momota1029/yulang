import YulangClosure.OriginalDrainFrontier

/-!
Conservation of actual queued work through the computed fourteen-stage
machine. Historical processed witnesses are retained in the exact event
trace, independently of the opaque operation/receipt bookkeeping readback.
This is a local control supplier for NQ §5.2, not native extraction or NQ.
-/
namespace YulangClosure.OriginalStageWorkConservation

open OriginalDrainStages
open OriginalDrainBoundary (Owner EmptyBoundary)
open NativeDrainOwnership (Work)

def Held (work : Work) (before after : Frame) : Prop :=
  after.core.current = some work ∨
    (after.core.current = none ∧ after.core.processed = before.core.processed ++ [work])

theorem structural_current {family : Family} {readback : Readback}
    {frame : Frame} {result : Update} {work : Work}
    (current : frame.core.current = some work)
    (success : structural family readback frame = .ok result) : Held work frame result.frame := by
  unfold structural at success
  split at success
  · cases success
  · split at success
    · cases success
      cases family <;> simp [Held, Frame.set, completed, current]
    · split at success
      · cases success
        cases family <;> exact Or.inl current
      · split at success
        · split at success
          · cases success
          · cases success
            cases family <;> exact Or.inl current
        · cases success

theorem update_current {readback : Readback} {front : Option Work} {dirty : Bool}
    {frame : Frame} {result : Update} {work : Work}
    (current : frame.core.current = some work)
    (success : update readback front dirty frame = .ok result) : Held work frame result.frame := by
  cases stage : frame.stage <;> simp only [update, stage, current] at success
  case transport => cases success; exact Or.inl rfl
  case context => cases success; exact Or.inl current
  case dispatch =>
    split at success
    · cases success
    · cases success
    · cases choice : readback.dispatch with
      | finished =>
        simp only [choice] at success
        cases success
        unfold finishDispatch
        split
        · simp [Held, completed]
        · exact Or.inl rfl
      | children family tasks =>
        simp only [choice] at success
        cases success
        cases family <;> exact Or.inl rfl
  case functionAdmission | functionEnqueue | tupleAdmission | tupleEnqueue |
      recordAdmission | recordEnqueue | variantAdmission | variantEnqueue =>
    exact structural_current current success
  case diagnostics => cases success; exact Or.inl rfl
  case acknowledgements =>
    split at success <;> cases success
    · exact Or.inl current
    · exact Or.inl rfl
  case returnReady => cases success; exact Or.inl current

theorem structural_not_returned {family : Family} {readback : Readback}
    {frame : Frame} {result : Update}
    (success : structural family readback frame = .ok result) : result.returned = false := by
  unfold structural at success
  split at success
  · cases success
  · split at success
    · cases success; rfl
    · split at success
      · cases success; rfl
      · split at success
        · split at success
          · cases success
          · cases success; rfl
        · cases success

theorem returned_is_ready {readback : Readback} {front : Option Work} {dirty : Bool}
    {frame : Frame} {result : Update}
    (success : update readback front dirty frame = .ok result)
    (returned : result.returned = true) : frame.stage = .returnReady := by
  cases stage : frame.stage <;> simp only [update, stage] at success
  case transport =>
    split at success
    · split at success <;> cases success <;> cases returned
    · cases success; cases returned
  case context => split at success <;> cases success; cases returned
  case dispatch =>
    split at success
    · cases success
    · cases success
    · cases choice : readback.dispatch <;> simp only [choice] at success <;>
        cases success <;> cases returned
  case functionAdmission | functionEnqueue | tupleAdmission | tupleEnqueue |
      recordAdmission | recordEnqueue | variantAdmission | variantEnqueue =>
    rw [structural_not_returned success] at returned
    cases returned
  case diagnostics => cases success; cases returned
  case acknowledgements => split at success <;> cases success <;> cases returned
  case returnReady => rfl

theorem active_not_returned {readback : Readback} {front : Option Work} {dirty : Bool}
    {frame : Frame} {result : Update} {work : Work}
    (shape : frame.Shape) (current : frame.core.current = some work)
    (success : update readback front dirty frame = .ok result) : result.returned = false := by
  cases resultCase : result.returned with
  | false => rfl
  | true =>
    have stage := returned_is_ready success resultCase
    have empty : frame.core.current = none := by simpa only [Frame.Shape, stage] using shape
    rw [current] at empty
    cases empty

def Working (owner : Owner) (state : State) : Prop :=
  ∃ frame ∈ state.frames, frame.owner = owner ∧ frame.stage.phase = .working

theorem structural_working {family : Family} {readback : Readback}
    {frame : Frame} {result : Update}
    (success : structural family readback frame = .ok result) :
    result.frame.stage.phase = .working := by
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

theorem update_working {readback : Readback} {front : Option Work} {dirty : Bool}
    {frame : Frame} {result : Update}
    (working : frame.stage.phase = .working)
    (available : frame.core.current = none → front ≠ none)
    (success : update readback front dirty frame = .ok result) :
    result.frame.stage.phase = .working ∧ result.returned = false := by
  have notReturned : result.returned = false := by
    cases returned : result.returned with
    | false => rfl
    | true =>
      have stage := returned_is_ready success returned
      simp [stage, Stage.phase] at working
  refine ⟨?_, notReturned⟩
  cases stage : frame.stage <;> simp only [Stage.phase, stage] at working
  case transport =>
    simp only [update, stage] at success
    split at success
    · rename_i empty
      cases front with
      | none => exact False.elim (available empty rfl)
      | some head => cases success; rfl
    · cases success; rfl
  case context => simp only [update, stage] at success; split at success <;> cases success; rfl
  case dispatch =>
    simp only [update, stage] at success
    split at success
    · cases success
    · cases success
    · cases choice : readback.dispatch with
      | finished =>
        simp only [choice] at success
        cases success
        unfold finishDispatch
        split
        · rfl
        · rfl
      | children family tasks =>
        simp only [choice] at success
        cases success
        cases family <;> rfl
  case functionAdmission | functionEnqueue | tupleAdmission | tupleEnqueue |
      recordAdmission | recordEnqueue | variantAdmission | variantEnqueue =>
    exact structural_working (by simpa only [update, stage] using success)
  case diagnostics | acknowledgements | returnReady => cases working

theorem advanced_working {owner : Owner} {state : State} {head : Frame}
    {rest : List Frame} {readback : Readback} {result : Update}
    (top : state.frames = head :: rest) (same : head.owner = owner)
    (working : head.stage.phase = .working)
    (before : ¬ EmptyBoundary owner state.project)
    (success : update readback state.queue.head? state.dirty head = .ok result) :
    Working owner (advanced state rest result) := by
  have available : head.core.current = none → state.queue.head? ≠ none := by
    intro current empty
    exact before ⟨head.project, rest.map Frame.project,
      by simp only [State.project, top, List.map_cons], same, working, current,
      by cases queue : state.queue with
         | nil => exact queue
         | cons first rest => simp only [queue, List.head?_cons, reduceCtorEq] at empty⟩
  obtain ⟨phase, returned⟩ := update_working working available success
  exact ⟨result.frame, by simp only [advanced, returned, Bool.false_eq_true]; exact List.mem_cons_self,
    (update_owner success).trans same, phase⟩

theorem apply_working {owner : Owner} {state after : State} {event : Event}
    (live : Working owner state) (before : ¬ EmptyBoundary owner state.project)
    (success : apply event state = .ok after) : Working owner after := by
  obtain ⟨frame, member, same, working⟩ := live
  cases top : state.frames with
  | nil => simp only [top, List.not_mem_nil] at member
  | cons head rest =>
    rw [top] at member
    rcases List.mem_cons.mp member with rfl | held
    · cases event with
      | begin destination =>
        simp only [apply] at success
        split at success
        · cases success
          exact ⟨frame, by simp [top], same, working⟩
        · cases success
      | reserveBirth => cases success; exact ⟨frame, by simp [top], same, working⟩
      | enqueue work front => cases success; exact ⟨frame, by simp [top], same, working⟩
      | bookkeeping data => cases success; exact ⟨frame, by simp [top], same, working⟩
      | advance target readback =>
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
                exact advanced_working top same working before updated
        · cases success
      | settle target =>
        simp only [apply, withTop, top] at success
        split at success
        · split at success
          · cases success; exact ⟨_, List.mem_cons_self, same, working⟩
          · cases success
        · cases success
      | settled target dirty =>
        simp only [apply, withTop, top] at success
        split at success
        · split at success
          · cases success; exact ⟨_, List.mem_cons_self, same, working⟩
          · cases success
        · cases success
      | prepare target prepared =>
        simp only [apply, withTop, top] at success
        split at success
        · cases success; exact ⟨_, List.mem_cons_self, same, working⟩
        · cases success
    · exact ⟨frame, apply_keeps_suspended top held success, same, working⟩

theorem structural_not_take {family : Family} {readback : Readback}
    {frame : Frame} {result : Update}
    (success : structural family readback frame = .ok result) : result.take = false := by
  unfold structural at success
  split at success
  · cases success
  · split at success
    · cases success; rfl
    · split at success
      · cases success; rfl
      · split at success
        · split at success
          · cases success
          · cases success; rfl
        · cases success

theorem update_take {readback : Readback} {front : Option Work} {dirty : Bool}
    {frame : Frame} {result : Update}
    (success : update readback front dirty frame = .ok result) (taken : result.take = true) :
    ∃ work, front = some work ∧ result.frame.core.current = some work ∧ result.returned = false := by
  cases stage : frame.stage <;> simp only [update, stage] at success
  case transport =>
    split at success
    · cases choice : front with
      | none => simp only [choice] at success; cases success; cases taken
      | some work =>
        simp only [choice] at success
        cases success
        exact ⟨work, rfl, rfl, rfl⟩
    · cases success; cases taken
  case context => split at success <;> cases success; cases taken
  case dispatch =>
    split at success
    · cases success
    · cases success
    · cases choice : readback.dispatch <;> simp only [choice] at success <;>
        cases success <;> cases taken
  case functionAdmission | functionEnqueue | tupleAdmission | tupleEnqueue |
      recordAdmission | recordEnqueue | variantAdmission | variantEnqueue =>
    rw [structural_not_take success] at taken
    cases taken
  case diagnostics => cases success; cases taken
  case acknowledgements => split at success <;> cases success <;> cases taken
  case returnReady => cases success; cases taken

theorem next_queue_keeps {queue : List Work} {result : Update} {work : Work}
    (member : work ∈ if result.take then queue.tail else queue) :
    work ∈ nextQueue queue result := by
  cases enqueued : result.enqueue with
  | none => simpa only [nextQueue, enqueued] using member
  | some head =>
    simp only [nextQueue, enqueued]
    exact List.mem_cons_of_mem head member

theorem advanced_keeps_tail {state : State} {rest : List Frame} {result : Update}
    {frame : Frame} (member : frame ∈ rest) : frame ∈ (advanced state rest result).frames := by
  cases returned : result.returned <;> simp [advanced, returned, member]

theorem live_top_above {owner : Owner} {state : State} {head : Frame} {rest : List Frame}
    (valid : Valid state) (live : Working owner state) (top : state.frames = head :: rest) :
    owner.index ≤ head.core.index := by
  obtain ⟨frame, member, same, _⟩ := live
  have named := congrArg Owner.index same
  change frame.core.index = owner.index at named
  have indexed := valid.indexed
  rw [top] at indexed member
  rcases List.mem_cons.mp member with rfl | later
  · omega
  · have below := indexed_member indexed.2 later
    have position := indexed.1
    omega

def InFlight (owner : Owner) (work : Work) (state : State) : Prop :=
  work ∈ state.queue ∨ ∃ frame ∈ state.frames,
    owner.index ≤ frame.core.index ∧ frame.core.current = some work

def Processed (work : Work) (state : State) : Prop :=
  ∃ frame ∈ state.frames, work ∈ frame.core.processed

/-- A new completion appends this entire admitted occurrence during the
actual transition. Merely finding an older processed record is insufficient.
The completing frame may be nested above the original working owner. -/
def Completed (work : Work) (before after : State) : Prop :=
  ∃ head rest changed,
    before.frames = head :: rest ∧ head.core.current = some work ∧
    after.frames = changed :: rest ∧ changed.owner = head.owner ∧
    changed.core.current = none ∧ changed.core.processed = head.core.processed ++ [work]

theorem completed_processed {work : Work} {before after : State}
    (completed : Completed work before after) : Processed work after := by
  obtain ⟨head, rest, changed, _, _, top, _, _, appended⟩ := completed
  refine ⟨changed, ?_, ?_⟩
  · rw [top]; exact List.mem_cons_self
  · simp [appended]

theorem advanced_flight {owner : Owner} {work : Work} {state : State}
    {head : Frame} {rest : List Frame} {readback : Readback} {result : Update}
    (valid : Valid state) (live : Working owner state) (top : state.frames = head :: rest)
    (success : update readback state.queue.head? state.dirty head = .ok result)
    (flight : InFlight owner work state) :
    InFlight owner work (advanced state rest result) ∨ Completed work state (advanced state rest result) := by
  have index := congrArg Owner.index (update_owner success)
  change result.frame.core.index = head.core.index at index
  rcases flight with queued | ⟨held, member, above, current⟩
  · cases taking : result.take with
    | false =>
      left; left
      apply next_queue_keeps
      simpa only [taking, Bool.false_eq_true, ↓reduceIte] using queued
    | true =>
      obtain ⟨selected, front, current, returned⟩ := update_take success taking
      cases queue : state.queue with
      | nil => simp only [queue, List.not_mem_nil] at queued
      | cons first tail =>
        have selectedSame : first = selected := by
          simpa only [queue, List.head?_cons, Option.some.injEq] using front
        rw [queue] at queued
        rcases List.mem_cons.mp queued with sameWork | later
        · left; right
          refine ⟨result.frame, ?_, ?_, ?_⟩
          · simp only [advanced, returned, Bool.false_eq_true]; exact List.mem_cons_self
          · rw [index]
            exact live_top_above valid live top
          · exact current.trans (congrArg some (sameWork.trans selectedSame).symm)
        · left; left
          apply next_queue_keeps
          simpa only [taking, queue, List.tail_cons, ↓reduceIte] using later
  · rw [top] at member
    rcases List.mem_cons.mp member with sameFrame | later
    · subst held
      have shape := valid.shapes head (by rw [top]; exact List.mem_cons_self)
      have returned := active_not_returned shape current success
      have retained : result.frame ∈ (advanced state rest result).frames := by
        simp only [advanced, returned, Bool.false_eq_true, ↓reduceIte]
        exact List.mem_cons_self
      rcases update_current current success with active | ⟨idle, appended⟩
      · exact Or.inl (Or.inr ⟨result.frame, retained, by simpa only [index] using above, active⟩)
      · refine Or.inr ⟨head, rest, result.frame, top, current, ?_, update_owner success, idle, appended⟩
        simp [advanced, returned]
    · exact Or.inl (Or.inr ⟨held, advanced_keeps_tail later, above, current⟩)

theorem replace_flight {owner : Owner} {work : Work} {state : State}
    {head changed : Frame} {rest : List Frame} (top : state.frames = head :: rest)
    (index : changed.core.index = head.core.index)
    (current : changed.core.current = head.core.current) (flight : InFlight owner work state) :
    InFlight owner work {state with frames := changed :: rest} := by
  rcases flight with queued | ⟨held, member, above, active⟩
  · exact Or.inl queued
  · rw [top] at member
    rcases List.mem_cons.mp member with same | later
    · subst held
      exact Or.inr ⟨changed, List.mem_cons_self, by simpa only [index] using above,
        current.trans active⟩
    · exact Or.inr ⟨held, List.mem_cons_of_mem changed later, above, active⟩

theorem push_frame_flight {owner : Owner} {work : Work} {state : State}
    (head : Frame) (flight : InFlight owner work state) :
    InFlight owner work {state with frames := head :: state.frames} := by
  rcases flight with queued | ⟨held, member, above, current⟩
  · exact Or.inl queued
  · exact Or.inr ⟨held, List.mem_cons_of_mem head member, above, current⟩

theorem apply_flight {owner : Owner} {work : Work} {state after : State} {event : Event}
    (valid : Valid state) (live : Working owner state) (flight : InFlight owner work state)
    (success : apply event state = .ok after) :
    InFlight owner work after ∨ Completed work state after := by
  cases event with
  | begin destination =>
    simp only [apply] at success
    split at success
    · cases success
      exact Or.inl (push_frame_flight _ flight)
    · cases success
  | reserveBirth => cases success; exact Or.inl flight
  | bookkeeping data => cases success; exact Or.inl flight
  | enqueue added front =>
    cases success
    left
    rcases flight with queued | held
    · left
      cases front <;> simp [queued]
    · exact Or.inr held
  | advance target readback =>
    simp only [apply, advance, withTop] at success
    split at success
    · cases success
    · rename_i head rest top
      split at success
      · split at success
        · cases success
        · split at success
          · cases success
          · split at success
            · cases success
            · rename_i result updated
              cases success
              exact advanced_flight valid live top updated flight
      · cases success
  | settle target =>
    simp only [apply, withTop] at success
    split at success
    · cases success
    · rename_i head rest top
      split at success
      · split at success
        · cases success
          exact Or.inl (replace_flight (changed := {head with poll := .settling}) top rfl rfl flight)
        · cases success
      · cases success
  | settled target dirty =>
    simp only [apply, withTop] at success
    split at success
    · cases success
    · rename_i head rest top
      split at success
      · split at success
        · cases success
          exact Or.inl (replace_flight (changed := {head with poll := .returned}) top rfl rfl flight)
        · cases success
      · cases success
  | prepare target prepared =>
    simp only [apply, withTop] at success
    split at success
    · cases success
    · rename_i head rest top
      split at success
      · cases success
        exact Or.inl (replace_flight
          (changed := {head with core := {head.core with prepared := prepared}}) top rfl rfl flight)
      · cases success

theorem enqueue_flight {owner : Owner} {work : Work} {state after : State} {front : Bool}
    (success : apply (.enqueue work front) state = .ok after) : InFlight owner work after := by
  cases success
  left
  cases front <;> simp

/-- Actual states visited by this exact event list, including its starting
state. An error stops the trace; it is not replaced by a successful state. -/
def states : List Event → State → List State
  | [], state => [state]
  | event :: rest, state => state :: match apply event state with
    | .error _ => []
    | .ok next => states rest next

/-- Every before-state of this exact successful prefix is before this
owner's boundary. The endpoint is deliberately not excluded. -/
def NoEarlier (owner : Owner) : List Event → State → Prop
  | [], _ => True
  | event :: rest, state => ¬ EmptyBoundary owner state.project ∧
      match apply event state with
      | .error _ => True
      | .ok next => NoEarlier owner rest next

theorem states_start (events : List Event) (state : State) : state ∈ states events state := by
  cases events <;> simp [states]

theorem states_step {event : Event} {events : List Event} {state next cut : State}
    (step : apply event state = .ok next) (member : cut ∈ states events next) :
    cut ∈ states (event :: events) state := by
  simp only [states, step]
  exact List.mem_cons_of_mem state member

theorem conserve {owner : Owner} {work : Work} {events : List Event} {state last : State}
    (valid : Valid state) (live : Working owner state) (flight : InFlight owner work state)
    (before : NoEarlier owner events state) (computed : execute events state = .ok last) :
    InFlight owner work last ∨ ∃ cut ∈ states events state, Processed work cut := by
  induction events generalizing state with
  | nil => cases computed; exact Or.inl flight
  | cons event events ih =>
    cases step : apply event state with
    | error failure => simp only [execute, step, reduceCtorEq] at computed
    | ok next =>
      have free : ¬ EmptyBoundary owner state.project ∧ NoEarlier owner events next := by
        simpa only [NoEarlier, step] using before
      have ran : execute events next = .ok last := by simpa only [execute, step] using computed
      rcases apply_flight valid live flight step with active | processed
      · rcases ih (apply_valid valid step) (apply_working live free.1 step) active free.2 ran with
          final | ⟨cut, member, done⟩
        · exact Or.inl final
        · exact Or.inr ⟨cut, states_step step member, done⟩
      · exact Or.inr ⟨next, states_step step (states_start events next), completed_processed processed⟩

theorem boundary_excludes_flight {owner : Owner} {work : Work} {state : State}
    (valid : Valid state) (boundary : EmptyBoundary owner state.project) :
    ¬ InFlight owner work state := by
  obtain ⟨head, rest, top, same, _, emptyCurrent, emptyQueue⟩ :=
    (projected_empty_boundary_iff valid).mp boundary
  have named := congrArg Owner.index same
  change head.core.index = owner.index at named
  have indexed := valid.indexed
  rw [top] at indexed
  intro flight
  rcases flight with queued | ⟨held, member, above, current⟩
  · simp only [emptyQueue, List.not_mem_nil] at queued
  · rw [top] at member
    rcases List.mem_cons.mp member with equal | below
    · subst held
      rw [emptyCurrent] at current
      cases current
    · have position := indexed_member indexed.2 below
      have topIndex := indexed.1
      omega

theorem first_boundary_processed {owner : Owner} {work : Work} {events : List Event}
    {state last : State} (valid : Valid state) (live : Working owner state)
    (flight : InFlight owner work state) (before : NoEarlier owner events state)
    (computed : execute events state = .ok last) (boundary : EmptyBoundary owner last.project) :
    ∃ cut ∈ states events state, Processed work cut := by
  rcases conserve valid live flight before computed with active | processed
  · exact False.elim (boundary_excludes_flight (execute_valid valid computed) boundary active)
  · exact processed

/-- Every item present in ANY actual queue snapshot of this prefix has an
actual processed-frame witness in that SAME event trace. This includes
structural enqueues and nested frames without relying on issued/return logs. -/
theorem every_queued_processed {owner : Owner} {events : List Event} {state last : State}
    (valid : Valid state) (live : Working owner state) (before : NoEarlier owner events state)
    (computed : execute events state = .ok last) (boundary : EmptyBoundary owner last.project) :
    ∀ queuedState ∈ states events state, ∀ work ∈ queuedState.queue,
      ∃ doneState ∈ states events state, Processed work doneState := by
  induction events generalizing state with
  | nil =>
    intro queuedState member work queued
    have same : queuedState = state := by simpa only [states, List.mem_singleton] using member
    subst queuedState
    exact first_boundary_processed valid live (Or.inl queued) before computed boundary
  | cons event events ih =>
    cases step : apply event state with
    | error failure => simp only [execute, step, reduceCtorEq] at computed
    | ok next =>
      have free : ¬ EmptyBoundary owner state.project ∧ NoEarlier owner events next := by
        simpa only [NoEarlier, step] using before
      have ran : execute events next = .ok last := by simpa only [execute, step] using computed
      intro queuedState member work queued
      simp only [states, step, List.mem_cons] at member
      rcases member with same | later
      · subst queuedState
        exact first_boundary_processed valid live (Or.inl queued) before computed boundary
      · obtain ⟨doneState, observed, done⟩ :=
          ih (apply_valid valid step) (apply_working live free.1 step) free.2 ran
            queuedState later work queued
        exact ⟨doneState, states_step step observed, done⟩

/-- Select the first boundary on the supplied event list, retaining exact
list-indexed firstness rather than merely an unlabeled reachability proof. -/
theorem select_first {owner : Owner} {events : List Event} {start last : State}
    (computed : execute events start = .ok last) (ends : EmptyBoundary owner last.project) :
    ∃ earlier later cut,
      events = earlier ++ later ∧ execute earlier start = .ok cut ∧
      NoEarlier owner earlier start ∧ EmptyBoundary owner cut.project := by
  induction events generalizing start with
  | nil =>
    change Except.ok start = Except.ok last at computed
    cases computed
    exact ⟨[], [], last, rfl, rfl, True.intro, ends⟩
  | cons event events ih =>
    by_cases now : EmptyBoundary owner start.project
    · exact ⟨[], event :: events, start, rfl, rfl, True.intro, now⟩
    · cases step : apply event start with
      | error failure => simp only [execute, step, reduceCtorEq] at computed
      | ok next =>
        have tail : execute events next = .ok last := by
          simpa only [execute, step] using computed
        obtain ⟨earlier, later, cut, decomposition, ran, trace, boundary⟩ := ih tail
        refine ⟨event :: earlier, later, cut, ?_, ?_, ?_, boundary⟩
        · simp only [List.cons_append, decomposition]
        · simp only [execute, step, ran]
        · simpa only [NoEarlier, step] using And.intro now trace

theorem no_earlier_before {owner : Owner} {events : List Event} {state last : State}
    (before : NoEarlier owner events state) (computed : execute events state = .ok last) :
    OriginalFirstDrainBoundary.BeforeFirst owner state last := by
  induction events generalizing state with
  | nil => cases computed; exact .nil last
  | cons event events ih =>
    cases step : apply event state with
    | error failure => simp only [execute, step, reduceCtorEq] at computed
    | ok next =>
      have free : ¬ EmptyBoundary owner state.project ∧ NoEarlier owner events next := by
        simpa only [NoEarlier, step] using before
      have tail : execute events next = .ok last := by simpa only [execute, step] using computed
      exact OriginalFirstDrainBoundary.before_trans
        (.snoc event (.nil state) free.1 step) (ih free.2 tail)

/-- A new completion on an actual event edge in this exact suffix. An
earlier stored processed record cannot establish this proposition. -/
def CompletionIn (work : Work) : List Event → State → Prop
  | [], _ => False
  | event :: rest, state => match apply event state with
    | .error _ => False
    | .ok next => Completed work state next ∨ CompletionIn work rest next

theorem conserve_completion {owner : Owner} {work : Work} {events : List Event}
    {state last : State} (valid : Valid state) (live : Working owner state)
    (flight : InFlight owner work state) (before : NoEarlier owner events state)
    (computed : execute events state = .ok last) :
    InFlight owner work last ∨ CompletionIn work events state := by
  induction events generalizing state with
  | nil => cases computed; exact Or.inl flight
  | cons event events ih =>
    cases step : apply event state with
    | error failure => simp only [execute, step, reduceCtorEq] at computed
    | ok next =>
      have free : ¬ EmptyBoundary owner state.project ∧ NoEarlier owner events next := by
        simpa only [NoEarlier, step] using before
      have tail : execute events next = .ok last := by simpa only [execute, step] using computed
      simp only [CompletionIn, step]
      rcases apply_flight valid live flight step with active | completed
      · rcases ih (apply_valid valid step) (apply_working live free.1 step) active free.2 tail with
          final | later
        · exact Or.inl final
        · exact Or.inr (Or.inr later)
      · exact Or.inr (Or.inl completed)

theorem first_boundary_completion {owner : Owner} {work : Work} {events : List Event}
    {state last : State} (valid : Valid state) (live : Working owner state)
    (flight : InFlight owner work state) (before : NoEarlier owner events state)
    (computed : execute events state = .ok last) (boundary : EmptyBoundary owner last.project) :
    CompletionIn work events state := by
  rcases conserve_completion valid live flight before computed with active | completed
  · exact False.elim (boundary_excludes_flight (execute_valid valid computed) boundary active)
  · exact completed

theorem prefix_live {owner : Owner} {leading suffix : List Event} {state middle : State}
    (live : Working owner state) (before : NoEarlier owner (leading ++ suffix) state)
    (computed : execute leading state = .ok middle) :
    Working owner middle ∧ NoEarlier owner suffix middle := by
  induction leading generalizing state with
  | nil => cases computed; exact ⟨live, before⟩
  | cons event leading ih =>
    cases step : apply event state with
    | error failure => simp only [execute, step, reduceCtorEq] at computed
    | ok next =>
      have free : ¬ EmptyBoundary owner state.project ∧ NoEarlier owner (leading ++ suffix) next := by
        simpa only [List.cons_append, NoEarlier, step] using before
      have tail : execute leading next = .ok middle := by simpa only [execute, step] using computed
      exact ih (apply_working live free.1 step) free.2 tail

theorem execute_suffix {leading suffix : List Event} {state middle last : State}
    (computed : execute leading state = .ok middle)
    (whole : execute (leading ++ suffix) state = .ok last) :
    execute suffix middle = .ok last := by
  induction leading generalizing state with
  | nil => cases computed; exact whole
  | cons event leading ih =>
    cases step : apply event state with
    | error failure => simp only [execute, step, reduceCtorEq] at computed
    | ok next =>
      apply ih
      · simpa only [execute, step] using computed
      · simpa only [List.cons_append, execute, step] using whole

/-- Each exact queue-observation cut has a NEW completion in its remaining
suffix, not merely a matching old entry somewhere in the whole trace. -/
def FutureQueueCoverage (events : List Event) (state : State) : Prop :=
  ∀ leading suffix middle, events = leading ++ suffix →
    execute leading state = .ok middle →
    ∀ work ∈ middle.queue, CompletionIn work suffix middle

theorem every_queue_has_new_completion {owner : Owner} {events : List Event} {state last : State}
    (valid : Valid state) (live : Working owner state) (before : NoEarlier owner events state)
    (computed : execute events state = .ok last) (boundary : EmptyBoundary owner last.project) :
    FutureQueueCoverage events state := by
  intro leading suffix middle decomposition ran work queued
  subst events
  have remaining := prefix_live live before ran
  exact first_boundary_completion (execute_valid valid ran) remaining.1 (Or.inl queued)
    remaining.2 (execute_suffix ran computed) boundary

/-- At the actual initialized Dispatch cut, a candidate finite boundary
suffix supplies a NONEMPTY first prefix. Every queue snapshot in that exact
prefix has a processed witness in the same trace; the endpoint's native
poll-entry/settlement fields are derived as well. No coarse run, queue law,
processing witness, frame invariant, or termination premise is supplied. -/
theorem initialized_dispatch_queue_coverage
    {history events : List Event} {tau last : State} {activeFrame : Frame} {activeTail : List Frame}
    (initialized : execute history initial = .ok tau)
    (activeTop : tau.frames = activeFrame :: activeTail)
    (dispatch : activeFrame.stage = .dispatch)
    (candidate : execute events tau = .ok last)
    (ends : EmptyBoundary activeFrame.owner last.project) :
    ∃ earlier later cut frame rest,
      events = earlier ++ later ∧ earlier ≠ [] ∧ execute earlier tau = .ok cut ∧
      NoEarlier activeFrame.owner earlier tau ∧ EmptyBoundary activeFrame.owner cut.project ∧
      cut.frames = frame :: rest ∧ frame.owner = activeFrame.owner ∧
      frame.core.index = rest.length ∧ frame.stage = .transport ∧
      frame.core.current = none ∧ cut.queue = [] ∧ frame.poll = .entry ∧
      apply (.settle activeFrame.owner) cut =
        .ok {cut with frames := {frame with poll := .settling} :: rest} ∧
      (∀ queuedState ∈ states earlier tau, ∀ work ∈ queuedState.queue,
        ∃ doneState ∈ states earlier tau, Processed work doneState) ∧
      FutureQueueCoverage earlier tau := by
  have valid := initialized_valid initialized
  have present : activeFrame ∈ tau.frames := by rw [activeTop]; exact List.mem_cons_self
  have live : Working activeFrame.owner tau := ⟨activeFrame, present, rfl, by
    simp only [dispatch, Stage.phase]⟩
  have active := OriginalDrainFrontier.initialized_dispatch_current initialized present dispatch
  have notBoundary := OriginalDrainFrontier.initialized_active_not_boundary initialized activeTop active
  have entryOnly := OriginalDrainFrontier.initialized_active_entry_only initialized activeTop active
  obtain ⟨earlier, later, cut, decomposition, ran, before, boundary⟩ := select_first candidate ends
  have nonempty : earlier ≠ [] := by
    intro empty
    subst earlier
    change Except.ok tau = Except.ok cut at ran
    cases ran
    exact notBoundary boundary
  have cutValid := execute_valid valid ran
  have entry := OriginalFirstDrainBoundary.before_entry (no_earlier_before before ran) entryOnly
  obtain ⟨frame, rest, top, same, stage, current, empty⟩ :=
    (projected_empty_boundary_iff cutValid).mp boundary
  have poll := entry frame (by rw [top]; exact List.mem_cons_self) same
  have indexed := cutValid.indexed
  rw [top] at indexed
  refine ⟨earlier, later, cut, frame, rest, decomposition, nonempty, ran, before, boundary,
    top, same, indexed.1, stage, current, empty, poll, ?_,
    every_queued_processed valid live before ran boundary,
    every_queue_has_new_completion valid live before ran boundary⟩
  have settlement := boundary_enters_settlement cutValid top
    (by simpa only [same] using boundary) poll
  simpa only [same] using settlement

end YulangClosure.OriginalStageWorkConservation
