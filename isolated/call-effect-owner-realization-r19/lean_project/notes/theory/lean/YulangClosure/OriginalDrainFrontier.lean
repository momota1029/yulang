import YulangClosure.OriginalFirstDrainBoundary

/-!
The first empty boundary AFTER an initialized active drain cut.

Fresh begin is already Transport/None/empty, before seed enqueue. The frozen
first-boundary theorem from initial therefore cannot select the NQ post-tau
frontier by itself. Here the polling invariant is derived from the existing
computed apply/execute functions, then used at the supplied active cut.

No caller supplies Valid, EntryOnly, a polling invariant, a coarse C.Run, or
termination. The final theorem consumes a candidate finite successful suffix
ending at the same owner's EmptyBoundary and finds its first later boundary.
Native event/readback extraction and the full NQ contradiction remain separate.
-/
namespace YulangClosure.OriginalDrainFrontier

open OriginalDrainStages
open OriginalDrainBoundary (Owner EmptyBoundary)

namespace First
export OriginalFirstDrainBoundary
  (EntryOnly BeforeFirst update_entry before_entry before_valid finite_first_boundary)
end First

/-- A nonentry polling counter belongs only to the idle Transport frame.
This is a derived field invariant, not another executable-stage guard. -/
def FramePoll (frame : Frame) : Prop :=
  frame.poll = .entry ∨ (frame.stage = .transport ∧ frame.core.current = none)

def Polls (frames : List Frame) : Prop := ∀ frame ∈ frames, FramePoll frame

theorem fresh_poll (birth index : Nat) (destination : Option NativeDrainOwnership.Ticket) :
    FramePoll (fresh birth index destination) := Or.inl rfl

theorem initial_polls : Polls initial.frames := by
  intro frame member
  cases member

theorem nonentry_idle {frame : Frame} (polls : FramePoll frame)
    (nonentry : frame.poll ≠ .entry) : frame.stage = .transport ∧ frame.core.current = none :=
  polls.resolve_left nonentry

/-- If an update starts nonentry, the derived invariant selects the exact
Transport/None branch, which resets entry for both pop outcomes. All other
successful updates use the frozen full-stage entry-preservation theorem. -/
theorem update_returns_entry {readback : Readback} {front : Option NativeDrainOwnership.Work}
    {dirty : Bool} {frame : Frame} {result : Update} (polls : FramePoll frame)
    (success : update readback front dirty frame = .ok result) : result.frame.poll = .entry := by
  rcases polls with entry | ⟨stage, current⟩
  · exact First.update_entry entry success
  · simp only [update, stage, current] at success
    cases front <;> cases success <;> rfl

theorem tail_polls {head : Frame} {rest : List Frame} (before : Polls (head :: rest)) :
    Polls rest := by
  intro frame member
  exact before frame (List.mem_cons_of_mem head member)

theorem replace_polls {head changed : Frame} {rest : List Frame}
    (before : Polls (head :: rest)) (after : FramePoll changed) : Polls (changed :: rest) := by
  intro frame member
  rcases List.mem_cons.mp member with rfl | later
  · exact after
  · exact before frame (List.mem_cons_of_mem head later)

theorem advanced_polls {state : State} {head : Frame} {rest : List Frame}
    {readback : Readback} {result : Update} (before : Polls state.frames)
    (top : state.frames = head :: rest)
    (updated : update readback state.queue.head? state.dirty head = .ok result) :
    Polls (advanced state rest result).frames := by
  rw [top] at before
  cases returned : result.returned with
  | false =>
      simp only [advanced, returned, Bool.false_eq_true]
      exact replace_polls before (Or.inl (update_returns_entry (before head List.mem_cons_self) updated))
  | true =>
      simp only [advanced, returned, ite_eq_left]
      exact tail_polls before

theorem apply_polls {state after : State} {event : Event} (before : Polls state.frames)
    (success : apply event state = .ok after) : Polls after.frames := by
  cases event with
  | begin destination =>
      simp only [apply] at success
      split at success
      · cases success
        intro frame member
        rcases List.mem_cons.mp member with rfl | old
        · exact fresh_poll _ _ _
        · exact before frame old
      · cases success
  | reserveBirth => cases success; exact before
  | enqueue work front => cases success; exact before
  | bookkeeping data => cases success; exact before
  | advance owner readback =>
      simp only [apply, advance, withTop] at success
      split at success
      · cases success
      · rename_i frame rest top
        split at success
        · split at success
          · cases success
          · split at success
            · cases success
            · split at success
              · cases success
              · rename_i result updated
                cases success
                exact advanced_polls before top updated
        · cases success
  | settle owner =>
      simp only [apply, withTop] at success
      split at success
      · cases success
      · rename_i frame rest top
        split at success
        · split at success
          · rename_i guard
            cases success
            rw [top] at before
            exact replace_polls before (Or.inr ⟨guard.1, guard.2.1⟩)
          · cases success
        · cases success
  | settled owner dirty =>
      simp only [apply, withTop] at success
      split at success
      · cases success
      · rename_i frame rest top
        split at success
        · split at success
          · rename_i settling
            cases success
            rw [top] at before
            have idle := nonentry_idle (before frame List.mem_cons_self) (by
              rw [settling]
              intro impossible
              cases impossible)
            exact replace_polls before (Or.inr idle)
          · cases success
        · cases success
  | prepare owner prepared =>
      simp only [apply, withTop] at success
      split at success
      · cases success
      · rename_i frame rest top
        split at success
        · cases success
          rw [top] at before
          rcases before frame List.mem_cons_self with entry | idle
          · exact replace_polls before (Or.inl entry)
          · exact replace_polls before (Or.inr idle)
        · cases success

theorem execute_polls {events : List Event} {start last : State} (before : Polls start.frames)
    (success : execute events start = .ok last) : Polls last.frames := by
  induction events generalizing start with
  | nil => cases success; exact before
  | cons event events ih =>
      simp only [execute] at success
      cases step : apply event start with
      | error failure => simp [step] at success
      | ok next => exact ih (apply_polls before step) (by simpa [step] using success)

theorem initialized_polls {history : List Event} {state : State}
    (computed : execute history initial = .ok state) : Polls state.frames :=
  execute_polls initial_polls computed

/-- The active frame's entry counter is derived, not supplied at tau. -/
theorem initialized_active_entry {history : List Event} {state : State} {frame : Frame}
    (computed : execute history initial = .ok state) (present : frame ∈ state.frames)
    (active : frame.core.current ≠ none) : frame.poll = .entry := by
  rcases initialized_polls computed frame present with entry | idle
  · exact entry
  · exact False.elim (active idle.2)

/-- Birth/index ownership cannot select a different suspended frame at the
same cut. The index invariant is itself obtained from initialized execution. -/
theorem initialized_active_entry_only {history : List Event} {state : State}
    {frame : Frame} {rest : List Frame} (computed : execute history initial = .ok state)
    (top : state.frames = frame :: rest) (active : frame.core.current ≠ none) :
    First.EntryOnly frame.owner state.frames := by
  have valid := initialized_valid computed
  have entry := initialized_active_entry computed
    (by rw [top]; exact List.mem_cons_self) active
  intro selected member same
  have topOwnerSame : topOwner state = some selected.owner := by
    simp only [topOwner, top, List.head?_cons, Option.map_some, same]
  obtain ⟨tail, selectedTop⟩ := same_top_is_saved_frame valid member topOwnerSame
  have equal : selected = frame := (List.cons.inj (selectedTop.symm.trans top)).1
  simpa only [equal] using entry

theorem initialized_active_not_boundary {history : List Event} {state : State}
    {frame : Frame} {rest : List Frame} (computed : execute history initial = .ok state)
    (top : state.frames = frame :: rest) (active : frame.core.current ≠ none) :
    ¬ EmptyBoundary frame.owner state.project := by
  intro boundary
  obtain ⟨actual, tail, actualTop, _, _, current, _⟩ :=
    (projected_empty_boundary_iff (initialized_valid computed)).mp boundary
  have equal : actual = frame := (List.cons.inj (actualTop.symm.trans top)).1
  exact active (equal ▸ current)

/-- First boundary strictly after the supplied active cut. The candidate
finite suffix supplies existence; no normal completion or finite suffix is
created by the theorem. Both initialization validity and owner EntryOnly
are derived before applying the frozen first-boundary result at tau. -/
theorem initialized_active_first_settlement
    {history events : List Event} {tau last : State} {activeFrame : Frame} {activeTail : List Frame}
    (initialized : execute history initial = .ok tau)
    (activeTop : tau.frames = activeFrame :: activeTail)
    (activeCurrent : activeFrame.core.current ≠ none)
    (candidate : execute events tau = .ok last)
    (ends : EmptyBoundary activeFrame.owner last.project) :
    ∃ earlier later cut frame rest,
      events = earlier ++ later ∧ earlier ≠ [] ∧ execute earlier tau = .ok cut ∧
      First.BeforeFirst activeFrame.owner tau cut ∧ EmptyBoundary activeFrame.owner cut.project ∧
      cut.frames = frame :: rest ∧ frame.owner = activeFrame.owner ∧
      frame.core.index = rest.length ∧ frame.stage = .transport ∧
      frame.core.current = none ∧ cut.queue = [] ∧ frame.poll = .entry ∧
      apply (.settle activeFrame.owner) cut =
        .ok {cut with frames := {frame with poll := .settling} :: rest} := by
  have notBoundary := initialized_active_not_boundary initialized activeTop activeCurrent
  have entryOnly := initialized_active_entry_only initialized activeTop activeCurrent
  obtain ⟨earlier, later, cut, decomposition, ran, trace, boundary⟩ :=
    First.finite_first_boundary candidate ends
  have nonempty : earlier ≠ [] := by
    intro empty
    subst earlier
    change Except.ok tau = Except.ok cut at ran
    cases ran
    exact notBoundary boundary
  have valid := First.before_valid trace (initialized_valid initialized)
  have entry := First.before_entry trace entryOnly
  obtain ⟨frame, rest, top, same, stage, current, empty⟩ :=
    (projected_empty_boundary_iff valid).mp boundary
  have poll := entry frame (by rw [top]; exact List.mem_cons_self) same
  have indexed := valid.indexed
  rw [top] at indexed
  refine ⟨earlier, later, cut, frame, rest, decomposition, nonempty, ran, trace, boundary,
    top, same, indexed.1, stage, current, empty, poll, ?_⟩
  have settlement := boundary_enters_settlement valid top
    (by simpa only [same] using boundary) poll
  simpa only [same] using settlement

/-- NQ's stated tau is immediately before dispatch_live_item. An actual
Dispatch-stage readback already supplies current via the initialized shape
invariant; no independent active-current invariant is required. -/
theorem initialized_dispatch_current {history : List Event} {state : State} {frame : Frame}
    (initialized : execute history initial = .ok state) (present : frame ∈ state.frames)
    (dispatch : frame.stage = .dispatch) : frame.core.current ≠ none := by
  have shape := (initialized_valid initialized).shapes frame present
  obtain ⟨work, current⟩ := (by simpa only [Frame.Shape, dispatch] using shape :
    ∃ work, frame.core.current = some work)
  rw [current]
  intro impossible
  cases impossible

theorem initialized_dispatch_first_settlement
    {history events : List Event} {tau last : State} {activeFrame : Frame} {activeTail : List Frame}
    (initialized : execute history initial = .ok tau)
    (activeTop : tau.frames = activeFrame :: activeTail)
    (dispatch : activeFrame.stage = .dispatch)
    (candidate : execute events tau = .ok last)
    (ends : EmptyBoundary activeFrame.owner last.project) :
    ∃ earlier later cut frame rest,
      events = earlier ++ later ∧ earlier ≠ [] ∧ execute earlier tau = .ok cut ∧
      First.BeforeFirst activeFrame.owner tau cut ∧ EmptyBoundary activeFrame.owner cut.project ∧
      cut.frames = frame :: rest ∧ frame.owner = activeFrame.owner ∧
      frame.core.index = rest.length ∧ frame.stage = .transport ∧
      frame.core.current = none ∧ cut.queue = [] ∧ frame.poll = .entry ∧
      apply (.settle activeFrame.owner) cut =
        .ok {cut with frames := {frame with poll := .settling} :: rest} :=
  initialized_active_first_settlement initialized activeTop
    (initialized_dispatch_current initialized (by rw [activeTop]; exact List.mem_cons_self) dispatch)
    candidate ends

end YulangClosure.OriginalDrainFrontier
