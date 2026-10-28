import YulangClosure.OriginalDrainStages

/-!
An owner's first empty Transport boundary is the entry to settlement, not a
cut after that same frame has already entered or returned from settlement.
The proof follows the actual computed fourteen-stage updates and frame
lifetime, without assuming a program-counter invariant for the final frame.
-/
namespace YulangClosure.OriginalFirstDrainBoundary

open OriginalDrainStages
open OriginalDrainBoundary (Owner EmptyBoundary)

theorem structural_entry {family : Family} {readback : Readback} {frame : Frame}
    {result : Update} (entry : frame.poll = .entry)
    (success : structural family readback frame = .ok result) : result.frame.poll = .entry := by
  unfold structural at success
  split at success
  · cases success
  · split at success
    · cases success
      cases family <;> exact entry
    · split at success
      · cases success
        cases family <;> exact entry
      · split at success
        · split at success
          · cases success
          · cases success
            cases family <;> exact entry
        · cases success

theorem update_entry {readback : Readback} {front : Option NativeDrainOwnership.Work}
    {dirty : Bool} {frame : Frame} {result : Update} (entry : frame.poll = .entry)
    (success : update readback front dirty frame = .ok result) : result.frame.poll = .entry := by
  cases stage : frame.stage <;> simp only [update, stage] at success
  case transport =>
    split at success
    · split at success <;> cases success <;> rfl
    · cases success; exact entry
  case context => split at success <;> cases success; exact entry
  case dispatch =>
    split at success
    · cases success
    · cases success
    · cases choice : readback.dispatch with
      | finished =>
        simp only [choice] at success
        cases success
        unfold finishDispatch
        split <;> exact entry
      | children family tasks =>
        simp only [choice] at success
        cases success
        cases family <;> exact entry
  case functionAdmission | functionEnqueue | tupleAdmission | tupleEnqueue |
      recordAdmission | recordEnqueue | variantAdmission | variantEnqueue =>
    exact structural_entry entry success
  case diagnostics => cases success; exact entry
  case acknowledgements => split at success <;> cases success <;> exact entry
  case returnReady => cases success; exact entry

def EntryOnly (owner : Owner) (frames : List Frame) : Prop :=
  ∀ frame ∈ frames, frame.owner = owner → frame.poll = .entry

theorem initial_entry (owner : Owner) : EntryOnly owner initial.frames := by
  intro frame member
  cases member

theorem tail_entry {owner : Owner} {head : Frame} {rest : List Frame}
    (before : EntryOnly owner (head :: rest)) : EntryOnly owner rest := by
  intro frame member same
  exact before frame (List.mem_cons_of_mem head member) same

theorem replace_entry {owner : Owner} {head changed : Frame} {rest : List Frame}
    (before : EntryOnly owner (head :: rest)) (same : changed.owner = head.owner)
    (poll : head.poll = .entry → changed.poll = .entry) :
    EntryOnly owner (changed :: rest) := by
  intro frame member named
  rcases List.mem_cons.mp member with rfl | later
  · exact poll (before head List.mem_cons_self (same.symm.trans named))
  · exact before frame (List.mem_cons_of_mem head later) named

theorem advanced_entry {owner : Owner} {state : State} {frame : Frame} {rest : List Frame}
    {readback : Readback} {result : Update}
    (before : EntryOnly owner state.frames) (top : state.frames = frame :: rest)
    (updated : update readback state.queue.head? state.dirty frame = .ok result) :
    EntryOnly owner (advanced state rest result).frames := by
  rw [top] at before
  cases returned : result.returned with
  | false =>
    simp only [advanced, returned, Bool.false_eq_true]
    exact replace_entry before (update_owner updated) (fun entry => update_entry entry updated)
  | true =>
    simp only [advanced, returned, ite_eq_left]
    exact tail_entry before

/-- Before this owner's first empty cut, no event can move its frame into
or out of settlement. Other owners and their nested frames remain allowed. -/
theorem apply_entry {owner : Owner} {state after : State} {event : Event}
    (before : EntryOnly owner state.frames)
    (notBoundary : ¬ EmptyBoundary owner state.project)
    (success : apply event state = .ok after) : EntryOnly owner after.frames := by
  cases event with
  | begin destination =>
    simp only [apply] at success
    split at success
    · cases success
      intro frame member named
      rcases List.mem_cons.mp member with rfl | old
      · rfl
      · exact before frame old named
    · cases success
  | reserveBirth => cases success; exact before
  | enqueue work front => cases success; exact before
  | bookkeeping data => cases success; exact before
  | advance target readback =>
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
              exact advanced_entry before top updated
      · cases success
  | settle target =>
    have boundary := settlement_starts_at_boundary success
    simp only [apply, withTop] at success
    split at success
    · cases success
    · rename_i frame rest top
      split at success
      · rename_i same
        split at success
        · cases success
          intro selected member named
          rcases List.mem_cons.mp member with rfl | old
          · have equal : target = owner := same.1.symm.trans named
            exact False.elim (notBoundary (equal ▸ boundary))
          · exact before selected (by rw [top]; exact List.mem_cons_of_mem frame old) named
        · cases success
      · cases success
  | settled target dirty =>
    simp only [apply, withTop] at success
    split at success
    · cases success
    · rename_i frame rest top
      split at success
      · split at success
        · rename_i settling
          cases success
          intro selected member named
          rcases List.mem_cons.mp member with rfl | old
          · have entry := before frame (by rw [top]; exact List.mem_cons_self) named
            rw [entry] at settling
            cases settling
          · exact before selected (by rw [top]; exact List.mem_cons_of_mem frame old) named
        · cases success
      · cases success
  | prepare target prepared =>
    simp only [apply, withTop] at success
    split at success
    · cases success
    · rename_i frame rest top
      split at success
      · cases success
        intro selected member named
        rcases List.mem_cons.mp member with rfl | old
        · exact before frame (by rw [top]; exact List.mem_cons_self) named
        · exact before selected (by rw [top]; exact List.mem_cons_of_mem frame old) named
      · cases success

/-- A finite actual event prefix strictly before this owner's first empty
cut. Each transition is the existing executable `apply`, not an assumed
coarse-control run or an added semantic preservation law. -/
inductive BeforeFirst (owner : Owner) : State → State → Prop where
  | nil (state : State) : BeforeFirst owner state state
  | snoc {first middle last : State} (event : Event)
      (earlier : BeforeFirst owner first middle)
      (before : ¬ EmptyBoundary owner middle.project)
      (step : apply event middle = .ok last) : BeforeFirst owner first last

theorem before_entry {owner : Owner} {first last : State}
    (run : BeforeFirst owner first last) (entry : EntryOnly owner first.frames) :
    EntryOnly owner last.frames := by
  induction run with
  | nil => exact entry
  | snoc event earlier before step ih => exact apply_entry ih before step

theorem before_valid {owner : Owner} {first last : State}
    (run : BeforeFirst owner first last) (valid : Valid first) : Valid last := by
  induction run with
  | nil => exact valid
  | snoc event earlier before step ih => exact apply_valid ih step

theorem before_trans {owner : Owner} {first middle last : State}
    (left : BeforeFirst owner first middle) (right : BeforeFirst owner middle last) :
    BeforeFirst owner first last := by
  induction right with
  | nil => exact left
  | snoc event earlier before step ih => exact .snoc event ih before step

/-- Any actual finite execution ending at an empty cut contains a first one.
The returned prefix is part of the original event list; no terminating
execution, empty cut, or event is added to that list by this construction. -/
theorem finite_first_boundary {owner : Owner} {events : List Event} {start last : State}
    (computed : execute events start = .ok last)
    (ends : EmptyBoundary owner last.project) :
    ∃ earlier later cut,
      events = earlier ++ later ∧ execute earlier start = .ok cut ∧
      BeforeFirst owner start cut ∧ EmptyBoundary owner cut.project := by
  induction events generalizing start with
  | nil =>
    change Except.ok start = Except.ok last at computed
    cases computed
    exact ⟨[], [], last, rfl, rfl, .nil last, ends⟩
  | cons event events ih =>
    by_cases now : EmptyBoundary owner start.project
    · exact ⟨[], event :: events, start, rfl, rfl, .nil start, now⟩
    · cases step : apply event start with
      | error failure => simp [execute, step] at computed
      | ok next =>
        have tail : execute events next = .ok last := by simpa [execute, step] using computed
        obtain ⟨earlier, later, cut, decomposition, ran, trace, boundary⟩ := ih tail
        refine ⟨event :: earlier, later, cut, ?_, ?_, ?_, boundary⟩
        · simp only [List.cons_append, decomposition]
        · simp [execute, step, ran]
        · exact before_trans (.snoc event (.nil start) now step) trace

/-- The program counter at the FIRST actual empty boundary is derived from
initialization. No final-frame entry/saved-poll premise is supplied. -/
theorem first_empty_enters_settlement {owner : Owner} {last : State}
    (run : BeforeFirst owner initial last) (boundary : EmptyBoundary owner last.project) :
    ∃ frame rest,
      last.frames = frame :: rest ∧ frame.owner = owner ∧
      frame.core.index = rest.length ∧ frame.stage = .transport ∧
      frame.core.current = none ∧ last.queue = [] ∧ frame.poll = .entry ∧
      apply (.settle owner) last = .ok {last with frames := {frame with poll := .settling} :: rest} := by
  have valid := before_valid run initial_valid
  have entry := before_entry run (initial_entry owner)
  obtain ⟨frame, rest, top, same, stage, current, empty⟩ :=
    (projected_empty_boundary_iff valid).mp boundary
  have poll := entry frame (by rw [top]; exact List.mem_cons_self) same
  have ordered := valid.indexed
  rw [top] at ordered
  refine ⟨frame, rest, top, same, ordered.1, stage, current, empty, poll, ?_⟩
  have settle := boundary_enters_settlement valid top (by simpa only [same] using boundary) poll
  simpa only [same] using settle

/-- The first cut is supplied by the given initialized execution. In
particular the settlement-entry program counter is not a caller premise. -/
theorem initialized_first_settlement {owner : Owner} {events : List Event} {last : State}
    (computed : execute events initial = .ok last)
    (ends : EmptyBoundary owner last.project) :
    ∃ earlier later cut frame rest,
      events = earlier ++ later ∧ execute earlier initial = .ok cut ∧
      BeforeFirst owner initial cut ∧ EmptyBoundary owner cut.project ∧
      cut.frames = frame :: rest ∧ frame.owner = owner ∧
      frame.core.index = rest.length ∧ frame.stage = .transport ∧
      frame.core.current = none ∧ cut.queue = [] ∧ frame.poll = .entry ∧
      apply (.settle owner) cut = .ok {cut with frames := {frame with poll := .settling} :: rest} := by
  obtain ⟨earlier, later, cut, decomposition, ran, trace, boundary⟩ :=
    finite_first_boundary computed ends
  obtain ⟨frame, rest, fields⟩ := first_empty_enters_settlement trace boundary
  exact ⟨earlier, later, cut, frame, rest, decomposition, ran, trace, boundary, fields⟩

end YulangClosure.OriginalFirstDrainBoundary
