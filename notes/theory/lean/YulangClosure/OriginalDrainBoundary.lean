import YulangClosure.NativeDrainOwnership

/-!
The actual shared drain cannot discard its working frame before its own
empty working boundary. Both birth and frame index identify the owner;
reuse of a stack position is not identity of a drain.

Every constructor of the existing NativeDrainOwnership.Step is retained.
This does not supply the semantic body of dispatch or a full native inference
machine, and says nothing about excluded abort/rollback transitions.
-/
namespace YulangClosure.OriginalDrainBoundary

open NativeDrainOwnership

structure Owner where
  birth : Nat
  index : Nat
  deriving DecidableEq, Repr

def identity (frame : Frame) : Owner := ⟨frame.birth, frame.index⟩

def WorkingFrames (owner : Owner) (frames : List Frame) : Prop :=
  ∃ frame ∈ frames, identity frame = owner ∧ frame.phase = .working

def Working (owner : Owner) (state : State) : Prop :=
  WorkingFrames owner state.frames

/-- This is the existing enterDiagnostics guard at the specified actual
frame. An empty queue during a nested or current dispatch is insufficient. -/
def EmptyBoundary (owner : Owner) (state : State) : Prop :=
  ∃ frame rest, state.frames = frame :: rest ∧ identity frame = owner ∧
    frame.phase = .working ∧ frame.current = none ∧ state.queue = []

private theorem keep_tail (owner : Owner) (head : Frame) {tail : List Frame}
    (live : WorkingFrames owner tail) : WorkingFrames owner (head :: tail) := by
  obtain ⟨frame, member, same, phase⟩ := live
  exact ⟨frame, List.mem_cons_of_mem head member, same, phase⟩

private theorem replace_head (owner : Owner) {first last : Frame} {rest : List Frame}
    (same : identity last = identity first) (phase : last.phase = first.phase)
    (live : WorkingFrames owner (first :: rest)) : WorkingFrames owner (last :: rest) := by
  obtain ⟨frame, member, identified, active⟩ := live
  rcases List.mem_cons.mp member with rfl | later
  · exact ⟨last, List.mem_cons_self, same.trans identified, phase.trans active⟩
  · exact ⟨frame, List.mem_cons_of_mem last later, identified, active⟩

private theorem drop_inactive (owner : Owner) {head : Frame} {tail : List Frame}
    (excluded : ¬ (identity head = owner ∧ head.phase = .working))
    (live : WorkingFrames owner (head :: tail)) : WorkingFrames owner tail := by
  obtain ⟨frame, member, same, phase⟩ := live
  rcases List.mem_cons.mp member with rfl | later
  · exact False.elim (excluded ⟨same, phase⟩)
  · exact ⟨frame, later, same, phase⟩

/-- A normal control step preserves this precise working owner unless the
step starts at its own first-empty candidate boundary. No fairness, completed
child, queue invariant, frame-depth or final-boundary hypothesis is used. -/
theorem step_keeps_working {owner : Owner} {before after : State}
    (step : Step before after) (live : Working owner before)
    (notEmpty : ¬ EmptyBoundary owner before) : Working owner after := by
  cases step with
  | begin task relation empty =>
    exact keep_tail owner _ live
  | startReplay id task relation op found empty idle active same child =>
    exact keep_tail owner _ live
  | takePlain frame rest work remaining top head phase current plain =>
    have old : WorkingFrames owner (frame :: rest) := by simpa only [Working, top] using live
    exact replace_head owner (first := frame) rfl rfl old
  | takeReplay frame rest work remaining ticket op top head phase current ack found lower upper wait prepared =>
    have old : WorkingFrames owner (frame :: rest) := by simpa only [Working, top] using live
    exact replace_head owner (first := frame) rfl rfl old
  | transport frame rest work relation top phase current =>
    have old : WorkingFrames owner (frame :: rest) := by simpa only [Working, top] using live
    exact replace_head owner (first := frame) rfl rfl old
  | dispatch frame rest work transitions top phase current =>
    have old : WorkingFrames owner (frame :: rest) := by simpa only [Working, top] using live
    exact replace_head owner (first := frame) rfl rfl old
  | prepare frame rest ticket op top position found lower upper wait =>
    have old : WorkingFrames owner (frame :: rest) := by simpa only [Working, top] using live
    exact replace_head owner (first := frame) rfl rfl old
  | enterDiagnostics frame rest top phase current empty =>
    have old : WorkingFrames owner (frame :: rest) := by simpa only [Working, top] using live
    have different : ¬ identity frame = owner := by
      intro same
      exact notEmpty ⟨frame, rest, top, same, phase, current, empty⟩
    exact keep_tail owner _ (drop_inactive owner (fun both => different both.1) old)
  | diagnostics frame rest top phase =>
    have old : WorkingFrames owner (frame :: rest) := by simpa only [Working, top] using live
    have inactive : ¬ (identity frame = owner ∧ frame.phase = .working) := by
      intro both
      rw [phase] at both
      cases both.2
    exact keep_tail owner _ (drop_inactive owner inactive old)
  | acknowledge frame rest ticket remaining op top phase diagnosed pending prepared found ordered wait =>
    have old : WorkingFrames owner (frame :: rest) := by simpa only [Working, top] using live
    have inactive : ¬ (identity frame = owner ∧ frame.phase = .working) := by
      intro both
      rw [phase] at both
      cases both.2
    exact keep_tail owner _ (drop_inactive owner inactive old)
  | emptyReady frame rest top phase pending =>
    have old : WorkingFrames owner (frame :: rest) := by simpa only [Working, top] using live
    have inactive : ¬ (identity frame = owner ∧ frame.phase = .working) := by
      intro both
      rw [phase] at both
      cases both.2
    exact keep_tail owner _ (drop_inactive owner inactive old)
  | popPlain frame rest top phase index pending current diagnosed destination =>
    have old : WorkingFrames owner (frame :: rest) := by simpa only [Working, top] using live
    apply drop_inactive owner _ old
    intro both
    rw [phase] at both
    cases both.2
  | popReplay frame rest ticket op top phase index pending current diagnosed destination found wait consumed queued =>
    have old : WorkingFrames owner (frame :: rest) := by simpa only [Working, top] using live
    apply drop_inactive owner _ old
    intro both
    rw [phase] at both
    cases both.2
  | commit =>
    obtain ⟨frame, member, same, phase⟩ := live
    exact ⟨{frame with prepared := frame.completed}, List.mem_map.mpr ⟨frame, member, rfl⟩, same, phase⟩
  | _ => exact live

/-- The finite prefix strictly before the specified drain's first empty
boundary. This records actual control steps and the original first-boundary
property; it contains no successful-child or future-completion requirement. -/
inductive BeforeBoundary (owner : Owner) : State → State → Prop
  | nil (state) : BeforeBoundary owner state state
  | snoc {start middle last} : BeforeBoundary owner start middle →
      Step middle last → ¬ EmptyBoundary owner middle → BeforeBoundary owner start last

theorem before_boundary_run {owner : Owner} {start last : State}
    (past : BeforeBoundary owner start last) : Run start last := by
  induction past with
  | nil => exact Run.nil _
  | snoc previous step notEmpty ih => exact Run.snoc ih step

theorem before_boundary_working {owner : Owner} {start last : State}
    (past : BeforeBoundary owner start last) (live : Working owner start) : Working owner last := by
  induction past with
  | nil => exact live
  | snoc previous step notEmpty ih => exact step_keeps_working step ih notEmpty

theorem working_depth {owner : Owner} {state : State}
    (live : Working owner state)
    (indices : ∀ frame ∈ state.frames, frame.index < state.frames.length) :
    owner.index < state.frames.length := by
  obtain ⟨frame, member, same, phase⟩ := live
  have position := congrArg Owner.index same
  change frame.index = owner.index at position
  rw [← position]
  exact indices frame member

/-- Losing the working owner in any actual finite control run has a concrete
earlier empty boundary in that very run. This is a necessary condition, not a
termination or completion assertion. -/
theorem losing_working_has_boundary {owner : Owner} {start last : State}
    (run : Run start last) (live : Working owner start) (lost : ¬ Working owner last) :
    ∃ boundary, Run start boundary ∧ EmptyBoundary owner boundary ∧ Run boundary last := by
  classical
  induction run with
  | nil => exact False.elim (lost live)
  | @snoc middle last past step ih =>
    by_cases still : Working owner middle
    · have empty : EmptyBoundary owner middle :=
        Classical.byContradiction (fun absent => lost (step_keeps_working step still absent))
      exact ⟨middle, past, empty, Run.snoc (Run.nil middle) step⟩
    · obtain ⟨boundary, before, empty, after⟩ := ih still
      exact ⟨boundary, before, empty, Run.snoc after step⟩

/-- The statement specializes to frame removal without identifying a later
reuse of its stack slot with this original birth. -/
theorem removal_has_boundary {owner : Owner} {start last : State}
    (run : Run start last) (live : Working owner start)
    (removed : ∀ frame ∈ last.frames, identity frame ≠ owner) :
    ∃ boundary, Run start boundary ∧ EmptyBoundary owner boundary ∧ Run boundary last := by
  apply losing_working_has_boundary run live
  rintro ⟨frame, member, same, phase⟩
  exact removed frame member same

end YulangClosure.OriginalDrainBoundary
