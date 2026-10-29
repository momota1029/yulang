import YulangClosure.FormalPermissionTermCallControl

/-! R16: the production live-variable/function arena event protocol. Snapshots,
reserve results and sampler outcomes are supplied observations, not certified
Rust executions. The initial buffer is explicit and is never assumed empty.
Allocation failure and identity-claim failure precede page publication. -/
namespace YulangClosure.FormalPermissionArenaEvents
open FormalPermissionTermCallControl FormalPermissionHelperFrames
noncomputable section

inductive Lane where
  | interner | internedJournal | pageDescriptors | pagePositions
  | claimedPagesJournal | pageBacking
  deriving DecidableEq

inductive Mode where
  | liveVariable | positiveFunction | negativeFunction
  deriving DecidableEq

inductive Publication where
  | allocationFailed | identityClaimFailed | published
  deriving DecidableEq

structure ReserveOutcome where
  changed : Bool
  succeeded : Bool
  observation : EventOutcome

structure Event where
  lane : Lane
  observation : EventOutcome

structure Attempt where
  lane : Lane
  changed : Bool
  succeeded : Bool
  observation : EventOutcome

def emitted (a : Attempt) : List Event :=
  if a.changed then [⟨a.lane, a.observation⟩] else []

/-- Emit before examining the reserve result. The failed stage's own growth
is retained; subsequent stages are not executed. -/
def run : List Attempt → List Event
  | [] => []
  | a :: rest => emitted a ++ if a.succeeded then run rest else []

def reserve (lane : Lane) (active : Bool) (o : ReserveOutcome) : Attempt :=
  ⟨lane, active && o.changed, !active || o.succeeded, o.observation⟩

structure Input where
  mode : Mode
  childrenValid : Bool
  cacheHit : Bool
  journalPresent : Bool
  pageNeeded : Bool
  interner : ReserveOutcome
  internedJournal : ReserveOutcome
  pageDescriptors : ReserveOutcome
  pagePositions : ReserveOutcome
  claimedPagesJournal : ReserveOutcome
  publication : Publication
  backingObservation : EventOutcome

def valid (i : Input) : Bool :=
  match i.mode with
  | .liveVariable => true
  | .positiveFunction | .negativeFunction => i.childrenValid

def starts (i : Input) : Bool := valid i && !i.cacheHit

def published (i : Input) : Bool := decide (i.publication = .published)

def publicationAttempt (i : Input) : Attempt :=
  ⟨.pageBacking, i.pageNeeded && published i,
    !i.pageNeeded || published i, i.backingObservation⟩

/-- Disabled stages are identities. Thus the six slots have a fixed order,
without inventing reserve attempts for absent journals or an unneeded page. -/
def protocol (i : Input) : List Attempt :=
  [reserve .interner true i.interner,
   reserve .internedJournal i.journalPresent i.internedJournal,
   reserve .pageDescriptors i.pageNeeded i.pageDescriptors,
   reserve .pagePositions i.pageNeeded i.pagePositions,
   reserve .claimedPagesJournal (i.pageNeeded && i.journalPresent) i.claimedPagesJournal,
   publicationAttempt i]

def appended (i : Input) : List Event :=
  if starts i then run (protocol i) else []

def canonical : List Lane :=
  [.interner, .internedJournal, .pageDescriptors, .pagePositions,
   .claimedPagesJournal, .pageBacking]

theorem run_order (as : List Attempt) :
    List.Sublist ((run as).map Event.lane) (as.map Attempt.lane) := by
  induction as with
  | nil => exact List.Sublist.refl _
  | cons a rest ih =>
      cases hc : a.changed <;> cases hs : a.succeeded
      · simpa [run, emitted, hc, hs] using (List.nil_sublist (a.lane :: rest.map Attempt.lane))
      · simpa [run, emitted, hc, hs] using ih.cons a.lane
      · simpa [run, emitted, hc, hs] using (List.nil_sublist (rest.map Attempt.lane)).cons_cons a.lane
      · simpa [run, emitted, hc, hs] using ih.cons_cons a.lane

/-- Exact ordered omission: no lane is inserted, duplicated or reordered. -/
theorem appended_order (i : Input) :
    List.Sublist ((appended i).map Event.lane) canonical := by
  cases h : starts i with
  | false => simp [appended, h, canonical]
  | true =>
      simpa [appended, h, protocol, reserve, publicationAttempt, canonical] using run_order (protocol i)

theorem appended_bound (i : Input) : (appended i).length ≤ 6 := by
  have h := (appended_order i).length_le
  simpa [canonical] using h

theorem disabled_reserve (lane : Lane) (o : ReserveOutcome) :
    emitted (reserve lane false o) = [] ∧
    (reserve lane false o).succeeded = true := by
  simp [reserve, emitted]

theorem failed_reserve_growth_retained (lane : Lane) (o : ReserveOutcome)
    (changed : o.changed = true) (failed : o.succeeded = false)
    (rest : List Attempt) :
    run (reserve lane true o :: rest) = [⟨lane, o.observation⟩] := by
  simp [run, reserve, emitted, changed, failed]

theorem unchanged_reserve_emits_nothing (lane : Lane) (o : ReserveOutcome)
    (unchanged : o.changed = false) : emitted (reserve lane true o) = [] := by
  simp [reserve, emitted, unchanged]

theorem run_append_success (before after : List Attempt)
    (success : ∀ a ∈ before, a.succeeded = true) :
    run (before ++ after) = run before ++ run after := by
  revert success
  induction before with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro success
      have head := success a (by simp)
      have tail : ∀ b ∈ rest, b.succeeded = true := fun b hb => success b (by simp [hb])
      simp only [List.cons_append, run, head, if_true, ih tail, List.append_assoc]

/-- Any failure retains all earlier events, including its own changed-capacity
event. This applies to every reachable reserve stage and publication failure. -/
theorem failure_preserves_prefix (before after : List Attempt) (a : Attempt)
    (success : ∀ b ∈ before, b.succeeded = true) (failed : a.succeeded = false) :
    run (before ++ a :: after) = run before ++ emitted a := by
  rw [run_append_success before (a :: after) success]
  simp [run, failed]

theorem cache_hit_no_events (i : Input) (hit : i.cacheHit = true) :
    appended i = [] := by
  simp [appended, starts, hit]

theorem invalid_function_no_events (i : Input)
    (function : i.mode = .positiveFunction ∨ i.mode = .negativeFunction)
    (invalid : i.childrenValid = false) : appended i = [] := by
  rcases function with h | h <;> simp [appended, starts, valid, h, invalid]

theorem publication_stage (i : Input) :
    emitted (publicationAttempt i) =
      (if i.pageNeeded && published i then [⟨.pageBacking, i.backingObservation⟩] else []) := by
  rfl

/-- Allocation and page identity failure cannot generate PageBacking. This
statement concerns the newly appended suffix; a preexisting oldEvents may contain it. -/
theorem publication_failure_no_backing_stage (i : Input)
    (failed : i.publication ≠ .published) :
    emitted (publicationAttempt i) = [] := by
  simp [publication_stage, published, failed]

private theorem run_member (as : List Attempt) (e : Event) (member : e ∈ run as) :
    ∃ a ∈ as, e ∈ emitted a := by
  revert member
  induction as with
  | nil => intro member; simp [run] at member
  | cons a rest ih =>
      intro member
      simp only [run, List.mem_append] at member
      rcases member with head | tail
      · exact ⟨a, by simp, head⟩
      · have tailMember : e ∈ run rest := by
          cases hs : a.succeeded <;> simp_all
        obtain ⟨b, hb, he⟩ := ih tailMember
        exact ⟨b, by simp [hb], he⟩

theorem backing_requires_publication (i : Input) (e : Event)
    (member : e ∈ appended i) (backing : e.lane = .pageBacking) :
    i.pageNeeded = true ∧ i.publication = .published := by
  have executed : e ∈ run (protocol i) := by
    cases hs : starts i <;> simp_all [appended]
  obtain ⟨a, ha, he⟩ := run_member (protocol i) e executed
  simp only [protocol, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with ha | ha | ha | ha | ha | ha
  all_goals subst a
  all_goals simp only [emitted] at he
  all_goals split at he
  all_goals simp_all [reserve, publicationAttempt, published]

def events (oldEvents : List EventOutcome) (i : Input) : List EventOutcome :=
  oldEvents ++ (appended i).map Event.observation

/-- This is the source buffer assertion's precondition, not a consequence of
the six-new-events bound. Every attempted append must have a free slot. -/
def Fits (oldEvents : List EventOutcome) (i : Input) : Prop :=
  oldEvents.length + (appended i).length ≤ 6

theorem combined_prefix_bound (oldEvents : List EventOutcome) (i : Input)
    (fits : Fits oldEvents i) : (events oldEvents i).length ≤ 6 := by
  simpa [events, Fits] using fits

theorem each_append_has_slot (oldEvents : List EventOutcome) (i : Input)
    (fits : Fits oldEvents i) (n : Nat) (pending : n < (appended i).length) :
    oldEvents.length + n < 6 := by
  unfold Fits at fits
  omega

theorem preexisting_prefix_preserved (oldEvents : List EventOutcome) (i : Input) :
    events oldEvents i = oldEvents ++ (appended i).map Event.observation := rfl

/-- R15 now consumes the derived suffix together with the old buffer. Arena
contents/returned term remain distinct opaque observations. Actual constructor
result correspondence and each sampler outcome remain external premises. -/
theorem derived_control_refines (oldEvents : List EventOutcome) (i : Input)
    (constructor : ConstructorOutcome) (accounting : Bool) (s : HelperState) :
    runOps (controlOps constructor (events oldEvents i) accounting s) s =
      controlState constructor (events oldEvents i) accounting s :=
  control_ops_refine constructor (events oldEvents i) accounting s

theorem derived_constructor_error_preserved (oldEvents : List EventOutcome) (i : Input)
    (constructor : ConstructorOutcome) (accounting : Bool) (errorMap : Nat → Nat)
    (error : Nat) (failed : constructor.result = .error error)
    (samplesOk : AllSamplesOk (events oldEvents i)) :
    controlResult errorMap constructor (events oldEvents i) accounting = .error (errorMap error) :=
  constructor_error_preserved errorMap constructor (events oldEvents i) accounting error failed samplesOk

end
end YulangClosure.FormalPermissionArenaEvents
