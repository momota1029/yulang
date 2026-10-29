import YulangClosure.FormalPermissionCandidateCallJournal

/-! R20: token-preserving interpretation of the two journal owners.
Frozen admission sources: term.rs:705–822; lib.rs:3503–3558,9267–9545,
9646–9678. This module does not turn a trace alphabet into native evidence.
Concrete source/execution correspondence requires the frozen native receipt.
The original all-source parent scope and its shared witness are unchanged. -/
namespace YulangClosure.FormalPermissionNativePrefix

/-- Native transaction identities are retained independently of presence. -/
structure State where
  session : Option Nat
  arena : Option Nat
  deriving DecidableEq

def initial : State := ⟨none, none⟩

def project (s : State) : FormalPermissionCandidateCallJournal.Journals :=
  ⟨s.session.map (fun _ => ()), s.arena.map (fun _ => ())⟩

/-- No neutral event may hide a write to either active-journal option.
Payload writes that preserve both options require source classification. -/
inductive Action where
  | beginArena (token : Nat)
  | publishSession (token : Nat)
  | takeSession (token : Nat)
  | takeArena (token : Nat)
  | neutral
  deriving DecidableEq

def transition (s : State) : Action → State
  | .beginArena t => { s with arena := some t }
  | .publishSession t => { s with session := some t }
  | .takeSession _ => { s with session := none }
  | .takeArena _ => { s with arena := none }
  | .neutral => s

/-- Entry/finish discipline checks token agreement and the Store-before-session
order; it permits the arena-only interval before session publication. -/
def enabled (s : State) : Action → Bool
  | .beginArena _ => decide (s.session = none ∧ s.arena = none)
  | .publishSession t => decide (s.session = none ∧ s.arena = some t)
  | .takeSession t => decide (s.session = some t ∧ s.arena = some t)
  | .takeArena t => decide (s.session = none ∧ s.arena = some t)
  | .neutral => true

def microstep : Action → FormalPermissionCandidateCallJournal.Microstep
  | .beginArena _ => .beginArena
  | .publishSession _ => .publishSession
  | .takeSession _ => .takeSession
  | .takeArena _ => .takeArena
  | .neutral => .unchanged

structure Observation where
  sessionPresent : Bool
  arenaPresent : Bool
  deriving DecidableEq

def observe (s : State) : Observation :=
  ⟨s.session.isSome, s.arena.isSome⟩

/-- Before/after observations must come from the actual same owners and event.
The strings in the external receipt are not silently classified here. -/
structure Event where
  action : Action
  before : Observation
  after : Observation

def run (s : State) : List Event → State
  | [] => s
  | e :: es => run (transition s e.action) es

def validates (s : State) : List Event → Bool
  | [] => true
  | e :: es =>
      enabled s e.action && decide (e.before = observe s) &&
      decide (e.after = observe (transition s e.action)) &&
      validates (transition s e.action) es

theorem transition_projection (s : State) (a : Action) :
    project (transition s a) = FormalPermissionCandidateCallJournal.step (project s) (microstep a) := by
  cases a <;> rfl

theorem run_projection (s : State) (events : List Event) :
    project (run s events) =
      FormalPermissionCandidateCallJournal.run (project s) (events.map (fun e => microstep e.action)) := by
  induction events generalizing s with
  | nil => rfl
  | cons e es ih =>
      simpa only [run, List.map_cons, FormalPermissionCandidateCallJournal.run, List.foldl_cons,
        transition_projection] using ih (transition s e.action)

/-- This supplies the initialization equation, rather than assuming a caller
frame is absent. Its interpretation as native initialization is a source edge. -/
theorem initial_projection : project initial = FormalPermissionCandidateCallJournal.initial := by rfl

/-- Both the token and both presence observations are required at each event.
This is a general checker equation, not authentication of any native trace. -/
theorem validates_cons (s : State) (e : Event) (es : List Event) :
    validates s (e :: es) = true ↔
      enabled s e.action = true ∧ e.before = observe s ∧
      e.after = observe (transition s e.action) ∧
      validates (transition s e.action) es = true := by
  simp only [validates, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨fun ⟨⟨⟨a, b⟩, c⟩, d⟩ => ⟨a, b, c, d⟩,
    fun ⟨a, b, c, d⟩ => ⟨⟨⟨a, b⟩, c⟩, d⟩⟩

end YulangClosure.FormalPermissionNativePrefix
