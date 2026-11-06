import Yulang.SignatureRequests

/-!
# Finite execution prefixes of the unlabelled loop expansion

The control operations implement the contracts in `spec/03c-control.md`
§3c.1–2. `last`, `next`, and `redo` have empty response types: their old
body continuation cannot be resumed. `redo` installs the original body for
the same item, retaining the current external state and remaining cursor.

Traversal and external interpretation are explicit parameters. The cursor
may describe an infinite traversal, and restarting a finite body may diverge.
Fuel bounds observations; it is not a language termination assumption. The
independent `Step`, `Pending`, and `Prefix` judgments characterize the
executable observer for every machine, state, body tree, and fuel.

This is an unlabelled library control model, not a source elaborator or an
implementation of arbitrary `Fold`. In particular it does not identify
label values with operation names or choose generative handler identities.
-/

namespace Yulang.LoopEffects

open Directed SignatureRequests

inductive Operation (External : Type) where
  | last | next | redo
  | external : External → Operation External
  deriving DecidableEq, Repr

def signature (external : Signature External) : Signature (Operation External) where
  Payload
    | .last | .next | .redo => Unit
    | .external operation => external.Payload operation
  Response
    | .last | .next | .redo => Empty
    | .external operation => external.Response operation

def handled : List (Operation External) := [.last, .next, .redo]

/-- External interpretation receives the complete signed occurrence. It may
answer with a new state and observation, or suspend without changing state. -/
structure Reply (external : Signature External) (operation : External) (State Event : Type) where
  value : external.Response operation
  state : State
  event : Event

structure Machine (n : Nat) (external : Signature External)
    (Item Cursor State Event Value : Type) where
  nextItem : Cursor → Option (Item × Cursor)
  body : Item → Tree n (signature external) Value
  interpret : (occurrence : Occurrence n External) → external.Payload occurrence.key →
    State → Option (Reply external occurrence.key State Event)

inductive Control (n : Nat) (external : Signature External) (Item Cursor Value : Type) where
  | pull : Cursor → Control n external Item Cursor Value
  | body : Item → Cursor → Tree n (signature external) Value → Control n external Item Cursor Value
  | done : Control n external Item Cursor Value

structure Configuration (n : Nat) (external : Signature External) (Item Cursor State Value : Type) where
  state : State
  control : Control n external Item Cursor Value

inductive Observation (Config Event : Type) where
  | progress : Option Event → Config → Observation Config Event
  | blocked : Observation Config Event
  | finished : Observation Config Event

variable {External Item Cursor State Event Value : Type} {n : Nat}
variable {external : Signature External}

def Machine.step [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value)
    (configuration : Configuration n external Item Cursor State Value) :
    Observation (Configuration n external Item Cursor State Value) Event :=
  match configuration with
  | ⟨_, .done⟩ => .finished
  | ⟨state, .pull cursor⟩ =>
      match machine.nextItem cursor with
      | none => .progress none ⟨state, .done⟩
      | some (item, rest) => .progress none ⟨state, .body item rest (machine.body item)⟩
  | ⟨state, .body _ rest (.pure _)⟩ => .progress none ⟨state, .pull rest⟩
  | ⟨state, .body item rest (.request occurrence payload resume)⟩ =>
      match occurrence with
      | ⟨.last, weights⟩ =>
          if Capturable (handled (External := External)) ⟨.last, weights⟩ then .progress none ⟨state, .done⟩ else .blocked
      | ⟨.next, weights⟩ =>
          if Capturable (handled (External := External)) ⟨.next, weights⟩ then .progress none ⟨state, .pull rest⟩ else .blocked
      | ⟨.redo, weights⟩ =>
          if Capturable (handled (External := External)) ⟨.redo, weights⟩ then
            .progress none ⟨state, .body item rest (machine.body item)⟩
          else .blocked
      | ⟨.external operation, weights⟩ =>
          match machine.interpret ⟨operation, weights⟩ payload state with
          | none => .blocked
          | some answer =>
              .progress (some answer.event) ⟨answer.state, .body item rest (resume answer.value)⟩

/-- Independent transition rules. An abortive operation never calls the
stored body resumption. Only an external response can resume its request. -/
inductive Step (machine : Machine n external Item Cursor State Event Value) :
    Configuration n external Item Cursor State Value → Option Event →
      Configuration n external Item Cursor State Value → Prop where
  | exhausted (missing : machine.nextItem cursor = none) :
      Step machine ⟨state, .pull cursor⟩ none ⟨state, .done⟩
  | enter (selected : machine.nextItem cursor = some (item, rest)) :
      Step machine ⟨state, .pull cursor⟩ none ⟨state, .body item rest (machine.body item)⟩
  | returned (value : Value) :
      Step machine ⟨state, .body item rest (.pure value)⟩ none ⟨state, .pull rest⟩
  | last (weights : Fin n → Int) (payload : Unit)
      (resume : Empty → Tree n (signature external) Value)
      (visible : Capturable (handled (External := External)) ⟨.last, weights⟩) :
      Step machine ⟨state, .body item rest (.request ⟨.last, weights⟩ payload resume)⟩
        none ⟨state, .done⟩
  | next (weights : Fin n → Int) (payload : Unit)
      (resume : Empty → Tree n (signature external) Value)
      (visible : Capturable (handled (External := External)) ⟨.next, weights⟩) :
      Step machine ⟨state, .body item rest (.request ⟨.next, weights⟩ payload resume)⟩
        none ⟨state, .pull rest⟩
  | redo (weights : Fin n → Int) (payload : Unit)
      (resume : Empty → Tree n (signature external) Value)
      (visible : Capturable (handled (External := External)) ⟨.redo, weights⟩) :
      Step machine ⟨state, .body item rest (.request ⟨.redo, weights⟩ payload resume)⟩
        none ⟨state, .body item rest (machine.body item)⟩
  | external (operation : External) (weights : Fin n → Int) (payload : external.Payload operation)
      (resume : external.Response operation → Tree n (signature external) Value)
      (answer : Reply external operation State Event)
      (responded : machine.interpret ⟨operation, weights⟩ payload state = some answer) :
      Step machine ⟨state, .body item rest (.request ⟨.external operation, weights⟩ payload resume)⟩
        (some answer.event) ⟨answer.state, .body item rest (resume answer.value)⟩

/-- Suspension retains the entire original configuration, including signed
weights, payload, continuation, cursor, and state. Protected loop operations
are not answered with a fictitious inhabitant of `Empty`. -/
inductive Pending (machine : Machine n external Item Cursor State Event Value) :
    Configuration n external Item Cursor State Value → Prop where
  | last (weights : Fin n → Int) (payload : Unit)
      (resume : Empty → Tree n (signature external) Value)
      (hidden : ¬ Capturable (handled (External := External)) ⟨.last, weights⟩) :
      Pending machine ⟨state, .body item rest (.request ⟨.last, weights⟩ payload resume)⟩
  | next (weights : Fin n → Int) (payload : Unit)
      (resume : Empty → Tree n (signature external) Value)
      (hidden : ¬ Capturable (handled (External := External)) ⟨.next, weights⟩) :
      Pending machine ⟨state, .body item rest (.request ⟨.next, weights⟩ payload resume)⟩
  | redo (weights : Fin n → Int) (payload : Unit)
      (resume : Empty → Tree n (signature external) Value)
      (hidden : ¬ Capturable (handled (External := External)) ⟨.redo, weights⟩) :
      Pending machine ⟨state, .body item rest (.request ⟨.redo, weights⟩ payload resume)⟩
  | external (operation : External) (weights : Fin n → Int) (payload : external.Payload operation)
      (resume : external.Response operation → Tree n (signature external) Value)
      (unanswered : machine.interpret ⟨operation, weights⟩ payload state = none) :
      Pending machine ⟨state, .body item rest (.request ⟨.external operation, weights⟩ payload resume)⟩

theorem Step.executable [DecidableEq External]
    {machine : Machine n external Item Cursor State Event Value}
    (transition : Step machine configuration event following) :
    machine.step configuration = .progress event following := by
  cases transition <;> simp_all [Machine.step]

theorem Pending.executable [DecidableEq External]
    {machine : Machine n external Item Cursor State Event Value}
    (pending : Pending machine configuration) : machine.step configuration = .blocked := by
  cases pending <;> simp_all [Machine.step]

theorem step_progress_iff [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value)
    (configuration next : Configuration n external Item Cursor State Value) (event : Option Event) :
    machine.step configuration = .progress event next ↔ Step machine configuration event next := by
  constructor
  · intro observed
    cases configuration with
    | mk state control =>
      cases control with
      | done => cases observed
      | pull cursor =>
          cases selected : machine.nextItem cursor with
          | none =>
              simp only [Machine.step, selected] at observed
              cases observed
              exact .exhausted selected
          | some pair =>
              rcases pair with ⟨item, rest⟩
              simp only [Machine.step, selected] at observed
              cases observed
              exact .enter selected
      | body item rest action =>
          cases action with
          | pure value =>
              cases observed
              exact .returned value
          | request occurrence payload resume =>
              rcases occurrence with ⟨operation, weights⟩
              cases operation with
              | last =>
                  simp only [Machine.step] at observed
                  split at observed
                  · cases observed; exact .last weights payload resume (by assumption)
                  · cases observed
              | next =>
                  simp only [Machine.step] at observed
                  split at observed
                  · cases observed; exact .next weights payload resume (by assumption)
                  · cases observed
              | redo =>
                  simp only [Machine.step] at observed
                  split at observed
                  · cases observed; exact .redo weights payload resume (by assumption)
                  · cases observed
              | external operation =>
                  cases responded : machine.interpret ⟨operation, weights⟩ payload state with
                  | none => simp [Machine.step, responded] at observed
                  | some answer =>
                      simp only [Machine.step, responded] at observed
                      cases observed
                      exact .external operation weights payload resume answer responded
  · exact Step.executable

theorem step_blocked_iff [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value)
    (configuration : Configuration n external Item Cursor State Value) :
    machine.step configuration = .blocked ↔ Pending machine configuration := by
  constructor
  · intro observed
    cases configuration with
    | mk state control =>
      cases control with
      | done => cases observed
      | pull cursor =>
          cases selected : machine.nextItem cursor <;> simp [Machine.step, selected] at observed
      | body item rest action =>
          cases action with
          | pure value => cases observed
          | request occurrence payload resume =>
              rcases occurrence with ⟨operation, weights⟩
              cases operation with
              | last =>
                  simp only [Machine.step] at observed
                  split at observed
                  · cases observed
                  · exact .last weights payload resume (by assumption)
              | next =>
                  simp only [Machine.step] at observed
                  split at observed
                  · cases observed
                  · exact .next weights payload resume (by assumption)
              | redo =>
                  simp only [Machine.step] at observed
                  split at observed
                  · cases observed
                  · exact .redo weights payload resume (by assumption)
              | external operation =>
                  cases responded : machine.interpret ⟨operation, weights⟩ payload state with
                  | none => exact .external operation weights payload resume responded
                  | some answer => simp [Machine.step, responded] at observed
  · exact Pending.executable

theorem step_finished_iff [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value)
    (configuration : Configuration n external Item Cursor State Value) :
    machine.step configuration = .finished ↔ configuration.control = .done := by
  cases configuration with
  | mk state control =>
    cases control with
    | done => exact ⟨fun _ => rfl, fun _ => rfl⟩
    | pull cursor =>
        cases selected : machine.nextItem cursor <;> simp [Machine.step, selected]
    | body item rest action =>
        cases action with
        | pure value => simp [Machine.step]
        | request occurrence payload resume =>
            rcases occurrence with ⟨operation, weights⟩
            cases operation with
            | last | next | redo => simp only [Machine.step]; split <;> simp
            | external operation =>
                cases responded : machine.interpret ⟨operation, weights⟩ payload state <;>
                  simp [Machine.step, responded]

theorem Step.deterministic [DecidableEq External]
    {machine : Machine n external Item Cursor State Event Value}
    (first : Step machine configuration event firstNext)
    (last : Step machine configuration otherEvent lastNext) :
    event = otherEvent ∧ firstNext = lastNext :=
  Observation.progress.inj (first.executable.symm.trans last.executable)

inductive Outcome (n : Nat) (external : Signature External) (Item Cursor State Value : Type) where
  | exhausted : Configuration n external Item Cursor State Value → Outcome n external Item Cursor State Value
  | blocked : Configuration n external Item Cursor State Value → Outcome n external Item Cursor State Value
  | returned : State → Unit → Outcome n external Item Cursor State Value

structure Report (n : Nat) (external : Signature External) (Item Cursor State Event Value : Type) where
  trace : List Event
  outcome : Outcome n external Item Cursor State Value

def Report.prepend (events : List Event)
    (report : Report n external Item Cursor State Event Value) :
    Report n external Item Cursor State Event Value := ⟨events ++ report.trace, report.outcome⟩

def Machine.run [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) : Nat →
    Configuration n external Item Cursor State Value → Report n external Item Cursor State Event Value
  | 0, configuration => ⟨[], .exhausted configuration⟩
  | fuel + 1, configuration =>
      match machine.step configuration with
      | .finished => ⟨[], .returned configuration.state ()⟩
      | .blocked => ⟨[], .blocked configuration⟩
      | .progress event next => (machine.run fuel next).prepend event.toList

/-- A finite derivation records exactly the external observations made
before completion, suspension, or exhaustion of the observation budget. -/
inductive Prefix (machine : Machine n external Item Cursor State Event Value) : Nat →
    Configuration n external Item Cursor State Value → List Event →
    Outcome n external Item Cursor State Value → Prop where
  | cutoff (configuration : Configuration n external Item Cursor State Value) :
      Prefix machine 0 configuration [] (.exhausted configuration)
  | returned (done : configuration.control = .done) :
      Prefix machine (fuel + 1) configuration [] (.returned configuration.state ())
  | blocked (pending : Pending machine configuration) :
      Prefix machine (fuel + 1) configuration [] (.blocked configuration)
  | progress (step : Step machine configuration event next)
      (rest : Prefix machine fuel next trace outcome) :
      Prefix machine (fuel + 1) configuration (event.toList ++ trace) outcome

theorem Prefix.executable [DecidableEq External]
    {machine : Machine n external Item Cursor State Event Value}
    (execution : Prefix machine fuel configuration trace outcome) :
    machine.run fuel configuration = ⟨trace, outcome⟩ := by
  induction execution with
  | cutoff => rfl
  | returned done => simp [Machine.run, (step_finished_iff _ _).mpr done]
  | blocked pending => simp [Machine.run, pending.executable]
  | progress step _ ih => simp [Machine.run, step.executable, ih, Report.prepend]

theorem run_prefix [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (fuel : Nat)
    (configuration : Configuration n external Item Cursor State Value) :
    Prefix machine fuel configuration (machine.run fuel configuration).trace
      (machine.run fuel configuration).outcome := by
  induction fuel generalizing configuration with
  | zero => exact .cutoff configuration
  | succ fuel ih =>
      cases observed : machine.step configuration with
      | finished =>
          simpa only [Machine.run, observed] using
            (Prefix.returned (fuel := fuel) ((step_finished_iff _ _).mp observed))
      | blocked =>
          simpa only [Machine.run, observed] using
            (Prefix.blocked (fuel := fuel) ((step_blocked_iff _ _).mp observed))
      | progress event next =>
          simpa only [Machine.run, observed, Report.prepend] using
            Prefix.progress ((step_progress_iff _ _ _ _).mp observed) (ih next)

/-- Exact for every budget and initial configuration. No success, bound,
termination, or pre-existing operational derivation is required. -/
theorem prefix_iff_run [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (fuel : Nat)
    (configuration : Configuration n external Item Cursor State Value)
    (trace : List Event) (outcome : Outcome n external Item Cursor State Value) :
    Prefix machine fuel configuration trace outcome ↔ machine.run fuel configuration = ⟨trace, outcome⟩ := by
  constructor
  · exact Prefix.executable
  · intro actual
    simpa only [actual] using run_prefix machine fuel configuration

/-- Continue only a budget-exhausted execution. A completed or suspended
execution is retained; resuming a suspension requires an outer response. -/
def Machine.extend [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (more : Nat)
    (report : Report n external Item Cursor State Event Value) :
    Report n external Item Cursor State Event Value :=
  match report.outcome with
  | .exhausted next => (machine.run more next).prepend report.trace
  | _ => report

theorem extend_prepend [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (more : Nat)
    (events : List Event) (report : Report n external Item Cursor State Event Value) :
    machine.extend more (report.prepend events) = (machine.extend more report).prepend events := by
  cases report with
  | mk trace outcome => cases outcome <;> simp [Machine.extend, Report.prepend, List.append_assoc]

/-- Prefix composition retains the current state and appends observations.
Increasing fuel cannot replay a prefix from its old state or erase its log. -/
theorem run_add [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (fuel more : Nat)
    (configuration : Configuration n external Item Cursor State Value) :
    machine.run (fuel + more) configuration = machine.extend more (machine.run fuel configuration) := by
  induction fuel generalizing configuration with
  | zero => simp [Machine.run, Machine.extend, Report.prepend]
  | succ fuel ih =>
      cases observed : machine.step configuration with
      | finished | blocked => simp [Nat.succ_add, Machine.run, observed, Machine.extend]
      | progress event next =>
          simp only [Nat.succ_add, Machine.run, observed, ih, extend_prepend]

theorem run_add_exhausted [DecidableEq External]
    (machine : Machine n external Item Cursor State Event Value) (fuel more : Nat)
    (configuration next : Configuration n external Item Cursor State Value) (trace : List Event)
    (observed : machine.run fuel configuration = ⟨trace, .exhausted next⟩) :
    machine.run (fuel + more) configuration = (machine.run more next).prepend trace := by
  rw [run_add, observed]
  rfl

end Yulang.LoopEffects
