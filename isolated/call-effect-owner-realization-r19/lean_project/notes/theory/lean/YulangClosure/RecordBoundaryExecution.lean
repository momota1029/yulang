import YulangClosure.NativeRecordPlan

/-!
The record-boundary manuscript's ordinary bind composition, including every
finite request prefix and typed resumption. The payload machines and their
independently stated contracts are inputs; record execution never consults a
typing proof. The same immutable visible input and ordered pending fields are
retained across requests. There is no termination assumption, bounded request
count, backing-object lookup, or implicit adaptation at a type variable.

This closes the compositional record-plan part of the manuscript theorem.
Authentic source boundary elaboration, the child contracts' full contextual
meaning, and native execution correspondence remain independent obligations.
-/
namespace YulangClosure.RecordBoundaryExecution

open RecordBoundary

/-- One observable layer of an arbitrary payload machine. Its state can retain
an unbounded loop; the type does not require a finite computation tree. -/
inductive Observation (State Value Request Response Failure : Type) where
  | next (state : State)
  | returned (value : Value)
  | requested (request : Request) (resume : Response → State)
  | failed (failure : Failure)

def Accepted (good : Value → Prop) (allowed : Request → Prop)
    (response : Request → Response → Prop) (continuing : State → Prop) :
    Observation State Value Request Response Failure → Prop
  | .next state => continuing state
  | .returned value => good value
  | .requested request resume =>
      allowed request ∧ ∀ answer, response request answer → continuing (resume answer)
  | .failed _ => True

/-- All finite observations, including the zero-step prefix. Failure is an
explicit propagated exit; it is not a successful normal result. -/
def Safe (step : State → Observation State Value Request Response Failure)
    (good : Value → Prop) (allowed : Request → Prop)
    (response : Request → Response → Prop) : Nat → State → Prop
  | 0, _ => True
  | depth + 1, state => Accepted good allowed response
      (Safe step good allowed response depth) (step state)

def SafeAll (step : State → Observation State Value Request Response Failure)
    (good : Value → Prop) (allowed : Request → Prop)
    (response : Request → Response → Prop) (state : State) : Prop :=
  ∀ depth, Safe step good allowed response depth state

theorem safeAll_unfold
    (safe : SafeAll step good allowed response state) :
    Accepted good allowed response (SafeAll step good allowed response) (step state) := by
  cases h : step state with
  | next next => exact fun n => by simpa [Safe, Accepted, h] using safe (n + 1)
  | returned value => simpa [Safe, Accepted, h] using safe 1
  | requested request resume =>
      have hs (n : Nat) : allowed request ∧ ∀ answer, response request answer →
          Safe step good allowed response n (resume answer) := by
        simpa [Safe, Accepted, h] using safe (n + 1)
      refine ⟨(hs 0).1, ?_⟩
      intro answer valid n
      exact (hs n).2 answer valid
  | failed failure => trivial

theorem accepted_mono
    (h : Accepted good allowed response first observation)
    (imp : ∀ state, first state → second state) :
    Accepted good allowed response second observation := by
  cases observation with
  | next state => exact imp state h
  | returned value => exact h
  | requested request resume => exact ⟨h.1, fun answer valid => imp _ (h.2 answer valid)⟩
  | failed failure => trivial

/-- A transition invariant suffices for all finite observations; no total
termination or eventual response is required. -/
theorem invariant_safe
    (closed : ∀ state, invariant state →
      Accepted good allowed response invariant (step state))
    (initial : invariant state) : SafeAll step good allowed response state := by
  intro depth
  induction depth generalizing state with
  | zero => trivial
  | succ depth ih => exact accepted_mono (closed state initial) (fun _ h => ih h)

/-- An actual finite path may resume a request any number of times. An
individual saved continuation is a function, not a consumed linear token. -/
inductive Transition
    (step : State → Observation State Value Request Response Failure)
    (response : Request → Response → Prop) : State → State → Prop where
  | internal : step state = .next next → Transition step response state next
  | resume : step state = .requested request continuation → response request answer →
      Transition step response state (continuation answer)

inductive Trace
    (step : State → Observation State Value Request Response Failure)
    (response : Request → Response → Prop) : State → State → Prop where
  | refl (state) : Trace step response state state
  | tail : Trace step response start state → Transition step response state next →
      Trace step response start next

theorem transition_safe
    (safe : SafeAll step good allowed response state)
    (transition : Transition step response state next) :
    SafeAll step good allowed response next := by
  have h := safeAll_unfold safe
  cases transition with
  | internal hs => simpa [Accepted, hs] using h
  | resume hs hr =>
      rw [hs] at h
      exact h.2 _ hr

theorem trace_safe
    (safe : SafeAll step good allowed response start)
    (trace : Trace step response start state) :
    SafeAll step good allowed response state := by
  induction trace with
  | refl => exact safe
  | tail _ transition ih => exact transition_safe ih transition

theorem trace_return
    (safe : SafeAll step good allowed response start)
    (trace : Trace step response start state)
    (returned : step state = .returned value) : good value := by
  have h := safeAll_unfold (trace_safe safe trace)
  simpa [Accepted, returned] using h

theorem trace_request
    (safe : SafeAll step good allowed response start)
    (trace : Trace step response start state)
    (requested : step state = .requested request continuation) :
    allowed request ∧ ∀ answer, response request answer →
      SafeAll step good allowed response (continuation answer) := by
  have h := safeAll_unfold (trace_safe safe trace)
  simpa [Accepted, requested] using h

def SlotGood (typed : Value → Ty → Prop) (input : View Value)
    (target : Field Ty) (slot : Nat × Option Value) : Prop :=
  slot.1 = target.1 ∧ SlotTyped typed target.2 slot.2 ∧
    slot.2.isSome = (input target.1).isSome

def OutputsGood (typed : Value → Ty → Prop) (input : View Value)
    (targets : List (Field Ty)) (output : List (Nat × Option Value)) : Prop :=
  Aligned (SlotGood typed input) targets output

theorem outputs_append
    (prior : OutputsGood typed input targets output)
    (last : SlotGood typed input target slot) :
    OutputsGood typed input (targets ++ [target]) (output ++ [slot]) := by
  induction prior with
  | nil => exact .cons last .nil
  | cons head tail ih => exact .cons head ih

theorem outputs_typed (good : OutputsGood typed input targets output) :
    OutputTyped typed targets output := by
  induction good with
  | nil => exact .nil
  | cons head tail ih => exact .cons ⟨head.1, head.2.1⟩ ih

theorem outputs_survivors (good : OutputsGood typed input targets output) (label : Nat) :
    (visible output label).isSome =
      ((input label).isSome && (signature targets label).isSome) := by
  induction good with
  | nil => simp [visible, signature]
  | @cons target slot targets output head tail ih =>
      by_cases equal : label = target.1
      · simpa [visible, signature, head.1, equal] using head.2.2
      · simpa [visible, signature, head.1, equal] using ih

/-- Exact output order, payload typing, and visibility are independent of a
particular payload-machine representation. -/
theorem outputs_view (good : OutputsGood typed input targets output) :
    ViewTyped typed (signature targets) (visible output) ∧
      ∀ label, (visible output label).isSome =
        ((input label).isSome && (signature targets label).isSome) :=
  ⟨outputTyped_visible (outputs_typed good), outputs_survivors good⟩

inductive State (Ty Cast Value Child : Type) where
  | scan (output : List (Nat × Option Value)) (pending : List (FieldPlan Ty Cast))
  | child (output : List (Nat × Option Value)) (entry : FieldPlan Ty Cast)
      (pending : List (FieldPlan Ty Cast)) (active : Child)

/-- The executable record driver implements ordinary ordered bind. A request
exposes exactly the child's packet and retains the record frame in its response
continuation; failure is propagated with its original tag. -/
def step (start : Cast → Value → Child)
    (observe : Child → Observation Child Value Request Response Failure)
    (input : View Value) : State Ty Cast Value Child →
    Observation (State Ty Cast Value Child) (List (Nat × Option Value)) Request Response Failure
  | .scan output [] => .returned output
  | .scan output (.absent target :: pending) =>
      .next (.scan (output ++ [(target.1, none)]) pending)
  | .scan output (entry@(.convert target _ cast) :: pending) =>
      match input target.1 with
      | none => .next (.scan (output ++ [(target.1, none)]) pending)
      | some value => .next (.child output entry pending (start cast value))
  | .child output entry pending active =>
      match observe active with
      | .next next => .next (.child output entry pending next)
      | .returned value => .next (.scan (output ++ [(entry.target.1, some value)]) pending)
      | .requested request resume =>
          .requested request (fun answer => .child output entry pending (resume answer))
      | .failed failure => .failed failure

def ChildrenSafe (typed : Value → Ty → Prop) (resolve : Ty → Ty → Option Cast)
    (start : Cast → Value → Child)
    (observe : Child → Observation Child Value Request Response Failure)
    (allowed : Request → Prop) (response : Request → Response → Prop) : Prop :=
  ∀ a b cast value, resolve a b = some cast → typed value a →
    SafeAll observe (fun result => typed result b) allowed response (start cast value)

/-- The invariant retains the actual pending plan and the already produced
prefix. In the active-child case the original field is still visibly present. -/
inductive StateTyped (typed : Value → Ty → Prop) (source : Signature Ty)
    (known : Nat → Bool) (resolve : Ty → Ty → Option Cast) (input : View Value)
    (observe : Child → Observation Child Value Request Response Failure)
    (allowed : Request → Prop) (response : Request → Response → Prop)
    (targets : List (Field Ty)) : State Ty Cast Value Child → Prop where
  | scan : OutputsGood typed input done output →
      ValidPlan source known resolve todo pending → targets = done ++ todo →
      StateTyped typed source known resolve input observe allowed response targets (.scan output pending)
  | child : OutputsGood typed input done output → entry.Valid source known resolve →
      ValidPlan source known resolve todo pending → targets = done ++ (entry.target :: todo) →
      (input entry.target.1).isSome = true →
      SafeAll observe (fun result => typed result entry.target.2.ty) allowed response active →
      StateTyped typed source known resolve input observe allowed response targets
        (.child output entry pending active)

theorem missing_optional {entry : FieldPlan Ty Cast}
    (valid : entry.Valid source known resolve)
    (inputTyped : ViewTyped typed source input) (presence : PresenceValid known input)
    (missing : input entry.target.1 = none) : entry.target.2.optional = true := by
  cases optional : entry.target.2.optional with
  | true => rfl
  | false =>
      obtain ⟨value, present⟩ := required_input_present valid inputTyped presence optional
      rw [missing] at present
      contradiction

theorem state_closed
    (inputTyped : ViewTyped typed source input) (presence : PresenceValid known input)
    (children : ChildrenSafe typed resolve start observe allowed response)
    (stateTyped : StateTyped typed source known resolve input observe allowed response targets state) :
    Accepted (OutputsGood typed input targets) allowed response
      (StateTyped typed source known resolve input observe allowed response targets)
      (step start observe input state) := by
  cases stateTyped with
  | @scan done output todo pending good valid split =>
      cases valid with
      | nil => simpa [step, Accepted, split] using good
      | @cons target entry todo pending entryValid tailValid =>
          rcases entryValid with ⟨targetEq, fieldValid⟩
          cases entry with
          | absent actual =>
              have absent : input actual.1 = none := by
                have h := inputTyped actual.1
                rw [fieldValid.1] at h
                exact h
              have head : SlotGood typed input target (actual.1, none) := by
                cases targetEq
                exact ⟨rfl, fieldValid.2, by simp [FieldPlan.target, absent]⟩
              exact StateTyped.scan (outputs_append good head) tailValid
                (by simpa [List.append_assoc] using split)
          | convert actual origin cast =>
              cases hv : input actual.1 with
              | none =>
                  have optional := missing_optional fieldValid inputTyped presence hv
                  have head : SlotGood typed input target (actual.1, none) := by
                    cases targetEq
                    exact ⟨rfl, optional, by simp [FieldPlan.target, hv]⟩
                  simpa only [step, hv, Accepted] using
                    StateTyped.scan (observe := observe) (allowed := allowed) (response := response)
                      (outputs_append good head) tailValid
                      (show targets = (done ++ [target]) ++ todo by
                        simpa [List.append_assoc] using split)
              | some value =>
                  have payload := inputTyped actual.1
                  rw [fieldValid.1, hv] at payload
                  have childSafe := children _ _ _ _ fieldValid.2.2 payload
                  simpa only [step, hv, Accepted] using
                    StateTyped.child good fieldValid tailValid
                      (by simpa only [targetEq] using split)
                      (by simp [FieldPlan.target, hv]) childSafe
  | @child done output todo pending active entry good entryValid tailValid split present childSafe =>
      have childClosed := safeAll_unfold childSafe
      cases ho : observe active with
      | next next =>
          have nextSafe : SafeAll observe (fun result => typed result entry.target.2.ty)
              allowed response next := by simpa [Accepted, ho] using childClosed
          simpa only [step, ho, Accepted] using
            StateTyped.child good entryValid tailValid split present nextSafe
      | returned value =>
          have valueTyped : typed value entry.target.2.ty := by
            simpa [Accepted, ho] using childClosed
          have head : SlotGood typed input entry.target (entry.target.1, some value) :=
            ⟨rfl, valueTyped, by simp [present]⟩
          simpa only [step, ho, Accepted] using
            StateTyped.scan (observe := observe) (allowed := allowed) (response := response)
              (outputs_append good head) tailValid
              (show targets = (done ++ [entry.target]) ++ todo by
                simpa [List.append_assoc] using split)
      | requested request resume =>
          have hc : allowed request ∧ ∀ answer, response request answer →
              SafeAll observe (fun result => typed result entry.target.2.ty)
                allowed response (resume answer) := by simpa [Accepted, ho] using childClosed
          simp only [step, ho, Accepted]
          exact ⟨hc.1, fun answer valid =>
            StateTyped.child good entryValid tailValid split present (hc.2 answer valid)⟩
      | failed failure => simp only [step, ho, Accepted]

theorem initial_typed (valid : ValidPlan source known resolve targets plan) :
    StateTyped typed source known resolve input observe allowed response targets (.scan [] plan) :=
  .scan .nil valid rfl

theorem state_transition_preservation
    (inputTyped : ViewTyped typed source input) (presence : PresenceValid known input)
    (children : ChildrenSafe typed resolve start observe allowed response)
    (stateTyped : StateTyped typed source known resolve input observe allowed response targets state)
    (transition : Transition (step start observe input) response state next) :
    StateTyped typed source known resolve input observe allowed response targets next := by
  have closed := state_closed inputTyped presence children stateTyped
  cases transition with
  | internal hs => simpa [Accepted, hs] using closed
  | resume hs valid =>
      rw [hs] at closed
      exact closed.2 _ valid

theorem compiled_trace_invariant
    (compiled : compile source known resolve targets = some plan)
    (inputTyped : ViewTyped typed source input) (presence : PresenceValid known input)
    (children : ChildrenSafe typed resolve start observe allowed response)
    (trace : Trace (step start observe input) response (.scan [] plan) state) :
    StateTyped typed source known resolve input observe allowed response targets state := by
  have initial : StateTyped typed source known resolve input observe allowed response targets
      (.scan [] plan) := initial_typed (compile_sound compiled)
  induction trace with
  | refl => exact initial
  | tail _ transition ih => exact state_transition_preservation inputTyped presence children ih transition

/-- Even after arbitrary earlier child requests and responses, every required
field about to be scanned is genuinely present in this same input view. -/
theorem reachable_required_present
    (compiled : compile source known resolve targets = some plan)
    (inputTyped : ViewTyped typed source input) (presence : PresenceValid known input)
    (children : ChildrenSafe typed resolve start observe allowed response)
    (trace : Trace (step start observe input) response (.scan [] plan) (.scan output (entry :: pending)))
    (required : entry.target.2.optional = false) :
    ∃ value, input entry.target.1 = some value := by
  have invariant := compiled_trace_invariant compiled inputTyped presence children trace
  cases invariant with
  | scan good valid split =>
      cases valid with
      | cons head tail => exact required_input_present head.2 inputTyped presence required

/-- The complete finite-prefix contract is constructed from an actual compiled
plan. Its premises contain only input and child contracts, not record safety. -/
theorem compiled_safe
    (compiled : compile source known resolve targets = some plan)
    (inputTyped : ViewTyped typed source input) (presence : PresenceValid known input)
    (children : ChildrenSafe typed resolve start observe allowed response) :
    SafeAll (step start observe input) (OutputsGood typed input targets)
      allowed response (.scan [] plan) :=
  invariant_safe (fun _ h => state_closed inputTyped presence children h)
    (initial_typed (compile_sound compiled))

theorem compiled_prefix_return
    (compiled : compile source known resolve targets = some plan)
    (inputTyped : ViewTyped typed source input) (presence : PresenceValid known input)
    (children : ChildrenSafe typed resolve start observe allowed response)
    (trace : Trace (step start observe input) response (.scan [] plan) state)
    (returned : step start observe input state = .returned output) :
    ViewTyped typed (signature targets) (visible output) ∧
      ∀ label, (visible output label).isSome =
        ((input label).isSome && (signature targets label).isSome) :=
  outputs_view (trace_return (compiled_safe compiled inputTyped presence children) trace returned)

theorem compiled_prefix_request
    (compiled : compile source known resolve targets = some plan)
    (inputTyped : ViewTyped typed source input) (presence : PresenceValid known input)
    (children : ChildrenSafe typed resolve start observe allowed response)
    (trace : Trace (step start observe input) response (.scan [] plan) state)
    (requested : step start observe input state = .requested request continuation) :
    allowed request ∧ ∀ answer, response request answer →
      SafeAll (step start observe input) (OutputsGood typed input targets)
        allowed response (continuation answer) :=
  trace_request (compiled_safe compiled inputTyped presence children) trace requested

/-- Both uses of the very same saved record continuation satisfy the contract;
they need not return the same payload or traverse the same subsequent path. -/
theorem compiled_repeated_response
    (compiled : compile source known resolve targets = some plan)
    (inputTyped : ViewTyped typed source input) (presence : PresenceValid known input)
    (children : ChildrenSafe typed resolve start observe allowed response)
    (trace : Trace (step start observe input) response (.scan [] plan) state)
    (requested : step start observe input state = .requested request continuation)
    (first : response request answer₁) (second : response request answer₂) :
    SafeAll (step start observe input) (OutputsGood typed input targets)
        allowed response (continuation answer₁) ∧
      SafeAll (step start observe input) (OutputsGood typed input targets)
        allowed response (continuation answer₂) := by
  have h := compiled_prefix_request compiled inputTyped presence children trace requested
  exact ⟨h.2 _ first, h.2 _ second⟩

/-- Native indexed shape filling uses the same boundary-scoped resolver. The
proof does not relabel that query as an executable source adaptation. -/
theorem native_filled_safe
    (shaped : NativeRecordPlan.shape boundary sourceFields index targets = .ok slots)
    (filled : NativeRecordPlan.fill resolve slots = some plan)
    (inputTyped : ViewTyped typed (signature sourceFields) input)
    (children : ChildrenSafe typed (resolve boundary) start observe allowed response) :
    SafeAll (step start observe input) (OutputsGood typed input targets)
      allowed response (.scan [] plan) := by
  apply compiled_safe (NativeRecordPlan.filled_compile shaped filled) inputTyped
  · intro label falseProof
    contradiction
  · exact children

theorem child_request_exact
    {observe : Child → Observation Child Value Request Response Failure}
    (requested : observe active = .requested request continuation) :
    step start observe input (.child output entry pending active) =
      .requested request (fun answer => .child output entry pending (continuation answer)) := by
  simp only [step, requested]

theorem child_failure_exact
    {observe : Child → Observation Child Value Request Response Failure}
    {failure : Failure}
    (failed : observe active = .failed failure) :
    step start observe input (.child output entry pending active) = .failed failure := by
  simp only [step, failed]

namespace Witness

inductive Payload where
  | waiting (original : Nat)
  | done (answer : Nat)
  | spinning

def observe : Payload → Observation Payload Nat Nat Nat Nat
  | .waiting original => .requested original Payload.done
  | .done answer => .returned answer
  | .spinning => .next .spinning

def start (_ : Unit) (value : Nat) : Payload := .waiting value
def typed (_ : Nat) (_ : Unit) : Prop := True
def allowed (_ : Nat) : Prop := True
def response (_ _ : Nat) : Prop := True
def resolve (_ _ : Unit) : Option Unit := some ()
def input : View Nat := fun label => if label = 0 then some 5 else none
def source : Signature Unit := signature [(0, ⟨(), false⟩)]
def targets : List (Field Unit) := [(0, ⟨(), false⟩), (1, ⟨(), true⟩)]
def required : FieldPlan Unit Unit := .convert (0, ⟨(), false⟩) ⟨(), false⟩ ()
def optional : FieldPlan Unit Unit := .absent (1, ⟨(), true⟩)
def plan : List (FieldPlan Unit Unit) := [required, optional]

theorem all_payload_states_safe (state : Payload) :
    SafeAll observe (fun value => typed value ()) allowed response state := by
  apply invariant_safe (invariant := fun _ => True) _ trivial
  intro current _
  cases current <;> simp [observe, Accepted, typed, allowed]

theorem child_contract : ChildrenSafe typed resolve start observe allowed response := by
  intro a b cast value _ _
  cases b
  exact all_payload_states_safe _

theorem plan_compiled : compile source (fun _ => false) resolve targets = some plan := by
  decide

theorem input_typed : ViewTyped typed source input := by
  intro label
  by_cases equal : label = 0
  · simp [source, signature, input, equal, SlotTyped, typed]
  · simp [source, signature, input, equal]

def initial : State Unit Unit Nat Payload := .scan [] plan
def suspended : State Unit Unit Nat Payload := .child [] required [optional] (.waiting 5)
def saved (answer : Nat) : State Unit Unit Nat Payload := .child [] required [optional] (.done answer)
def completed (answer : Nat) : State Unit Unit Nat Payload :=
  .scan [(0, some answer), (1, none)] []

theorem request_keeps_original_packet_and_pending :
    step start observe input initial = .next suspended ∧
      step start observe input suspended = .requested 5 saved := by
  constructor <;> rfl

theorem answer_path (answer : Nat) :
    Trace (step start observe input) response (saved answer) (completed answer) := by
  apply Trace.tail (next := completed answer)
  · exact Trace.tail (.refl _) (.internal rfl)
  · exact .internal rfl

theorem both_answers_safe (first second : Nat) :
    SafeAll (step start observe input) (OutputsGood typed input targets) allowed response (saved first) ∧
      SafeAll (step start observe input) (OutputsGood typed input targets) allowed response (saved second) := by
  apply compiled_repeated_response plan_compiled input_typed
    (show PresenceValid (fun _ => false) input from fun _ h => by contradiction)
    child_contract (Trace.tail (.refl _) (.internal rfl))
    (show step start observe input suspended = .requested 5 saved from rfl) trivial trivial

theorem two_distinct_results_from_one_saved_frame :
    step start observe input (completed 7) = .returned [(0, some 7), (1, none)] ∧
      step start observe input (completed 9) = .returned [(0, some 9), (1, none)] ∧
      Trace (step start observe input) response (saved 7) (completed 7) ∧
      Trace (step start observe input) response (saved 9) (completed 9) :=
  ⟨rfl, rfl, answer_path 7, answer_path 9⟩

/-- A genuine self-loop meets every finite-prefix contract and never returns
in one step. Thus the proof does not get safety by assuming termination. -/
theorem divergent_payload_prefixes :
    SafeAll observe (fun value => typed value ()) allowed response .spinning ∧
      observe .spinning = .next .spinning := ⟨all_payload_states_safe _, rfl⟩

end Witness

end YulangClosure.RecordBoundaryExecution
