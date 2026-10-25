import YulangClosure.HigherOrderHandlerSafety

namespace YulangClosure.HigherOrder.Handler.Interaction
open YulangClosure.HigherOrder (Ty emptyContext extend OperationInstance)
open YulangClosure.HigherOrder.Handler

/-! Candidate root-only immutable arena over the exact Handler grammar.
All interior movement uses Handler.Step; no context extraction or handler bypass
is an arena rule. Scheduling follows the accepted prior Interaction interface:
ANY existing handle may replace the current branch in either phase. This is a
research scheduler, not native scheduling or activation freshening authority. -/

structure Saved where
  operation : OperationInstance
  payload : Value
  continuation : Comp

def Saved.request (s : Saved) : Comp :=
  .request s.operation s.payload s.continuation

def Saved.resume (s : Saved) (response : Value) : Comp :=
  substComp (single response) s.continuation

theorem publication_has_no_internal_step (saved : Saved) :
    ¬ Step saved.request event next := by
  intro step
  cases step

/-- Handles are stable natural-number positions; publication appends. -/
def lookup : List Saved → Nat → Option Saved
  | [], _ => none
  | s :: _, 0 => some s
  | _ :: ss, h + 1 => lookup ss h

theorem lookup_length_none (arena : List Saved) : lookup arena arena.length = none := by
  induction arena with
  | nil => rfl
  | cons head tail ih => exact ih

theorem lookup_append_old (found : lookup arena handle = some saved) :
    lookup (arena ++ [added]) handle = some saved := by
  induction arena generalizing handle with
  | nil => cases found
  | cons head tail ih =>
      cases handle with
      | zero => exact found
      | succ handle => exact ih found

theorem lookup_append_fresh (arena : List Saved) (saved : Saved) :
    lookup (arena ++ [saved]) arena.length = some saved := by
  induction arena with
  | nil => rfl
  | cons head tail ih => exact ih

theorem lookup_append_cases
    (found : lookup (arena ++ [added]) handle = some saved) :
    lookup arena handle = some saved ∨ saved = added := by
  induction arena generalizing handle with
  | nil =>
      cases handle with
      | zero => exact .inr (Option.some.inj found).symm
      | succ handle => cases found
  | cons head tail ih =>
      cases handle with
      | zero => exact .inl found
      | succ handle => exact ih found

/-- A newly allocated handle is exactly the previous arena length. -/
theorem lookup_append_origin
    (found : lookup (arena ++ [added]) handle = some saved) :
    lookup arena handle = some saved ∨ handle = arena.length ∧ saved = added := by
  induction arena generalizing handle with
  | nil =>
      cases handle with
      | zero => exact .inr ⟨rfl, (Option.some.inj found).symm⟩
      | succ handle => cases found
  | cons head tail ih =>
      cases handle with
      | zero => exact .inl found
      | succ handle =>
          rcases ih found with old | ⟨index, entry⟩
          · exact .inl old
          · exact .inr ⟨congrArg Nat.succ index, entry⟩

/-- Derived only from typing the actual published root request. -/
def SavedTyped (saved : Saved) (result : Ty) : Prop :=
  ValueTyped emptyContext saved.payload saved.operation.payloadType ∧
  CompTyped (extend emptyContext saved.operation.responseType)
    saved.continuation result

theorem capture_typed {saved : Saved} (h : CompTyped emptyContext saved.request a) :
    SavedTyped saved a := by
  cases h with
  | request hp hk => exact ⟨hp, hk⟩

theorem saved_request_typed (h : SavedTyped saved a) :
    CompTyped emptyContext saved.request a := .request h.1 h.2

theorem saved_resume_typed (h : SavedTyped saved a)
    (hr : ValueTyped emptyContext response saved.operation.responseType) :
    CompTyped emptyContext (saved.resume response) a := substitute_top h.2 hr

def ArenaTyped (arena : List Saved) (a : Ty) : Prop :=
  ∀ handle saved, lookup arena handle = some saved → SavedTyped saved a

theorem arena_append_typed (h : ArenaTyped arena a) (hs : SavedTyped saved a) :
    ArenaTyped (arena ++ [saved]) a := by
  intro handle entry found
  rcases lookup_append_cases found with old | rfl
  · exact h handle entry old
  · exact hs

inductive Phase where
  | running
  | waiting (handle : Nat)

structure State where
  current : Comp
  arena : List Saved
  phase : Phase

def WaitingCoherent (s : State) : Prop :=
  match s.phase with
  | .running => True
  | .waiting handle =>
      ∃ saved, lookup s.arena handle = some saved ∧ s.current = saved.request

structure StateTyped (s : State) (a : Ty) : Prop where
  currentTyped : CompTyped emptyContext s.current a
  arenaTyped : ArenaTyped s.arena a
  waitingCoherent : WaitingCoherent s

inductive Action where
  | internal (event : Event)
  | publish (handle : Nat) (saved : Saved)
  | response (handle : Nat) (operation : OperationInstance) (value : Value)

/-- Raw transitions are independent of typing, protocol, and preservation.
An external scheduler may select ANY existing handle, including an old handle
while another computation is running or waiting. Resume never removes entries. -/
inductive RawStep : State → Action → State → Prop where
  | internal : Step m e n →
      RawStep ⟨m, arena, .running⟩ (.internal e) ⟨n, arena, .running⟩
  | publish (arena : List Saved) (saved : Saved) :
      RawStep ⟨saved.request, arena, .running⟩ (.publish arena.length saved)
        ⟨saved.request, arena ++ [saved], .waiting arena.length⟩
  | response : lookup arena handle = some saved →
      RawStep ⟨m, arena, phase⟩ (.response handle suppliedOperation response)
        ⟨saved.resume response, arena, .running⟩

/-- External response obligation, stated separately from RawStep. Instance
matching is equality of the FULL instance (identity, arguments, both types).
No existence of an inhabitant of any response type is assumed. -/
def Protocol (s : State) : Action → Prop
  | .internal _ => True
  | .publish _ _ => True
  | .response handle suppliedOperation response =>
      ∃ saved, lookup s.arena handle = some saved ∧
        suppliedOperation = saved.operation ∧
        ValueTyped emptyContext response saved.operation.responseType

theorem response_protocol {s : State} (found : lookup s.arena handle = some saved)
    (typed : ValueTyped emptyContext response saved.operation.responseType) :
    Protocol s (.response handle saved.operation response) :=
  ⟨saved, found, rfl, typed⟩

theorem protocol_association {s : State}
    (found : lookup s.arena handle = some saved)
    (protocol : Protocol s (.response handle supplied response)) :
    supplied = saved.operation ∧
    ValueTyped emptyContext response saved.operation.responseType := by
  obtain ⟨other, ho, hop, hr⟩ := protocol
  have equal : other = saved := Option.some.inj (ho.symm.trans found)
  subst other
  exact ⟨hop, hr⟩

theorem wrong_instance_rejected {s : State}
    (found : lookup s.arena handle = some saved) (wrong : supplied ≠ saved.operation) :
    ¬ Protocol s (.response handle supplied response) := by
  intro protocol
  exact wrong (protocol_association found protocol).1

theorem missing_handle_rejected {s : State} (missing : lookup s.arena handle = none) :
    ¬ Protocol s (.response handle supplied response) := by
  rintro ⟨saved, found, _, _⟩
  rw [missing] at found
  cases found

theorem step_preservation (step : RawStep s action t)
    (protocol : Protocol s action) (typed : StateTyped s a) : StateTyped t a := by
  cases step with
  | internal step =>
      exact ⟨preservation step typed.currentTyped, typed.arenaTyped, True.intro⟩
  | publish arena saved =>
      exact ⟨typed.currentTyped,
        arena_append_typed typed.arenaTyped (capture_typed typed.currentTyped),
        saved, lookup_append_fresh arena saved, rfl⟩
  | response found =>
      have association := protocol_association found protocol
      exact ⟨saved_resume_typed (typed.arenaTyped _ _ found) association.2,
        typed.arenaTyped, True.intro⟩

/-- Equality of all old entries is stronger than merely retaining their types. -/
def ArenaExtends (old newer : List Saved) : Prop :=
  ∀ handle saved, lookup old handle = some saved → lookup newer handle = some saved

theorem step_immutable (step : RawStep s action t) : ArenaExtends s.arena t.arena := by
  intro handle saved found
  cases step with
  | internal _ => exact found
  | publish _ _ => exact lookup_append_old found
  | response _ => exact found

theorem step_origin (step : RawStep s action t)
    (found : lookup t.arena handle = some saved) :
    lookup s.arena handle = some saved ∨ action = .publish handle saved := by
  cases step with
  | internal _ => exact .inl found
  | response _ => exact .inl found
  | publish arena added =>
      rcases lookup_append_origin found with old | ⟨index, entry⟩
      · exact .inl old
      · cases index
        cases entry
        exact .inr rfl

/-- The protocol does not conceal a preservation premise in a trace rule. -/
inductive Trace : State → List Action → State → Prop where
  | refl (s : State) : Trace s [] s
  | cons : RawStep s action t → Protocol s action → Trace t actions last →
      Trace s (action :: actions) last

theorem trace_preservation (trace : Trace s actions t) (typed : StateTyped s a) :
    StateTyped t a := by
  induction trace with
  | refl => exact typed
  | cons step protocol rest ih => exact ih (step_preservation step protocol typed)

theorem trace_immutable (trace : Trace s actions t) : ArenaExtends s.arena t.arena := by
  induction trace with
  | refl => exact fun _ _ found => found
  | cons step protocol rest ih =>
      exact fun handle saved found => ih handle saved (step_immutable step handle saved found)

/-- Every final entry is either initial data or has an actual publication
in this very trace. Stable handles associate it with that exact publication. -/
theorem trace_origin (trace : Trace s actions t)
    (found : lookup t.arena handle = some saved) :
    lookup s.arena handle = some saved ∨ Action.publish handle saved ∈ actions := by
  induction trace generalizing handle saved with
  | refl => exact .inl found
  | cons step protocol rest ih =>
      rcases ih found with before | later
      · rcases step_origin step before with old | event
        · exact .inl old
        · exact .inr (by simp [event])
      · exact .inr (by simp [later])

/-- Concrete progress alternatives; an arbitrary stuck term is not terminal.
Waiting records the actual published request, including its entire restored continuation. -/
inductive Progress : State → Prop where
  | returned (v arena) : Progress ⟨.ret v, arena, .running⟩
  | failed (reason arena) :
      Progress ⟨.fail reason, arena, .running⟩
  | waiting (found : lookup arena handle = some saved) :
      Progress ⟨saved.request, arena, .waiting handle⟩
  | advance : RawStep s action t → Protocol s action → Progress s

theorem state_progress (typed : StateTyped s a) : Progress s := by
  rcases s with ⟨m, arena, phase⟩
  cases phase with
  | waiting handle =>
      obtain ⟨saved, found, equal⟩ := typed.waitingCoherent
      cases equal
      exact .waiting found
  | running =>
      rcases closed_progress typed.currentTyped with terminal | ⟨e, n, step⟩
      · cases terminal with
        | returned v => exact .returned _ _
        | failed reason => exact .failed _ _
        | requested op payload continuation =>
            exact .advance (.publish arena ⟨op, payload, continuation⟩) True.intro
      · exact .advance (.internal step) True.intro

/-- HO-HANDLER-INTERACTION-1: EVERY finite protocol-respecting prefix, all saved
continuations, the same current result type, and concrete progress. -/
theorem finite_interaction_safety (typed : StateTyped s a) (trace : Trace s actions t) :
    StateTyped t a ∧ Progress t ∧ ArenaExtends s.arena t.arena := by
  have ht := trace_preservation trace typed
  exact ⟨ht, state_progress ht, trace_immutable trace⟩

def initial (m : Comp) : State := ⟨m, [], .running⟩

theorem initial_typed (h : CompTyped emptyContext m a) : StateTyped (initial m) a := by
  refine ⟨h, ?_, True.intro⟩
  intro handle saved found
  cases found

theorem closed_program_interaction_safety (h : CompTyped emptyContext m a)
    (trace : Trace (initial m) actions t) : StateTyped t a ∧ Progress t := by
  have safe := finite_interaction_safety (initial_typed h) trace
  exact ⟨safe.1, safe.2.1⟩

theorem initial_saved_origin (trace : Trace (initial m) actions t)
    (found : lookup t.arena handle = some saved) :
    Action.publish handle saved ∈ actions := by
  rcases trace_origin trace found with impossible | published
  · cases impossible
  · exact published

/-- An observed response has exactly the saved payload, full instance and
continuation association, together with the externally supplied response type. -/
theorem typed_response_association (typed : StateTyped s a)
    (found : lookup s.arena handle = some saved)
    (protocol : Protocol s (.response handle supplied response)) :
    supplied = saved.operation ∧
    ValueTyped emptyContext saved.payload saved.operation.payloadType ∧
    ValueTyped emptyContext response saved.operation.responseType ∧
    CompTyped emptyContext (saved.resume response) a := by
  obtain ⟨instanceEq, responseTyped⟩ := protocol_association found protocol
  have hs := typed.arenaTyped handle saved found
  exact ⟨instanceEq, hs.1, responseTyped, saved_resume_typed hs responseTyped⟩

/-- The explicit external premise suffices for every selected old handle. -/
theorem resume_progress (typed : StateTyped s a)
    (found : lookup s.arena handle = some saved)
    (responseTyped : ValueTyped emptyContext response saved.operation.responseType) :
    StateTyped ⟨saved.resume response, s.arena, .running⟩ a ∧
    Progress ⟨saved.resume response, s.arena, .running⟩ := by
  have resumed : CompTyped emptyContext (saved.resume response) a :=
    saved_resume_typed (typed.arenaTyped _ _ found) responseTyped
  have ht : StateTyped ⟨saved.resume response, s.arena, .running⟩ a :=
    ⟨resumed, typed.arenaTyped, True.intro⟩
  exact ⟨ht, state_progress ht⟩

/-- Apply the trace invariant back to ANY captured handle and ANY independently
typed response, retaining publication provenance and concrete resumed progress. -/
theorem finite_saved_response_safety (initialTyping : CompTyped emptyContext m a)
    (trace : Trace (initial m) actions t)
    (found : lookup t.arena handle = some saved)
    (responseTyped : ValueTyped emptyContext response saved.operation.responseType) :
    Action.publish handle saved ∈ actions ∧
    StateTyped ⟨saved.resume response, t.arena, .running⟩ a ∧
    Progress ⟨saved.resume response, t.arena, .running⟩ := by
  have ht := trace_preservation trace (initial_typed initialTyping)
  exact ⟨initial_saved_origin trace found, resume_progress ht found responseTyped⟩

/-- Capture records exactly the pending request and its payload; lookup at its
fresh handle yields that same record, including the entire restored continuation. -/
theorem publication_association (arena : List Saved) (op payload continuation) :
    lookup (arena ++ [⟨op, payload, continuation⟩]) arena.length =
      some ⟨op, payload, continuation⟩ := lookup_append_fresh _ _

/-- Publication exposes the actual current root, never an interior request. -/
theorem publication_root (step : RawStep s (.publish handle saved) t) :
    s.current = saved.request ∧ s.phase = .running ∧
    handle = s.arena.length ∧ t.arena = s.arena ++ [saved] := by
  cases step
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem handler_cannot_publish
    (h : Handler) (m : Comp) (arena : List Saved) (phase : Phase) :
    ¬ RawStep ⟨.handle h m, arena, phase⟩ (.publish handle saved) t := by
  intro step
  have root := (publication_root step).1
  cases root

/-- Any finite actual internal prefix embeds without changing the arena. -/
theorem internal_prefix (trace : Prefix m events n) (arena : List Saved) :
    Trace ⟨m, arena, .running⟩ (events.map Action.internal) ⟨n, arena, .running⟩ := by
  induction trace with
  | refl => exact .refl _
  | cons step rest ih => exact .cons (.internal step) True.intro ih

theorem trace_append (first : Trace s xs t) (second : Trace t ys u) :
    Trace s (xs ++ ys) u := by
  induction first generalizing ys u with
  | refl => exact second
  | cons step protocol rest ih => exact .cons step protocol (ih second)

/-- Repeat any finite list of independently supplied values at one handle. -/
def replay (arena : List Saved) (saved : Saved) : Comp → List Value → Comp
  | m, [] => m
  | _, value :: values => replay arena saved (saved.resume value) values

def responseActions (handle : Nat) (saved : Saved) (values : List Value) : List Action :=
  values.map (fun value => .response handle saved.operation value)

theorem repeat_handle (found : lookup arena handle = some saved)
    (typed : ∀ value, value ∈ values → ValueTyped emptyContext value saved.operation.responseType)
    (m : Comp) :
    Trace ⟨m, arena, .running⟩ (responseActions handle saved values)
      ⟨replay arena saved m values, arena, .running⟩ := by
  induction values generalizing m with
  | nil => exact .refl _
  | cons value values ih =>
      refine .cons (.response found) (response_protocol found (typed value (by simp))) ?_
      exact ih (fun v hv => typed v (by simp [hv])) (saved.resume value)

/-- Publication of a new request does not invalidate an arbitrary old handle. -/
theorem capture_then_old_response (found : lookup arena handle = some old)
    (typed : ValueTyped emptyContext value old.operation.responseType) (fresh : Saved) :
    Trace ⟨fresh.request, arena, .running⟩
      [.publish arena.length fresh, .response handle old.operation value]
      ⟨old.resume value, arena ++ [fresh], .running⟩ :=
  .cons (.publish arena fresh) True.intro
    (.cons (.response (lookup_append_old found))
      (response_protocol (lookup_append_old found) typed) (.refl _))

/-- Independent handles can be revisited in either order; no last-capture rule. -/
theorem handles_in_any_order (first : lookup arena h1 = some s1)
    (second : lookup arena h2 = some s2)
    (t1 : ValueTyped emptyContext r1 s1.operation.responseType)
    (t2 : ValueTyped emptyContext r2 s2.operation.responseType) (m : Comp) :
    Trace ⟨m, arena, .running⟩
      [.response h1 s1.operation r1, .response h2 s2.operation r2,
       .response h1 s1.operation r1]
      ⟨s1.resume r1, arena, .running⟩ :=
  .cons (.response first) (response_protocol first t1)
    (.cons (.response second) (response_protocol second t2)
      (.cons (.response first) (response_protocol first t1) (.refl _)))

/-- Failure to inhabit a response type yields an honest wait, not an axiom
postulating a response. This uses the accepted canonical-bottom theorem. -/
theorem bottom_response_unavailable {s : State} (found : lookup s.arena handle = some saved)
    (bottom : saved.operation.responseType = .bottom) :
    ¬ Protocol s (.response handle operation response) := by
  intro protocol
  have hv := (protocol_association found protocol).2
  rw [bottom] at hv
  exact bottom_empty hv

/-- An action appearing in a trace is backed by an actual transition in that
trace, whose source current computation is the saved root request. -/
theorem trace_publication_witness (trace : Trace s actions t)
    (member : Action.publish handle saved ∈ actions) :
    ∃ before after, RawStep before (.publish handle saved) after ∧
      before.current = saved.request := by
  induction trace with
  | refl => cases member
  | cons step protocol rest ih =>
      rcases List.mem_cons.mp member with equal | later
      · subst equal
        exact ⟨_, _, step, (publication_root step).1⟩
      · exact ih later

/-- Locate publication within this exact trace, retaining both executable
prefix and suffix rather than only an unconnected transition witness. -/
theorem trace_publication_split (trace : Trace s actions t)
    (member : Action.publish handle saved ∈ actions) :
    ∃ priorActions before after suffix,
      actions = priorActions ++ (.publish handle saved :: suffix) ∧
      Trace s priorActions before ∧ RawStep before (.publish handle saved) after ∧
      Protocol before (.publish handle saved) ∧ Trace after suffix t := by
  induction trace with
  | refl => cases member
  | cons step protocol rest ih =>
      rcases List.mem_cons.mp member with equal | later
      · subst equal
        exact ⟨[], _, _, _, rfl, .refl _, step, protocol, rest⟩
      · obtain ⟨priorActions, before, after, suffix, equal, first, publication, admissible, last⟩ := ih later
        exact ⟨_ :: priorActions, before, after, suffix,
          congrArg (List.cons _) equal, .cons step protocol first,
          publication, admissible, last⟩

/-- The complete empty-arena result, including actual publication witnesses. -/
theorem empty_arena_safety (h : CompTyped emptyContext m a)
    (trace : Trace (initial m) actions t) :
    StateTyped t a ∧ Progress t ∧
    (∀ handle saved, lookup t.arena handle = some saved →
      Action.publish handle saved ∈ actions ∧
      ∃ before after, RawStep before (.publish handle saved) after ∧
        before.current = saved.request) := by
  have ht := trace_preservation trace (initial_typed h)
  refine ⟨ht, state_progress ht, ?_⟩
  intro handle saved found
  have member := initial_saved_origin trace found
  exact ⟨member, trace_publication_witness trace member⟩

/-! Concrete actual-handler traces. No arena extraction of an interior request
is used in any example. Each safety corollary invokes the universal invariant. -/

/-- An effectful first arm rejects after a response; the second arm succeeds. -/
def interactionHandler : Handler :=
  .mk 80 unitType boolType (.cons yesAttempt .nil)
    (.cons unitOperation true (.request nestedOperation .unit noAttempt)
      (.cons unitOperation true yesAttempt .nil))

theorem interactionHandler_typed :
    HandlerTyped emptyContext interactionHandler unitType boolType :=
  .mk (.cons (.ret (.inRight .bool)) .nil)
    (.cons (.request .unit (.ret (.inLeft .unit)))
      (.cons (.ret (.inRight .bool)) .nil))

def interactionProgram : Comp :=
  .handle interactionHandler (.request unitOperation .unit (.ret (.var 0)))

theorem interactionProgram_typed : CompTyped emptyContext interactionProgram boolType :=
  .handle interactionHandler_typed (.request .unit (.ret (.var rfl)))

def pendingSaved : Saved :=
  ⟨nestedOperation, .unit,
    .waitOperation (renameHandler Nat.succ interactionHandler) unitOperation
      (renameValue Nat.succ .unit) (renameComp (Original.up Nat.succ) (.ret (.var 0)))
      (renameOperationArms Nat.succ (.cons unitOperation true yesAttempt .nil))
      noAttempt⟩

theorem pending_root_prefix :
    Prefix interactionProgram [.silent, .silent, .silent] pendingSaved.request :=
  .cons .handleRequest (.cons .operationCons (.cons .operationRequest (.refl _)))

def pendingActions : List Action :=
  [.internal .silent, .internal .silent, .internal .silent, .publish 0 pendingSaved]

theorem pending_capture :
    Trace (initial interactionProgram) pendingActions
      ⟨pendingSaved.request, [pendingSaved], .waiting 0⟩ :=
  .cons (.internal .handleRequest) True.intro
    (.cons (.internal .operationCons) True.intro
      (.cons (.internal .operationRequest) True.intro
        (.cons (.publish [] pendingSaved) True.intro (.refl _))))

theorem pending_capture_safe :
    StateTyped ⟨pendingSaved.request, [pendingSaved], .waiting 0⟩ boolType ∧
    Progress ⟨pendingSaved.request, [pendingSaved], .waiting 0⟩ :=
  closed_program_interaction_safety interactionProgram_typed pending_capture

/-- Returning the nested response resumes the retained wait, observes No,
then actually executes the remaining matching arm and observes Yes. -/
theorem pending_resume_remaining (response : Value)
    (typed : ValueTyped emptyContext response boolType) :
    Trace ⟨pendingSaved.request, [pendingSaved], .waiting 0⟩
      [.response 0 nestedOperation response,
       .internal .silent, .internal .silent, .internal .silent]
      ⟨.ret (.bool true), [pendingSaved], .running⟩ :=
  .cons (.response (saved := pendingSaved) rfl) ⟨pendingSaved, rfl, rfl, typed⟩
    (.cons (.internal .operationNo) True.intro
      (.cons (.internal .operationCons) True.intro
        (.cons (.internal .operationYes) True.intro (.refl _))))

theorem pending_complete_safe (response : Value)
    (typed : ValueTyped emptyContext response boolType) :
    StateTyped ⟨.ret (.bool true), [pendingSaved], .running⟩ boolType ∧
    Progress ⟨.ret (.bool true), [pendingSaved], .running⟩ :=
  closed_program_interaction_safety interactionProgram_typed
    (trace_append pending_capture (pending_resume_remaining response typed))

/-- Both values really use the same immutable entry, including after completion
of the first response's remaining ordered trial. -/
theorem pending_two_distinct_responses :
    ∃ actions, Trace (initial interactionProgram) actions
      ⟨pendingSaved.resume (.bool false), [pendingSaved], .running⟩ ∧
      StateTyped ⟨pendingSaved.resume (.bool false), [pendingSaved], .running⟩ boolType := by
  have first := trace_append pending_capture (pending_resume_remaining (.bool true) .bool)
  have again : Trace ⟨.ret (.bool true), [pendingSaved], .running⟩
      [.response 0 nestedOperation (.bool false)]
      ⟨pendingSaved.resume (.bool false), [pendingSaved], .running⟩ :=
    .cons (.response (saved := pendingSaved) rfl) ⟨pendingSaved, rfl, rfl, .bool⟩ (.refl _)
  have both := trace_append first again
  exact ⟨_, both, trace_preservation both (initial_typed interactionProgram_typed)⟩

/-- Exhaustion captures restored HK, with result bool, not the selected arm's
original unit-result K. The accepted selected_execution actually calls K. -/
def forwardedSaved : Saved :=
  ⟨unitOperation, .unit, forwardedContinuation forwardingHandler (.ret (.var 0))⟩

theorem forwarded_capture :
    Trace (initial (.handle forwardingHandler (.request unitOperation .unit (.ret (.var 0)))))
      [.internal .silent, .internal .silent, .publish 0 forwardedSaved]
      ⟨forwardedSaved.request, [forwardedSaved], .waiting 0⟩ :=
  .cons (.internal .handleRequest) True.intro
    (.cons (.internal .operationEmpty) True.intro
      (.cons (.publish [] forwardedSaved) True.intro (.refl _)))

theorem forwarded_capture_safe : SavedTyped forwardedSaved boolType :=
  (trace_preservation forwarded_capture
    (initial_typed (.handle forwardingHandler_typed (.request .unit (.ret (.var rfl)))))).arenaTyped
    0 forwardedSaved rfl

theorem selected_original_execution_safe : ∃ actions,
    Trace (initial selectedProgram) actions ⟨.ret (.bool true), [], .running⟩ ∧
    StateTyped ⟨.ret (.bool true), [], .running⟩ boolType := by
  obtain ⟨events, execution⟩ := selected_execution
  have trace := internal_prefix execution []
  exact ⟨_, trace, trace_preservation trace (initial_typed selectedProgram_typed)⟩

/-- A second request is captured after the first one. The scheduler then
uses the old handle while the newer request is waiting. -/
def laterSaved : Saved := ⟨nestedOperation, .unit, .ret (.var 0)⟩
def earlierSaved : Saved := ⟨nestedOperation, .unit, laterSaved.request⟩

theorem earlier_request_typed : CompTyped emptyContext earlierSaved.request boolType :=
  .request .unit (.request .unit (.ret (.var rfl)))

theorem old_after_new_capture :
    Trace (initial earlierSaved.request)
      [.publish 0 earlierSaved, .response 0 nestedOperation (.bool true),
       .publish 1 laterSaved, .response 0 nestedOperation (.bool false)]
      ⟨earlierSaved.resume (.bool false), [earlierSaved, laterSaved], .running⟩ :=
  .cons (.publish [] earlierSaved) True.intro
    (.cons (.response (saved := earlierSaved) rfl) ⟨earlierSaved, rfl, rfl, .bool⟩
      (.cons (.publish [earlierSaved] laterSaved) True.intro
        (.cons (.response (saved := earlierSaved) rfl) ⟨earlierSaved, rfl, rfl, .bool⟩ (.refl _))))

theorem old_after_new_safe :
    StateTyped ⟨earlierSaved.resume (.bool false), [earlierSaved, laterSaved], .running⟩ boolType ∧
    Progress ⟨earlierSaved.resume (.bool false), [earlierSaved, laterSaved], .running⟩ :=
  closed_program_interaction_safety earlier_request_typed old_after_new_capture

/-- The response is the actual handler-bearing lambda with actual consumer
code. The request continuation calls it instead of treating it as opaque data. -/
def callbackOperation : OperationInstance :=
  ⟨81, [unitType, boolType], unitType, .callable unitType boolType⟩

def callbackSaved : Saved :=
  ⟨callbackOperation, .unit, .dynamicCall (.var 0) (.delay (.ret .unit))⟩

theorem callback_request_typed : CompTyped emptyContext callbackSaved.request boolType :=
  .request .unit (.dynamicCall (.var rfl) (.delay (.ret .unit)))

theorem callback_capture_response :
    Trace (initial callbackSaved.request)
      [.publish 0 callbackSaved, .response 0 callbackOperation nestedLambda]
      ⟨.dynamicCall nestedLambda (.delay (.ret .unit)), [callbackSaved], .running⟩ :=
  .cons (.publish [] callbackSaved) True.intro
    (.cons (.response (saved := callbackSaved) rfl) ⟨callbackSaved, rfl, rfl, nestedLambda_typed⟩ (.refl _))

theorem callback_every_internal_prefix_safe
    (execution : Prefix (.dynamicCall nestedLambda (.delay (.ret .unit))) events n) :
    StateTyped ⟨n, [callbackSaved], .running⟩ boolType ∧
    Progress ⟨n, [callbackSaved], .running⟩ :=
  closed_program_interaction_safety callback_request_typed
    (trace_append callback_capture_response (internal_prefix execution [callbackSaved]))

/-- Actual entry records retain the complete body and consumer from the
supplied callback, including the consumer's distinct outer binder context. -/
theorem callback_actual_entry : ∃ plan,
    Step (.dynamicCall nestedLambda (.delay (.ret .unit))) (.lambdaEntry plan)
      plan.computation ∧
    plan.body = .handle forwardingHandler (.ret (.var 0)) ∧
    plan.consumer = .mk boolType boolType
      (.handle (.mk 73 boolType boolType (.cons (.ret (.inRight (.var 0))) .nil) .nil)
        (.ret (.var 0))) [] [] :=
  ⟨_, .callLambda, rfl, rfl⟩

def bottomOperation : OperationInstance := ⟨82, [], unitType, .bottom⟩
def bottomSaved : Saved := ⟨bottomOperation, .unit, .ret (.var 0)⟩

theorem bottom_request_typed : CompTyped emptyContext bottomSaved.request .bottom :=
  .request .unit (.ret (.var rfl))

theorem bottom_capture : Trace (initial bottomSaved.request)
    [.publish 0 bottomSaved] ⟨bottomSaved.request, [bottomSaved], .waiting 0⟩ :=
  .cons (.publish [] bottomSaved) True.intro (.refl _)

theorem bottom_capture_safe :
    StateTyped ⟨bottomSaved.request, [bottomSaved], .waiting 0⟩ .bottom ∧
    Progress ⟨bottomSaved.request, [bottomSaved], .waiting 0⟩ :=
  closed_program_interaction_safety bottom_request_typed bottom_capture

/-- Value-arm pending waits use their own actual propagation constructor. -/
def valueWaitSaved (h : Handler) (v : Value) (rest : ValueArms)
    (op : OperationInstance) (p : Value) (k : Comp) : Saved :=
  ⟨op, p, .waitValue (renameHandler Nat.succ h) (renameValue Nat.succ v)
    (renameValueArms Nat.succ rest) k⟩

theorem value_wait_capture (h : Handler) (v : Value) (rest : ValueArms)
    (op : OperationInstance) (p : Value) (k : Comp) :
    Trace (initial (.waitValue h v rest (.request op p k)))
      [.internal .silent, .publish 0 (valueWaitSaved h v rest op p k)]
      ⟨(valueWaitSaved h v rest op p k).request,
        [valueWaitSaved h v rest op p k], .waiting 0⟩ :=
  .cons (.internal .valueRequest) True.intro
    (.cons (.publish [] (valueWaitSaved h v rest op p k)) True.intro (.refl _))

theorem value_wait_saved_response_safe
    (typed : CompTyped emptyContext (.waitValue h v rest (.request op p k)) a)
    (responseTyped : ValueTyped emptyContext response op.responseType) :
    StateTyped ⟨(valueWaitSaved h v rest op p k).resume response,
      [valueWaitSaved h v rest op p k], .running⟩ a ∧
    Progress ⟨(valueWaitSaved h v rest op p k).resume response,
      [valueWaitSaved h v rest op p k], .running⟩ :=
  (finite_saved_response_safety (handle := 0) typed (value_wait_capture h v rest op p k)
    (by rfl) responseTyped).2

end YulangClosure.HigherOrder.Handler.Interaction
