import YulangClosure.HigherOrderSafety

namespace YulangClosure.HigherOrder.Interaction
open YulangClosure.HigherOrder
open YulangClosure.HigherOrder.Safety

/-! Candidate finite value-typing interaction semantics. The raw arena and
transitions contain no typing derivations. This is a research extension of the
accepted finite HigherOrder core, not a native implementation or effect-hygiene
model. In particular retaining a view occurrence is not freshening it. -/

structure Saved where
  operation : OperationInstance
  payload : Value
  continuation : Comp
  context : EvalContext

def Saved.request (s : Saved) : Comp :=
  s.context.plug (.request s.operation s.payload s.continuation)

def Saved.resume (s : Saved) (response : Value) : Comp :=
  s.context.plug (substComp (single response) s.continuation)

theorem plug_suspended (k : EvalContext) (suspended : Suspended m) :
    Suspended (k.plug m) := by
  induction k with
  | hole => exact suspended
  | bind k body ih => exact .bind ih
  | scope owner k ih => exact .scope ih
  | expose ev rv k ih => exact .expose ih

theorem saved_request_suspended (saved : Saved) : Suspended saved.request :=
  plug_suspended saved.context (.request _ _ _)

theorem publication_has_no_internal_step (saved : Saved) :
    ¬ Safety.Step saved.request event next :=
  suspended_no_step (saved_request_suspended saved)

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

/-- This invariant is derived at capture by inversion, never a raw premise. -/
def SavedTyped (saved : Saved) (result : Ty) : Prop :=
  ∃ localResult,
    ValueTyped emptyContext saved.payload saved.operation.payloadType ∧
    CompTyped (extend emptyContext saved.operation.responseType)
      saved.continuation localResult ∧
    ContextTyped emptyContext saved.context localResult result

theorem capture_typed {saved : Saved} (h : CompTyped emptyContext saved.request a) :
    SavedTyped saved a := by
  obtain ⟨b, hm, hk⟩ := context_inversion saved.context h
  cases hm with
  | request hp hb => exact ⟨b, hp, hb, hk⟩

theorem saved_request_typed (h : SavedTyped saved a) :
    CompTyped emptyContext saved.request a := by
  obtain ⟨b, hp, hb, hk⟩ := h
  exact plug_typed hk (.request hp hb)

theorem saved_resume_typed (h : SavedTyped saved a)
    (hr : ValueTyped emptyContext response saved.operation.responseType) :
    CompTyped emptyContext (saved.resume response) a := by
  obtain ⟨b, hp, hb, hk⟩ := h
  exact plug_typed hk (substitute_top hb hr)

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
  | internal (event : Safety.Event)
  | publish (handle : Nat) (saved : Saved)
  | response (handle : Nat) (operation : OperationInstance) (value : Value)

/-- Raw transitions are independent of typing, protocol, and preservation.
An external scheduler may select ANY existing handle, including an old handle
while another computation is running or waiting. Resume never removes entries. -/
inductive RawStep : State → Action → State → Prop where
  | internal : Safety.Step m e n →
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
Waiting records the actual published request, including its entire context. -/
inductive Progress : State → Prop where
  | returned (v arena) : Progress ⟨.ret v, arena, .running⟩
  | failed (k : EvalContext) (reason arena) :
      Progress ⟨k.plug (.fail reason), arena, .running⟩
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
      rcases closed_progress typed.currentTyped with returned | suspended | ⟨e, n, step⟩
      · cases returned
        exact .returned _ _
      · rcases suspended_decomposition suspended with
          ⟨k, reason, equal⟩ | ⟨k, op, payload, continuation, equal⟩
        · cases equal
          exact .failed _ _ _
        · cases equal
          exact .advance (.publish arena ⟨op, payload, continuation, k⟩) True.intro
      · exact .advance (.internal step) True.intro

/-- HO-INTERACTION-1: EVERY finite protocol-respecting prefix, all saved
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
  obtain ⟨b, payloadTyped, bodyTyped, contextTyped⟩ := hs
  exact ⟨instanceEq, payloadTyped, responseTyped,
    plug_typed contextTyped (substitute_top bodyTyped responseTyped)⟩

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
fresh handle yields that same record, including continuation and context. -/
theorem publication_association (arena : List Saved) (op payload continuation context) :
    lookup (arena ++ [⟨op, payload, continuation, context⟩]) arena.length =
      some ⟨op, payload, continuation, context⟩ := lookup_append_fresh _ _

theorem retained_outer_context (saved : Saved) (response : Value) :
    saved.resume response =
      saved.context.plug (substComp (single response) saved.continuation) := rfl

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

/-! Distinguishing constructions use actual raw capture and response rules. -/

def bottomOperation : OperationInstance := ⟨10, [], .base .unit, .bottom⟩
def bottomSaved : Saved := ⟨bottomOperation, .unit, .ret (.var 0), .hole⟩

theorem bottom_request_typed : CompTyped emptyContext bottomSaved.request .bottom :=
  .request .unit (.ret (.var rfl))

theorem bottom_wait_trace : Trace (initial bottomSaved.request) [.publish 0 bottomSaved]
    ⟨bottomSaved.request, [bottomSaved], .waiting 0⟩ :=
  .cons (.publish [] bottomSaved) True.intro (.refl _)

theorem bottom_wait_safety :
    StateTyped ⟨bottomSaved.request, [bottomSaved], .waiting 0⟩ .bottom ∧
    Progress ⟨bottomSaved.request, [bottomSaved], .waiting 0⟩ :=
  closed_program_interaction_safety bottom_request_typed bottom_wait_trace

theorem bottom_wait_no_response (operation : OperationInstance) (response : Value) :
    ¬ Protocol ⟨bottomSaved.request, [bottomSaved], .waiting 0⟩
      (.response 0 operation response) :=
  bottom_response_unavailable (saved := bottomSaved) rfl rfl


def boolOperation : OperationInstance := ⟨11, [], .base .unit, .base .bool⟩
def boolSaved : Saved := ⟨boolOperation, .unit, .ret (.var 0), .hole⟩

theorem bool_request_typed : CompTyped emptyContext boolSaved.request (.base .bool) :=
  .request .unit (.ret (.var rfl))

theorem two_distinct_responses :
    Value.bool false ≠ Value.bool true ∧
    Trace (initial boolSaved.request)
      [.publish 0 boolSaved,
       .response 0 boolOperation (.bool false), .response 0 boolOperation (.bool true)]
      ⟨.ret (.bool true), [boolSaved], .running⟩ := by
  constructor
  · intro impossible
    cases impossible
  · exact .cons (.publish [] boolSaved) True.intro
      (.cons (.response rfl) (response_protocol (saved := boolSaved) rfl ValueTyped.bool)
        (.cons (.response rfl) (response_protocol (saved := boolSaved) rfl ValueTyped.bool) (.refl _)))

theorem two_response_safety :
    StateTyped ⟨.ret (.bool true), [boolSaved], .running⟩ (.base .bool) ∧
    Progress ⟨.ret (.bool true), [boolSaved], .running⟩ :=
  closed_program_interaction_safety bool_request_typed two_distinct_responses.2

def nextRequestSaved : Saved :=
  ⟨boolOperation, .unit, .request boolOperation .unit (.ret (.var 0)), .hole⟩

theorem next_request_typed :
    CompTyped emptyContext nextRequestSaved.request (.base .bool) :=
  .request .unit (.request .unit (.ret (.var rfl)))

theorem new_request_after_resume :
    Trace (initial nextRequestSaved.request)
      [.publish 0 nextRequestSaved, .response 0 boolOperation (.bool false),
       .publish 1 boolSaved, .response 0 boolOperation (.bool true),
       .publish 2 boolSaved]
      ⟨boolSaved.request, [nextRequestSaved, boolSaved, boolSaved], .waiting 2⟩ :=
  .cons (.publish [] nextRequestSaved) True.intro
    (.cons (.response rfl) (response_protocol (saved := nextRequestSaved) rfl ValueTyped.bool)
      (.cons (.publish [nextRequestSaved] boolSaved) True.intro
        (.cons (.response rfl) (response_protocol (saved := nextRequestSaved) rfl ValueTyped.bool)
          (.cons (.publish [nextRequestSaved, boolSaved] boolSaved) True.intro (.refl _)))))

def identityConsumer : Adapter := .mk (.base .unit) (.base .unit) (.ret (.var 0)) [] []
def callableResponse : Value :=
  .lambda .value ⟨[], []⟩ (.base .unit) (.base .unit) (.base .unit)
    (.ret (.var 0)) identityConsumer

def callableOperation : OperationInstance :=
  ⟨12, [], .base .unit, .callable (.base .unit) (.base .unit)⟩

def callableSaved : Saved :=
  ⟨callableOperation, .unit, .dynamicCall (.var 0) (.delay (.ret .unit)), .hole⟩

theorem callable_response_typed :
    ValueTyped emptyContext callableResponse (.callable (.base .unit) (.base .unit)) :=
  .lambdaValue (.ret (.var rfl)) (.mk (.ret (.var rfl)))

theorem callable_request_typed :
    CompTyped emptyContext callableSaved.request (.base .unit) :=
  .request .unit (.dynamicCall (.var rfl) (.delay (.ret .unit)))

theorem callable_response_trace :
    Trace (initial callableSaved.request)
      [.publish 0 callableSaved, .response 0 callableOperation callableResponse]
      ⟨.dynamicCall callableResponse (.delay (.ret .unit)), [callableSaved], .running⟩ :=
  .cons (.publish [] callableSaved) True.intro
    (.cons (.response rfl) (response_protocol (saved := callableSaved) rfl callable_response_typed) (.refl _))

theorem callable_response_can_progress :
    Progress ⟨.dynamicCall callableResponse (.delay (.ret .unit)), [callableSaved], .running⟩ :=
  (closed_program_interaction_safety callable_request_typed callable_response_trace).2

/-- A nontrivial bind/scope/expose context survives verbatim. -/
def nestedSaved (ev rv : ViewOccurrence) : Saved :=
  ⟨boolOperation, .unit, .ret (.var 0),
    .expose ev rv (.scope 42 (.bind .hole (.ret (.var 0))))⟩

theorem nested_request_typed (ev rv : ViewOccurrence) :
    CompTyped emptyContext (nestedSaved ev rv).request (.base .bool) :=
  .expose (.scope (.bind (.request .unit (.ret (.var rfl))) (.ret (.var rfl))))

theorem nested_resume_equation (ev rv : ViewOccurrence) (b : Bool) :
    (nestedSaved ev rv).resume (.bool b) =
      .expose ev rv (.scope 42 (.bind (.ret (.bool b)) (.ret (.var 0)))) := rfl

/-- Same payload/response types do not make different operation identities match. -/
def wrongBoolOperation : OperationInstance := ⟨99, [], .base .unit, .base .bool⟩

theorem wrong_operation_example :
    ¬ Protocol ⟨boolSaved.request, [boolSaved], .waiting 0⟩
      (.response 0 wrongBoolOperation (.bool true)) := by
  apply wrong_instance_rejected (saved := boolSaved) rfl
  intro equal
  have impossible : (99 : Nat) = 11 := congrArg OperationInstance.operation equal
  cases impossible

end YulangClosure.HigherOrder.Interaction
