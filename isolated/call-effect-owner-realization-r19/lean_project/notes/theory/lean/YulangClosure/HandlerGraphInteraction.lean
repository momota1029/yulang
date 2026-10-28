import YulangClosure.HandlerGraphTransport

/-! Root request publication and finite external interaction in the combined
handler/graph machine. Typing of saved code follows from actual reachability. -/
namespace YulangClosure.HandlerGraph.Extension
open HigherOrder (Ty Context emptyContext extend OperationInstance)
variable {R T U : Type} {xi : R → Ty} {tau : T → Ty}

structure Saved (R : Type) where
  operation : OperationInstance
  payload : Value R Empty
  continuation : Comp R Empty

variable {s : Saved R}

/-- Only an actual ROOT request is publishable. Handler and wait propagation
must already have happened in the raw machine. -/
def Saved.suspended (s : Saved R) : Comp R Empty :=
  .request s.operation s.payload s.continuation

def Saved.resume (s : Saved R) (response : Value R Empty) : Comp R Empty :=
  substComp (single response) s.continuation

def SavedTyped (xi : R → Ty) (s : Saved R) (result : Ty) : Prop :=
  ValueTyped xi emptyTy emptyContext s.payload s.operation.payloadType ∧
    CompTyped xi emptyTy (extend emptyContext s.operation.responseType) s.continuation result

theorem capture_typed (s : Saved R)
    (h : CompTyped xi emptyTy emptyContext s.suspended result) : SavedTyped xi s result := by
  cases h with
  | request hp hk => exact ⟨hp, hk⟩

theorem saved_suspended_typed (h : SavedTyped xi s result) :
    CompTyped xi emptyTy emptyContext s.suspended result := .request h.1 h.2

theorem capture_reached {g : Graph R} (hg : WellTyped g xi)
    (initial : CompTyped xi emptyTy emptyContext m result)
    (steps : Prefix g m trace s.suspended) : SavedTyped xi s result :=
  capture_typed s (prefix_preservation hg steps initial)

def Saved.map (f : R → T) (s : Saved R) : Saved T :=
  ⟨s.operation, mapValue f s.payload, mapComp f s.continuation⟩

theorem saved_map_id (s : Saved R) : s.map id = s := by
  cases s
  simp only [Saved.map, mapValue_id, mapComp_id]

theorem saved_map_comp (f : R → T) (g : T → U) (s : Saved R) :
    (s.map f).map g = s.map (fun r => g (f r)) := by
  cases s
  simp only [Saved.map, mapValue_comp, mapComp_comp]

theorem saved_map_suspended (f : R → T) (s : Saved R) :
    (s.map f).suspended = mapComp f s.suspended := rfl

theorem saved_map_resume (f : R → T) (s : Saved R) (v : Value R Empty) :
    (s.map f).resume (mapValue f v) = mapComp f (s.resume v) := by
  simp only [Saved.resume, Saved.map, map_substitute_top]

theorem saved_map_typed (f : R → T) (types : ∀ r, tau (f r) = xi r)
    (h : SavedTyped xi s result) : SavedTyped tau (s.map f) result :=
  ⟨mapValue_typed h.1 f types, mapComp_typed h.2 f types⟩

theorem saved_resume_typed (h : SavedTyped xi s result)
    (response : Value R Empty)
    (hr : ValueTyped xi emptyTy emptyContext response s.operation.responseType) :
    CompTyped xi emptyTy emptyContext (s.resume response) result :=
  substitute_top h.2 hr

/-- Operation matching is full structural equality, never just the operation ID.
This raw interface rule does not assume response typing or preservation. -/
inductive Answer (s : Saved R) : OperationInstance → Value R Empty → Comp R Empty → Prop where
  | matched (operation : OperationInstance) (same : operation = s.operation) (response) :
      Answer s operation response (s.resume response)

theorem mismatched_instance_rejected (different : operation ≠ s.operation) :
    ¬ Answer s operation response next := by
  intro h
  cases h
  contradiction

theorem answer_typed (hs : SavedTyped xi s result)
    (hr : ValueTyped xi emptyTy emptyContext response operation.responseType)
    (answer : Answer s operation response next) :
    CompTyped xi emptyTy emptyContext next result := by
  cases answer
  subst_vars
  exact saved_resume_typed hs _ hr

/-- A raw matched answer commutes with reference transport. The full operation
instance is retained; response typing is not a premise of this equation. -/
theorem map_answer (f : R → T) (answer : Answer s operation response next) :
    Answer (s.map f) operation (mapValue f response) (mapComp f next) := by
  cases answer
  subst_vars
  simpa only [saved_map_resume] using
    (Answer.matched (s := s.map f) s.operation rfl (mapValue f response))

/-- Actual finite chains can change the reference sort at every extension.
The data contains concrete embeddings, without choosing any inhabitants. -/
inductive Chain (R : Type) (graph : Graph R) (xi : R → Ty) :
    (T : Type) → Graph T → (T → Ty) → Type 1 where
  | refl : Chain R graph xi R graph xi
  | snoc {T U : Type} {middle : Graph T} {tau : T → Ty} {last : Graph U} {ups : U → Ty} :
      Chain R graph xi T middle tau → Embedding middle tau last ups →
      Chain R graph xi U last ups

def Chain.embedding {g : Graph R} {xi : R → Ty} :
    {T : Type} → {h : Graph T} → {tau : T → Ty} →
      Chain R g xi T h tau → Embedding g xi h tau
  | _, _, _, .refl => .refl g xi
  | _, _, _, .snoc priorChain e => (Chain.embedding priorChain).trans e

theorem chain_old_nodes {g : Graph R} {h : Graph T}
    (chain : Chain R g xi T h tau) (r : R) :
    h (chain.embedding.refs r) = mapValue chain.embedding.refs (g r) :=
  chain.embedding.nodes r

theorem chain_injective {g : Graph R} {h : Graph T}
    (chain : Chain R g xi T h tau) : ∀ {r s}, chain.embedding.refs r = chain.embedding.refs s → r = s :=
  chain.embedding.injective

theorem chain_saved_typed {g : Graph R} {h : Graph T}
    (chain : Chain R g xi T h tau) (hs : SavedTyped xi s result) :
    SavedTyped tau (s.map chain.embedding.refs) result :=
  saved_map_typed _ chain.embedding.types hs

/-- Parent application for EVERY finite extension chain and EVERY new-world
response. The response can mention fresh references absent from the old graph. -/
theorem chain_resume_safety {g : Graph R} {h : Graph T}
    (chain : Chain R g xi T h tau)
    (captured : CompTyped xi emptyTy emptyContext s.suspended result)
    (finalTyped : WellTyped h tau)
    (finalGuard : GuardedValueGraph.Guarded (projectGraph h))
    (response : Value T Empty)
    (hr : ValueTyped tau emptyTy emptyContext response s.operation.responseType)
    (steps : Prefix h ((s.map chain.embedding.refs).resume response) trace last) :
    CompTyped tau emptyTy emptyContext last result ∧ CanProgress (graph := h) last :=
  finite_prefix_safety finalTyped finalGuard
    (saved_resume_typed (chain_saved_typed chain (capture_typed s captured)) response hr) steps

/-- Each response is quantified independently; the first execution does not
consume or mutate the captured record used by the second execution. -/
theorem repeated_responses {g : Graph R} {h : Graph T}
    (chain : Chain R g xi T h tau)
    (captured : CompTyped xi emptyTy emptyContext s.suspended result)
    (ht : WellTyped h tau) (guard : GuardedValueGraph.Guarded (projectGraph h))
    (one two : Value T Empty)
    (hOne : ValueTyped tau emptyTy emptyContext one s.operation.responseType)
    (hTwo : ValueTyped tau emptyTy emptyContext two s.operation.responseType)
    (first : Prefix h ((s.map chain.embedding.refs).resume one) t1 n1)
    (second : Prefix h ((s.map chain.embedding.refs).resume two) t2 n2) :
    (CompTyped tau emptyTy emptyContext n1 result ∧ CanProgress (graph := h) n1) ∧
    (CompTyped tau emptyTy emptyContext n2 result ∧ CanProgress (graph := h) n2) :=
  ⟨chain_resume_safety chain captured ht guard one hOne first,
    chain_resume_safety chain captured ht guard two hTwo second⟩

/-- The identity of the OLD saved continuation after a second extension is an
actual syntactic equation, not merely equality of result types. -/
theorem saved_after_second {g : Graph R} {h : Graph T} {k : Graph U} {ups : U → Ty}
    (chain : Chain R g xi T h tau) (extension : Embedding h tau k ups) (s : Saved R) :
    (s.map chain.embedding.refs).map extension.refs =
      s.map (Chain.snoc chain extension).embedding.refs :=
  saved_map_comp _ _ s

/-- Arbitrarily many independently chosen responses, including an empty family.
No response is required to be representable in the original reference sort. -/
theorem finite_response_family {g : Graph R} {h : Graph T}
    (chain : Chain R g xi T h tau)
    (captured : CompTyped xi emptyTy emptyContext s.suspended result)
    (ht : WellTyped h tau) (guard : GuardedValueGraph.Guarded (projectGraph h))
    (responses : Fin count → Value T Empty)
    (typed : ∀ i, ValueTyped tau emptyTy emptyContext (responses i) s.operation.responseType) :
    ∀ i trace last, Prefix h ((s.map chain.embedding.refs).resume (responses i)) trace last →
      CompTyped tau emptyTy emptyContext last result ∧ CanProgress (graph := h) last :=
  fun i _ _ steps => chain_resume_safety chain captured ht guard _ (typed i) steps

/-- A finite external interaction protocol over the ACTUAL graph machine.
Publication requires an actual ROOT request after actual propagation. Existing saved records
are immutable, all records transport on extension, and any stored record can be
resumed repeatedly. This is a research interface, not native scheduler authority.
Internal rules are exactly Step; external responses alone carry typing. -/
inductive Run (R : Type) (initialGraph : Graph R) (initialTypes : R → Ty)
    (initial : Comp R Empty) :
    (T : Type) → Graph T → (T → Ty) → Comp T Empty → List (Saved T) → Prop where
  | start : Run R initialGraph initialTypes initial R initialGraph initialTypes initial []
  | internal {T : Type} {g : Graph T} {tau : T → Ty}
      {current next : Comp T Empty} {event : Event T} {arena : List (Saved T)} :
      Run R initialGraph initialTypes initial T g tau current arena →
      Step g current event next →
      Run R initialGraph initialTypes initial T g tau next arena
  | publish {T : Type} {g : Graph T} {tau : T → Ty}
      {arena : List (Saved T)} (saved : Saved T) :
      Run R initialGraph initialTypes initial T g tau saved.suspended arena →
      Run R initialGraph initialTypes initial T g tau saved.suspended (saved :: arena)
  | extension {T U : Type} {g : Graph T} {tau : T → Ty} {h : Graph U} {ups : U → Ty}
      {current : Comp T Empty} {arena : List (Saved T)}
      (e : Embedding g tau h ups) :
      Run R initialGraph initialTypes initial T g tau current arena →
      WellTyped h ups →
      Run R initialGraph initialTypes initial U h ups (mapComp e.refs current)
        (arena.map (Saved.map e.refs))
  | answer {T : Type} {g : Graph T} {tau : T → Ty} {saved : Saved T}
      {current next : Comp T Empty} {arena : List (Saved T)}
      {operation : OperationInstance} {response : Value T Empty} :
      Run R initialGraph initialTypes initial T g tau current arena →
      saved ∈ arena → Answer saved operation response next →
      ValueTyped tau emptyTy emptyContext response operation.responseType →
      Run R initialGraph initialTypes initial T g tau next arena

/-- Saved-record typing is established only by actual publication, then retained
by immutable transport and reuse. No saved typing oracle is an input to Run. -/
theorem run_invariant {g : Graph R} {h : Graph T}
    (hg : WellTyped g xi) (initial : CompTyped xi emptyTy emptyContext m result)
    (run : Run R g xi m T h tau current arena) :
    WellTyped h tau ∧ CompTyped tau emptyTy emptyContext current result ∧
      ∀ s, s ∈ arena → SavedTyped tau s result := by
  induction run with
  | start =>
      refine ⟨hg, initial, ?_⟩
      intro s hs
      cases hs
  | internal prior step ih =>
      exact ⟨ih.1, preservation ih.1 step ih.2.1, ih.2.2⟩
  | publish saved prior ih =>
      refine ⟨ih.1, ih.2.1, ?_⟩
      intro s hs
      rcases List.mem_cons.mp hs with eq | old
      · subst s
        exact capture_typed saved ih.2.1
      · exact ih.2.2 s old
  | extension e prior typed ih =>
      refine ⟨typed, mapComp_typed ih.2.1 e.refs e.types, ?_⟩
      intro s hs
      obtain ⟨old, member, eq⟩ := List.mem_map.mp hs
      subst s
      exact saved_map_typed e.refs e.types (ih.2.2 old member)
  | answer prior member matched typed ih =>
      exact ⟨ih.1, answer_typed (ih.2.2 _ member) typed matched, ih.2.2⟩

/-- Finite internal prefixes after arbitrary interaction retain the original
result and every saved typing derivation. Progress uses the actual final guard. -/
theorem run_prefix_safety {g : Graph R} {h : Graph T}
    (hg : WellTyped g xi) (initial : CompTyped xi emptyTy emptyContext m result)
    (run : Run R g xi m T h tau current arena)
    (guard : GuardedValueGraph.Guarded (projectGraph h))
    (steps : Prefix h current trace last) :
    CompTyped tau emptyTy emptyContext last result ∧ CanProgress h last ∧
      (∀ s, s ∈ arena → SavedTyped tau s result) := by
  obtain ⟨typedGraph, typedCurrent, typedArena⟩ := run_invariant hg initial run
  have typedLast := prefix_preservation typedGraph steps typedCurrent
  exact ⟨typedLast, closed_progress typedGraph guard typedLast, typedArena⟩

/-- The four paper-style outcomes are actual outer syntax or an actual raw
step. A request underneath a handler or attempt is not a terminal alternative. -/
theorem run_prefix_four {g : Graph R} {h : Graph T}
    (hg : WellTyped g xi) (initial : CompTyped xi emptyTy emptyContext m result)
    (run : Run R g xi m T h tau current arena)
    (guard : GuardedValueGraph.Guarded (projectGraph h))
    (steps : Prefix h current trace last) :
    (∃ v, last = .ret v) ∨ (∃ op p k, last = .request op p k) ∨
      (∃ reason, last = .fail reason) ∨ ∃ event next, Step h last event next := by
  rcases (run_prefix_safety hg initial run guard steps).2.1 with terminal | step
  · cases terminal with
    | returned v => exact .inl ⟨v, rfl⟩
    | requested op p k => exact .inr (.inl ⟨op, p, k, rfl⟩)
    | failed reason => exact .inr (.inr (.inl ⟨reason, rfl⟩))
  · exact .inr (.inr (.inr step))

/-- Every final graph has a finite chain back to the initial graph. Internal
execution, publication, and answering do not overwrite nodes. -/
theorem run_chain {g : Graph R} {h : Graph T}
    (run : Run R g xi m T h tau current arena) :
    Nonempty (Chain R g xi T h tau) := by
  induction run with
  | start => exact ⟨.refl⟩
  | internal _ _ ih => exact ih
  | publish _ _ ih => exact ih
  | extension e _ _ ih =>
      obtain ⟨chain⟩ := ih
      exact ⟨.snoc chain e⟩
  | answer _ _ _ _ ih => exact ih

/-- Provenance is established without saved typing assumptions. Each arena
entry comes from a reached ROOT request on a run with this initial state, followed
by a concrete finite chain of immutable graph embeddings. -/
theorem run_saved_provenance {g : Graph R} {h : Graph T}
    (run : Run R g xi m T h tau current arena) :
    ∀ saved, saved ∈ arena →
      ∃ (V : Type) (originGraph : Graph V) (originTypes : V → Ty)
        (origin : Saved V) (originArena : List (Saved V)),
        Run R g xi m V originGraph originTypes origin.suspended originArena ∧
        ∃ chain : Chain V originGraph originTypes T h tau,
          saved = origin.map chain.embedding.refs := by
  induction run with
  | start => intro saved member; cases member
  | internal _ _ ih => exact ih
  | publish published prior ih =>
      intro saved member
      rcases List.mem_cons.mp member with eq | old
      · subst saved
        exact ⟨_, _, _, published, _, prior, .refl, (saved_map_id published).symm⟩
      · exact ih saved old
  | extension e _ _ ih =>
      intro saved member
      obtain ⟨old, oldMember, mappedEq⟩ := List.mem_map.mp member
      obtain ⟨V, og, ot, origin, oa, reached, chain, originEq⟩ := ih old oldMember
      refine ⟨V, og, ot, origin, oa, reached, .snoc chain e, ?_⟩
      calc
        saved = old.map e.refs := mappedEq.symm
        _ = (origin.map chain.embedding.refs).map e.refs := congrArg (fun s => s.map e.refs) originEq
        _ = origin.map (Chain.snoc chain e).embedding.refs :=
          saved_map_comp chain.embedding.refs e.refs origin
  | answer _ _ _ _ ih => exact ih

/-- Consume provenance at the parent: the original saved typing derivation
is obtained from its reached root request, before transporting it to the final
world. Neither origin typing nor saved typing is supplied as an oracle. -/
theorem run_saved_origin_typed {g : Graph R} {h : Graph T}
    (hg : WellTyped g xi) (initial : CompTyped xi emptyTy emptyContext m result)
    (run : Run R g xi m T h tau current arena) (saved : Saved T) (member : saved ∈ arena) :
    ∃ (V : Type) (originGraph : Graph V) (originTypes : V → Ty)
      (origin : Saved V) (originArena : List (Saved V)),
      Run R g xi m V originGraph originTypes origin.suspended (origin :: originArena) ∧
      SavedTyped originTypes origin result ∧
      ∃ chain : Chain V originGraph originTypes T h tau,
        saved = origin.map chain.embedding.refs := by
  obtain ⟨V, og, ot, origin, oa, reached, chain, eq⟩ := run_saved_provenance run saved member
  have typed := (run_invariant hg initial reached).2.1
  exact ⟨V, og, ot, origin, oa, .publish origin reached,
    capture_typed origin typed, chain, eq⟩

/-- An arbitrary old entry remains available after both responses. Responses
are independently typed in the current graph; no old-world encoding is needed. -/
theorem run_answer_twice {g : Graph R} {h : Graph T}
    (run : Run R g xi m T h tau current arena) (s : Saved T) (member : s ∈ arena)
    (one two : Value T Empty)
    (hOne : ValueTyped tau emptyTy emptyContext one s.operation.responseType)
    (hTwo : ValueTyped tau emptyTy emptyContext two s.operation.responseType) :
    Run R g xi m T h tau (s.resume one) arena ∧
    Run R g xi m T h tau (s.resume two) arena := by
  have first := Run.answer run member (.matched s.operation rfl one) hOne
  exact ⟨first, Run.answer first member (.matched s.operation rfl two) hTwo⟩

/-- Apply the invariant to EVERY saved entry and an independently chosen finite
family of responses, not only the latest published request. -/
theorem run_all_saved_responses {g : Graph R} {h : Graph T}
    (hg : WellTyped g xi) (initial : CompTyped xi emptyTy emptyContext m result)
    (run : Run R g xi m T h tau current arena)
    (guard : GuardedValueGraph.Guarded (projectGraph h))
    (s : Saved T) (member : s ∈ arena)
    (responses : Fin count → Value T Empty)
    (typed : ∀ i, ValueTyped tau emptyTy emptyContext (responses i) s.operation.responseType) :
    ∀ i trace last, Prefix h (s.resume (responses i)) trace last →
      CompTyped tau emptyTy emptyContext last result ∧ CanProgress h last := by
  obtain ⟨typedGraph, _, typedArena⟩ := run_invariant hg initial run
  intro i trace last steps
  exact finite_prefix_safety typedGraph guard
    (saved_resume_typed (typedArena s member) _ (typed i)) steps

/-- Root publication cannot reinterpret a request underneath any handler. -/
theorem handled_request_not_root (handler : Handler R Empty) (op : OperationInstance)
    (p : Value R Empty) (k : Comp R Empty) (saved : Saved R) :
    Comp.handle handler (.request op p k) ≠ saved.suspended := by
  intro eq
  cases eq

/-- Likewise an outstanding attempt must propagate its request first. -/
theorem waiting_request_not_root (handler : Handler R Empty) (v : Value R Empty)
    (arms : ValueArms R Empty) (op : OperationInstance) (p : Value R Empty)
    (k : Comp R Empty) (saved : Saved R) :
    Comp.waitValue handler v arms (.request op p k) ≠ saved.suspended := by
  intro eq
  cases eq

theorem operation_waiting_request_not_root (handler : Handler R Empty)
    (op nextOp : OperationInstance) (p nextP : Value R Empty)
    (k nextK : Comp R Empty) (arms : OperationArms R Empty) (saved : Saved R) :
    Comp.waitOperation handler op p k arms (.request nextOp nextP nextK) ≠ saved.suspended := by
  intro eq
  cases eq

/-- Internal prefixes are actual protocol segments, not assumed typed updates. -/
theorem run_internal_prefix {g : Graph R} {h : Graph T}
    (run : Run R g xi m T h tau current arena) (steps : Prefix h current trace last) :
    Run R g xi m T h tau last arena := by
  revert run
  induction steps with
  | refl => intro run; exact run
  | cons step _ ih => intro run; exact ih (.internal run step)

namespace Demo
abbrev unitTy : Ty := .base .unit
abbrev callableTy : Ty := .callable unitTy unitTy
def receipt : HigherOrder.ReceiptTemplate := ⟨[], []⟩
def operation : OperationInstance := ⟨73, [callableTy], unitTy, callableTy⟩
def laterOperation : OperationInstance := ⟨74, [unitTy], unitTy, unitTy⟩
def old : Graph (Fin 1) := fun _ => .unit
def oldTypes : Fin 1 → Ty := fun _ => unitTy

theorem old_typed : WellTyped old oldTypes := fun _ => .unit

/-- The continuation genuinely calls its supplied higher-order response. -/
def saved : Saved (Fin 1) :=
  ⟨operation, .ref 0, .dynamicCall (.var 0) (.delay (.ret (.ref 0)))⟩

theorem saved_actual_request :
    CompTyped oldTypes emptyTy emptyContext saved.suspended unitTy :=
  .request (.ref 0) (.dynamicCall (.var rfl) (.delay (.ret (.ref 0))))

def identityAdapter {R : Type} : Adapter R Empty :=
  .mk unitTy unitTy (.ret (.var 0)) [] []

/-- The request occurs INSIDE an actual value-arm attempt. Its response binder
is zero; the value-arm binder and the callback binder remain outside it. -/
def requestHandler {R : Type} : Handler R Empty :=
  .mk 91 unitTy unitTy
    (.cons (.request laterOperation .unit (.ret (.inRight (.var 0)))) .nil) .nil

theorem requestHandler_typed {R : Type} {xi : R → Ty} {env : Context} :
    HandlerTyped xi emptyTy env requestHandler unitTy unitTy :=
  .mk (.cons (.request .unit (.ret (.inRight (.var rfl)))) .nil) .nil

def callback {R : Type} : Value R Empty :=
  .lambda .computation receipt unitTy unitTy unitTy
    (.handle requestHandler (.ret .unit)) identityAdapter

theorem callback_typed {R : Type} {xi : R → Ty} {env : Context} :
    ValueTyped xi emptyTy env callback callableTy :=
  .lambdaComputation (.handle requestHandler_typed (.ret .unit)) (.mk (.ret (.var rfl)))

abbrev First := Sum (Fin 1) (Fin 1)
def first : Graph First
  | .inl _ => .unit
  | .inr _ => callback
def firstTypes : First → Ty
  | .inl _ => unitTy
  | .inr _ => callableTy

def firstEmbedding : Embedding old oldTypes first firstTypes where
  refs := Sum.inl
  injective := fun {_ _} h => Sum.inl.inj h
  types := fun _ => rfl
  nodes := fun _ => rfl

def firstChain : Chain (Fin 1) old oldTypes First first firstTypes :=
  .snoc .refl firstEmbedding

theorem first_typed : WellTyped first firstTypes := by
  intro r
  cases r with
  | inl _ => exact .unit
  | inr _ => exact callback_typed

def firstGuard : GuardedValueGraph.Guarded (projectGraph first) where
  rank := fun _ => 0
  ceiling := 1
  bound := fun _ => Nat.zero_lt_succ 0
  decrease := by
    intro r s edge
    cases r <;> cases edge

def responseOne : Value First Empty := .ref (.inr 0)
def responseTwo : Value First Empty := .wrap responseOne identityAdapter identityAdapter

theorem responseOne_typed : ValueTyped firstTypes emptyTy emptyContext responseOne callableTy := .ref _
theorem responseTwo_typed : ValueTyped firstTypes emptyTy emptyContext responseTwo callableTy :=
  .wrap responseOne_typed (.mk (.ret (.var rfl))) (.mk (.ret (.var rfl)))
theorem responses_distinct : responseOne ≠ responseTwo := by intro eq; cases eq

def carrier : Value First Empty := .delay (.ret (.ref (.inl 0)))
def callbackPlan : LambdaEntryPlan First :=
  ⟨.computation, receipt, unitTy, unitTy, unitTy,
    .handle requestHandler (.ret .unit), identityAdapter, carrier⟩

def laterSaved : Saved First :=
  ⟨laterOperation, .unit,
    .bind (.waitValue requestHandler .unit .nil (.ret (.inRight (.var 0)))) (.ret (.var 0))⟩

/-- Actual lookup, lambda entry, handler dispatch, arm attempt, wait propagation,
and bind propagation reach the next publishable ROOT request. -/
theorem fresh_response_reaches_request :
    Prefix first ((saved.map Sum.inl).resume responseOne)
      [.lookup (.inr 0), .lambdaEntry callbackPlan, .silent, .silent, .silent, .silent]
      laterSaved.suspended :=
  .cons .callRef
    (.cons .callLambda
      (.cons (.bind .handleReturn)
        (.cons (.bind .valueCons)
          (.cons (.bind .valueRequest)
            (.cons .bindRequest (.refl _))))))

theorem later_capture_derived : SavedTyped firstTypes laterSaved unitTy :=
  capture_reached first_typed
    (saved_resume_typed (saved_map_typed Sum.inl (fun _ => rfl)
      (capture_typed saved saved_actual_request)) responseOne responseOne_typed)
    fresh_response_reaches_request

theorem two_responses_safe
    (one : Prefix first ((saved.map Sum.inl).resume responseOne) t1 n1)
    (two : Prefix first ((saved.map Sum.inl).resume responseTwo) t2 n2) :
    (CompTyped firstTypes emptyTy emptyContext n1 unitTy ∧ CanProgress first n1) ∧
    (CompTyped firstTypes emptyTy emptyContext n2 unitTy ∧ CanProgress first n2) :=
  repeated_responses firstChain saved_actual_request first_typed firstGuard
    responseOne responseTwo responseOne_typed responseTwo_typed one two

theorem first_interaction :
    Run (Fin 1) old oldTypes saved.suspended First first firstTypes
      ((saved.map Sum.inl).resume responseOne) [saved.map Sum.inl] := by
  apply Run.answer (saved := saved.map Sum.inl)
  · exact .extension firstEmbedding (.publish saved .start) first_typed
  · exact List.mem_cons.mpr (.inl rfl)
  · exact .matched operation rfl responseOne
  · exact responseOne_typed

theorem later_publication :
    Run (Fin 1) old oldTypes saved.suspended First first firstTypes
      laterSaved.suspended [laterSaved, saved.map Sum.inl] :=
  .publish laterSaved (run_internal_prefix first_interaction fresh_response_reaches_request)

abbrev Second := Sum First (Fin 1)
def second : Graph Second
  | .inl r => mapValue Sum.inl (first r)
  | .inr _ => .delay (.ret (.ref (.inl (.inr 0))))
def secondTypes : Second → Ty
  | .inl r => firstTypes r
  | .inr _ => .thunk callableTy

def secondEmbedding : Embedding first firstTypes second secondTypes where
  refs := Sum.inl
  injective := fun {_ _} h => Sum.inl.inj h
  types := fun _ => rfl
  nodes := fun _ => rfl

def secondChain : Chain (Fin 1) old oldTypes Second second secondTypes :=
  .snoc firstChain secondEmbedding

theorem second_typed : WellTyped second secondTypes := by
  intro r
  cases r with
  | inl r => exact mapValue_typed (first_typed r) Sum.inl (fun _ => rfl)
  | inr _ => exact .delay (.ret (.ref _))

def secondGuard : GuardedValueGraph.Guarded (projectGraph second) where
  rank := fun _ => 0
  ceiling := 1
  bound := fun _ => Nat.zero_lt_succ 0
  decrease := by
    intro r s edge
    cases r with
    | inl r => cases r <;> cases edge
    | inr _ => cases edge

/-- This independently typed response reads the newly allocated delayed node
in its body, then calls the callback obtained there with its own carrier. -/
def secondResponse : Value Second Empty :=
  .lambda .computation receipt unitTy unitTy unitTy
    (.bind (.force (.ref (.inr 0))) (.dynamicCall (.var 0) (.var 1))) identityAdapter

theorem secondResponse_typed :
    ValueTyped secondTypes emptyTy emptyContext secondResponse callableTy :=
  .lambdaComputation
    (.bind (.force (.ref _)) (.dynamicCall (.var rfl) (.var rfl)))
    (.mk (.ret (.var rfl)))

def secondArena : List (Saved Second) :=
  [laterSaved.map Sum.inl, saved.map secondChain.embedding.refs]

theorem second_extension :
    Run (Fin 1) old oldTypes saved.suspended Second second secondTypes
      (mapComp Sum.inl laterSaved.suspended) secondArena := by
  exact Run.extension secondEmbedding later_publication second_typed

/-- The original entry is now the SECOND arena entry, and remains reusable. -/
theorem second_interaction :
    Run (Fin 1) old oldTypes saved.suspended Second second secondTypes
      ((saved.map secondChain.embedding.refs).resume secondResponse) secondArena := by
  apply Run.answer second_extension
  · exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))
  · exact .matched operation rfl secondResponse
  · exact secondResponse_typed

theorem old_after_second_safe
    (steps : Prefix second ((saved.map secondChain.embedding.refs).resume secondResponse) trace last) :
    CompTyped secondTypes emptyTy emptyContext last unitTy ∧ CanProgress second last :=
  chain_resume_safety secondChain saved_actual_request second_typed secondGuard
    secondResponse secondResponse_typed steps

/-- Every stored continuation is typed after the concrete interleaving. -/
theorem concrete_run_safe
    (steps : Prefix second ((saved.map secondChain.embedding.refs).resume secondResponse) trace last) :
    CompTyped secondTypes emptyTy emptyContext last unitTy ∧ CanProgress second last ∧
      (∀ s, s ∈ secondArena → SavedTyped secondTypes s unitTy) :=
  run_prefix_safety old_typed saved_actual_request second_interaction secondGuard steps

/-- Same ID and endpoints are insufficient when the ordered type arguments differ. -/
def wrongInstance : OperationInstance := ⟨73, [], unitTy, callableTy⟩
theorem wrongInstance_distinct : wrongInstance ≠ operation := by
  intro h
  have args := congrArg OperationInstance.typeArguments h
  cases args

theorem wrongInstance_cannot_resume :
    ¬ Answer (saved.map Sum.inl) wrongInstance responseOne next :=
  mismatched_instance_rejected wrongInstance_distinct

theorem old_fresh_separate (r : Fin 1) (s : Fin 1) :
    firstEmbedding.refs r ≠ Sum.inr s := by intro eq; cases eq

theorem overwrite_unit_rejected (e : Embedding old oldTypes first firstTypes)
    (bad : first (e.refs 0) = callback) : False := by
  have equation := e.nodes 0
  rw [bad] at equation
  change callback = Value.unit at equation
  cases equation

end Demo
end YulangClosure.HandlerGraph.Extension
