import YulangClosure.GraphExtensionTransport

/-! Actual saved graph requests through finite heterogeneous immutable extensions.
Research candidate: no native cell/store or handler correspondence is assumed. -/
namespace YulangClosure.HigherOrderGraph.Extension
open HigherOrder (Ty Context emptyContext extend OperationInstance)
open Safety
variable {R T U : Type} {xi : R → Ty} {tau : T → Ty}

structure Saved (R : Type) where
  operation : OperationInstance
  payload : Value R Empty
  continuation : Comp R Empty
  context : EvalContext R

variable {s : Saved R}

def Saved.suspended (s : Saved R) : Comp R Empty :=
  s.context.plug (.request s.operation s.payload s.continuation)

def Saved.resume (s : Saved R) (response : Value R Empty) : Comp R Empty :=
  s.context.plug (substComp (single response) s.continuation)

/-- The internal result type is existential; the full operation determines the
response binder. This predicate is derived from the actual request below. -/
def SavedTyped (xi : R → Ty) (s : Saved R) (result : Ty) : Prop :=
  ∃ bodyResult, ValueTyped xi emptyTy emptyContext s.payload s.operation.payloadType ∧
    CompTyped xi emptyTy (extend emptyContext s.operation.responseType) s.continuation bodyResult ∧
    ContextTyped xi emptyContext s.context bodyResult result

theorem capture_typed (s : Saved R)
    (h : CompTyped xi emptyTy emptyContext s.suspended result) : SavedTyped xi s result :=
  request_context_typing s.context h

theorem saved_suspended_typed (h : SavedTyped xi s result) :
    CompTyped xi emptyTy emptyContext s.suspended result := by
  obtain ⟨b, hp, hc, hk⟩ := h
  exact plug_typed hk (.request hp hc)

/-- A real reached request supplies every saved typing premise. -/
theorem capture_reached {g : Graph R} (hg : WellTyped g xi)
    (initial : CompTyped xi emptyTy emptyContext m result)
    (steps : Steps g m trace s.suspended) : SavedTyped xi s result :=
  capture_typed s (trace_preservation hg steps initial)

theorem capture_decomposition {m : Comp R Empty}
    (h : CompTyped xi emptyTy emptyContext m result) (request : Requested m) :
    ∃ s : Saved R, m = s.suspended ∧ SavedTyped xi s result := by
  obtain ⟨k, op, payload, continuation, eq⟩ := request
  refine ⟨⟨op, payload, continuation, k⟩, eq, ?_⟩
  apply capture_typed _
  change CompTyped xi emptyTy emptyContext (k.plug (.request op payload continuation)) result
  rw [← eq]
  exact h

def Saved.map (f : R → T) (s : Saved R) : Saved T :=
  ⟨s.operation, mapValue f s.payload, mapComp f s.continuation, mapContext f s.context⟩

theorem saved_map_id (s : Saved R) : s.map id = s := by
  cases s
  simp only [Saved.map, mapValue_id, mapComp_id, mapContext_id]

theorem saved_map_comp (f : R → T) (g : T → U) (s : Saved R) :
    (s.map f).map g = s.map (fun r => g (f r)) := by
  cases s
  simp only [Saved.map, mapValue_comp, mapComp_comp, mapContext_comp]

theorem saved_map_suspended (f : R → T) (s : Saved R) :
    (s.map f).suspended = mapComp f s.suspended := by
  simp only [Saved.suspended, Saved.map, map_plug, mapComp]

theorem saved_map_resume (f : R → T) (s : Saved R) (v : Value R Empty) :
    (s.map f).resume (mapValue f v) = mapComp f (s.resume v) := by
  simp only [Saved.resume, Saved.map, map_plug, map_substitute_top]

theorem saved_map_typed (f : R → T) (types : ∀ r, tau (f r) = xi r)
    (h : SavedTyped xi s result) : SavedTyped tau (s.map f) result := by
  obtain ⟨b, hp, hc, hk⟩ := h
  exact ⟨b, mapValue_typed hp f types, mapComp_typed hc f types,
    mapContext_typed f types hk⟩

theorem saved_resume_typed (h : SavedTyped xi s result)
    (response : Value R Empty)
    (hr : ValueTyped xi emptyTy emptyContext response s.operation.responseType) :
    CompTyped xi emptyTy emptyContext (s.resume response) result := by
  obtain ⟨b, hp, hc, hk⟩ := h
  exact plug_typed hk (substitute_top hc hr)

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
    (steps : Steps h ((s.map chain.embedding.refs).resume response) trace last) :
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
    (first : Steps h ((s.map chain.embedding.refs).resume one) t1 n1)
    (second : Steps h ((s.map chain.embedding.refs).resume two) t2 n2) :
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

/-- Allocation supplies final typing and guard, as well as exact immutable old
nodes. Fresh source RHS derivations and the finite cycle criterion are consumed. -/
theorem source_allocation_resume {g : Graph R} {nu : Fin n → Ty}
    (hg : WellTyped g xi) (guard : GuardedValueGraph.Guarded (projectGraph g))
    (s : Saved R) (captured : CompTyped xi emptyTy emptyContext s.suspended result)
    (rhs : Fin n → HigherOrder.Value)
    (hrhs : ∀ i, HigherOrder.ValueTyped (sourceContext nu env) (rhs i) (nu i))
    (hcapture : CapturesTyped xi env capture)
    (hcycle : FreshNoCycle (sourceFresh capture rhs))
    (response : Value (Sum R (Fin n)) Empty)
    (hr : ValueTyped (joinTy xi nu) emptyTy emptyContext response s.operation.responseType)
    (steps : Steps (allocate g (sourceFresh capture rhs))
      ((s.map Sum.inl).resume response) trace last) :
    CompTyped (joinTy xi nu) emptyTy emptyContext last result ∧
      CanProgress (graph := allocate g (sourceFresh capture rhs)) last := by
  have ht := allocate_typed hg (sourceFresh capture rhs)
    (fun i => sourceCloseValue_typed (hrhs i) hcapture)
  have hg' := allocationGuard guard (sourceFresh capture rhs) hcycle
  exact finite_prefix_safety ht hg'
    (saved_resume_typed (saved_map_typed Sum.inl (fun _ => rfl)
      (capture_typed s captured)) response hr) steps

/-- Arbitrarily many independently chosen responses, including an empty family.
No response is required to be representable in the original reference sort. -/
theorem finite_response_family {g : Graph R} {h : Graph T}
    (chain : Chain R g xi T h tau)
    (captured : CompTyped xi emptyTy emptyContext s.suspended result)
    (ht : WellTyped h tau) (guard : GuardedValueGraph.Guarded (projectGraph h))
    (responses : Fin count → Value T Empty)
    (typed : ∀ i, ValueTyped tau emptyTy emptyContext (responses i) s.operation.responseType) :
    ∀ i trace last, Steps h ((s.map chain.embedding.refs).resume (responses i)) trace last →
      CompTyped tau emptyTy emptyContext last result ∧ CanProgress (graph := h) last :=
  fun i _ _ steps => chain_resume_safety chain captured ht guard _ (typed i) steps

/-- Four explicit outcomes at every final prefix; graph suspension decomposes
into a request or failure in its actual finite evaluation context. -/
theorem chain_resume_four {g : Graph R} {h : Graph T}
    (chain : Chain R g xi T h tau)
    (captured : CompTyped xi emptyTy emptyContext s.suspended result)
    (ht : WellTyped h tau) (guard : GuardedValueGraph.Guarded (projectGraph h))
    (response : Value T Empty)
    (hr : ValueTyped tau emptyTy emptyContext response s.operation.responseType)
    (steps : Steps h ((s.map chain.embedding.refs).resume response) trace last) :
    Returned last ∨ Requested last ∨ Failed last ∨ ∃ event next, Step h last event next :=
  progress_four ht guard (chain_resume_safety chain captured ht guard response hr steps).1

/-- A finite external interaction protocol over the ACTUAL graph machine.
Publication requires an actual context-decomposed request. Existing saved records
are immutable, all records transport on extension, and any stored record can be
resumed repeatedly. This is a research interface, not native scheduler authority.
Internal rules are exactly Safety.Step; external responses alone carry typing. -/
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

/-- Parent safety induction for arbitrary finite INTERLEAVINGS of internal
steps, capture, extension and repeated responses. Every final internal prefix
and every stored old continuation retains the original overall result type. -/
theorem run_prefix_safety {g : Graph R} {h : Graph T}
    (hg : WellTyped g xi) (initial : CompTyped xi emptyTy emptyContext m result)
    (run : Run R g xi m T h tau current arena)
    (guard : GuardedValueGraph.Guarded (projectGraph h))
    (steps : Steps h current trace last) :
    CompTyped tau emptyTy emptyContext last result ∧
      (Returned last ∨ Requested last ∨ Failed last ∨ ∃ event next, Step h last event next) ∧
      (∀ s, s ∈ arena → SavedTyped tau s result) := by
  obtain ⟨typedGraph, typedCurrent, typedArena⟩ := run_invariant hg initial run
  have typedLast := trace_preservation typedGraph steps typedCurrent
  exact ⟨typedLast, progress_four typedGraph guard typedLast, typedArena⟩

namespace Demo
abbrev unitTy : Ty := .base .unit
abbrev callableTy : Ty := .callable unitTy unitTy
def receipt : HigherOrder.ReceiptTemplate := ⟨[], []⟩
def operation : OperationInstance := ⟨73, [callableTy], unitTy, callableTy⟩
def delayedOperation : OperationInstance := ⟨74, [callableTy], unitTy, .thunk callableTy⟩
def old : Graph (Fin 1) := fun _ => .unit
def oldTypes : Fin 1 → Ty := fun _ => unitTy

theorem old_typed : WellTyped old oldTypes := fun _ => .unit

def oldGuard : GuardedValueGraph.Guarded (projectGraph old) :=
  GuardedValueGraph.FiniteDecision.guardOfNoCycle _
    (GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl))

/-- The old request retains an old reference inside delayed argument code and
an independent bind/scope context outside its response continuation. -/
def saved : Saved (Fin 1) :=
  ⟨operation, .ref 0,
    .dynamicCall (.var 0) (.delay (.ret (.ref 0))),
    .bind (.scope 17 .hole) (.ret (.var 0))⟩

theorem saved_actual_request :
    CompTyped oldTypes emptyTy emptyContext saved.suspended unitTy :=
  .bind (.scope (.request (.ref 0)
    (.dynamicCall (.var rfl) (.delay (.ret (.ref 0)))))) (.ret (.var rfl))

theorem saved_capture : SavedTyped oldTypes saved unitTy :=
  capture_reached old_typed saved_actual_request (.refl _)

/-- A real source lambda and result consumer, with distinct binder scopes. -/
def callbackRhs : HigherOrder.Value :=
  .lambda .value receipt unitTy unitTy unitTy (.ret (.var 0))
    (.mk unitTy unitTy (.bind (.ret .unit) (.ret (.var 1))) [] [])
def callbackTypes : Fin 1 → Ty := fun _ => callableTy
def emptyCapture : Nat → Value (Fin 1) Empty := fun _ => .ref 0

theorem emptyCapture_typed : CapturesTyped oldTypes emptyContext emptyCapture := by
  intro i a h
  cases h

theorem callbackRhs_typed :
    HigherOrder.ValueTyped (sourceContext callbackTypes emptyContext) callbackRhs callableTy :=
  .lambdaValue (.ret (.var rfl)) (.mk (.bind (.ret .unit) (.ret (.var rfl))))

def freshOne := sourceFresh emptyCapture (fun _ : Fin 1 => callbackRhs)
abbrev First := Sum (Fin 1) (Fin 1)
def first : Graph First := allocate old freshOne
def firstTypes : First → Ty := joinTy oldTypes callbackTypes

theorem freshOne_equation (i : Fin 1) : freshOne i =
    .lambda .value receipt unitTy unitTy unitTy (.ret (.var 0))
      (.mk unitTy unitTy (.bind (.ret .unit) (.ret (.var 1))) [] []) := rfl

theorem freshOne_noCycle : FreshNoCycle freshOne :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

theorem first_typed : WellTyped first firstTypes :=
  allocate_typed old_typed freshOne
    (fun _ => sourceCloseValue_typed callbackRhs_typed emptyCapture_typed)

def firstGuard : GuardedValueGraph.Guarded (projectGraph first) :=
  allocationGuard oldGuard freshOne freshOne_noCycle

def firstChain : Chain (Fin 1) old oldTypes First first firstTypes :=
  .snoc .refl (allocationEmbedding old oldTypes callbackTypes freshOne)

def identityAdapter {R : Type} : Adapter R Empty :=
  .mk unitTy unitTy (.ret (.var 0)) [] []
def responseOne : Value First Empty := .ref (.inr 0)
def responseTwo : Value First Empty := .wrap responseOne identityAdapter identityAdapter

theorem responseOne_typed : ValueTyped firstTypes emptyTy emptyContext responseOne callableTy := .ref _
theorem responseTwo_typed : ValueTyped firstTypes emptyTy emptyContext responseTwo callableTy :=
  .wrap responseOne_typed (.mk (.ret (.var rfl))) (.mk (.ret (.var rfl)))
theorem responses_distinct : responseOne ≠ responseTwo := by intro h; cases h

/-- Actual fresh lookup and lambda entry carry the real code and consumer. -/
def carrier : Value First Empty := .delay (.ret (.ref (.inl 0)))
def callbackPlan : LambdaEntryPlan First :=
  ⟨.value, receipt, unitTy, unitTy, unitTy, .ret (.var 0),
    .mk unitTy unitTy (.bind (.ret .unit) (.ret (.var 1))) [] [], carrier⟩
def afterEntry : Comp First Empty :=
  .bind (.scope 17 callbackPlan.computation) (.ret (.var 0))

theorem fresh_response_entry :
    Steps first ((saved.map Sum.inl).resume responseOne)
      [.lookup (.inr 0), .lambdaEntry callbackPlan] afterEntry :=
  .cons (.bind (.scope .callRef))
    (.cons (.bind (.scope .callLambda)) (.refl _))

theorem two_responses_safe
    (one : Steps first ((saved.map Sum.inl).resume responseOne) t1 n1)
    (two : Steps first ((saved.map Sum.inl).resume responseTwo) t2 n2) :
    (CompTyped firstTypes emptyTy emptyContext n1 unitTy ∧ CanProgress (graph := first) n1) ∧
    (CompTyped firstTypes emptyTy emptyContext n2 unitTy ∧ CanProgress (graph := first) n2) :=
  repeated_responses firstChain saved_actual_request first_typed firstGuard
    responseOne responseTwo responseOne_typed responseTwo_typed one two

/-- A SECOND source allocation captures the first graph's actual callback under
new delayed code. No old reference is overwritten and the new reference cannot
be typed in oldTypes or firstTypes. -/
def delayedTypes : Fin 1 → Ty := fun _ => .thunk callableTy
def callbackContext : Context := extend emptyContext callableTy
def callbackCapture : Nat → Value First Empty := fun _ => responseOne
def delayedRhs : HigherOrder.Value := .delay (.ret (.var 1))

theorem callbackCapture_typed : CapturesTyped firstTypes callbackContext callbackCapture := by
  intro i a hi
  cases i with
  | zero =>
      change some callableTy = some a at hi
      cases hi
      exact responseOne_typed
  | succ i => cases hi

theorem delayedRhs_typed :
    HigherOrder.ValueTyped (sourceContext delayedTypes callbackContext) delayedRhs (.thunk callableTy) :=
  .delay (.ret (.var rfl))

def freshTwo := sourceFresh callbackCapture (fun _ : Fin 1 => delayedRhs)
abbrev Second := Sum First (Fin 1)
def second : Graph Second := allocate first freshTwo
def secondTypes : Second → Ty := joinTy firstTypes delayedTypes

theorem freshTwo_equation (i : Fin 1) :
    freshTwo i = .delay (.ret (.ref (.inl (.inr 0)))) := rfl

theorem freshTwo_noCycle : FreshNoCycle freshTwo :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

theorem second_typed : WellTyped second secondTypes :=
  allocate_typed first_typed freshTwo
    (fun _ => sourceCloseValue_typed delayedRhs_typed callbackCapture_typed)

def secondGuard : GuardedValueGraph.Guarded (projectGraph second) :=
  allocationGuard firstGuard freshTwo freshTwo_noCycle

def secondEmbedding : Embedding first firstTypes second secondTypes :=
  allocationEmbedding first firstTypes delayedTypes freshTwo

def secondChain : Chain (Fin 1) old oldTypes Second second secondTypes :=
  .snoc firstChain secondEmbedding

/-- This callable response mentions the brand-new delayed node in its BODY.
The computation-mode parameter remains a thunk, and the result consumer is real. -/
def secondResponse : Value Second Empty :=
  .lambda .computation receipt unitTy unitTy unitTy
    (.bind (.force (.ref (.inr 0))) (.dynamicCall (.var 0) (.var 1)))
    identityAdapter

theorem secondResponse_typed :
    ValueTyped secondTypes emptyTy emptyContext secondResponse callableTy :=
  .lambdaComputation
    (.bind (.force (.ref _)) (.dynamicCall (.var rfl) (.var rfl)))
    (.mk (.ret (.var rfl)))

theorem old_after_second_safe
    (steps : Steps second ((saved.map secondChain.embedding.refs).resume secondResponse) trace last) :
    CompTyped secondTypes emptyTy emptyContext last unitTy ∧ CanProgress (graph := second) last :=
  chain_resume_safety secondChain saved_actual_request second_typed secondGuard
    secondResponse secondResponse_typed steps

/-- One concrete interaction publishes the original request, extends, and
answers it using a newly allocated callable. -/
theorem first_interaction :
    Run (Fin 1) old oldTypes saved.suspended First first firstTypes
      ((saved.map Sum.inl).resume responseOne) [saved.map Sum.inl] := by
  apply Run.answer (saved := saved.map Sum.inl)
  · exact .extension (allocationEmbedding old oldTypes callbackTypes freshOne)
      (.publish saved .start) first_typed
  · exact List.mem_cons.mpr (.inl rfl)
  · exact .matched operation rfl responseOne
  · exact responseOne_typed

/-- The same stored record survives the first answer and a second allocation.
Its second answer uses code containing the newest delayed reference. -/
theorem second_interaction :
    Run (Fin 1) old oldTypes saved.suspended Second second secondTypes
      ((saved.map secondChain.embedding.refs).resume secondResponse)
      [saved.map secondChain.embedding.refs] := by
  apply Run.answer (saved := saved.map secondChain.embedding.refs)
  · have prior := Run.extension secondEmbedding first_interaction second_typed
    simpa only [List.map_cons, List.map_nil, saved_map_comp, secondChain,
      firstChain, Chain.embedding, Embedding.trans, Embedding.refl, allocationEmbedding, id] using prior
  · exact List.mem_cons.mpr (.inl rfl)
  · exact .matched operation rfl secondResponse
  · exact secondResponse_typed

/-- A second old saved request accepts a genuinely delayed fresh reference,
then forces and calls the returned callback in the old response continuation. -/
def delayedSaved : Saved (Fin 1) :=
  ⟨delayedOperation, .ref 0,
    .bind (.force (.var 0)) (.dynamicCall (.var 0) (.delay (.ret (.ref 0)))),
    .scope 19 .hole⟩

theorem delayedSaved_actual_request :
    CompTyped oldTypes emptyTy emptyContext delayedSaved.suspended unitTy :=
  .scope (.request (.ref 0)
    (.bind (.force (.var rfl)) (.dynamicCall (.var rfl) (.delay (.ret (.ref 0))))))

def delayedResponse : Value Second Empty := .ref (.inr 0)

theorem delayedResponse_typed :
    ValueTyped secondTypes emptyTy emptyContext delayedResponse (.thunk callableTy) := .ref _

theorem delayed_old_after_second_safe
    (steps : Steps second ((delayedSaved.map secondChain.embedding.refs).resume delayedResponse) trace last) :
    CompTyped secondTypes emptyTy emptyContext last unitTy ∧ CanProgress (graph := second) last :=
  chain_resume_safety secondChain delayedSaved_actual_request second_typed secondGuard
    delayedResponse delayedResponse_typed steps

/-- Same ID and endpoints, different ordered type arguments: still rejected. -/
def wrongInstance : OperationInstance := ⟨73, [], unitTy, callableTy⟩
theorem wrongInstance_distinct : wrongInstance ≠ operation := by
  intro h
  have args := congrArg OperationInstance.typeArguments h
  cases args

theorem wrongInstance_cannot_resume :
    ¬ Answer (saved.map Sum.inl) wrongInstance responseOne next :=
  mismatched_instance_rejected wrongInstance_distinct

/-- The exact old node equations also exclude replacement by a fresh lambda. -/
theorem overwrite_unit_rejected (e : Embedding old oldTypes first firstTypes)
    (bad : first (e.refs 0) = freshOne 0) : False := by
  have equation := e.nodes 0
  rw [bad] at equation
  change freshOne 0 = .unit at equation
  rw [freshOne_equation] at equation
  cases equation

end Demo
end YulangClosure.HigherOrderGraph.Extension
