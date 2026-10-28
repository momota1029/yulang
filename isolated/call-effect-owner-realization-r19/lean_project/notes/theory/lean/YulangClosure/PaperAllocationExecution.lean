import YulangClosure.PaperHeapExecution

/-!
Finite allocation/execution evidence for the actual paper syntax. The graph,
heap and saved-request list are explicit indices around `PaperCoreControl.State`;
they are not new fields of that executor or a replacement operational semantics.
Allocation is literally `FreshHeap.allocate`; execution uses the existing
`PaperExtendedExecution.controlStep` and exposed-response interface. The sole
observation case is R62's supplied finite Force observation followed by its real
Force/Delay transition. No observation termination is assumed or concluded.

All state, heap and saved-continuation typing below follows from initial typing
and independent source block/substitution, table-body and current-response
typing. No constructor assumes a preservation law or its resulting invariant.
Original source-rec realization/order, guarded heap typing, full owner/world
resumption, all source constructors, progress and native correspondence remain
OPEN. In particular allocation of a block alone does not execute source `rec`.
-/
namespace YulangClosure.PaperTypes.PaperAllocationExecution

open FreshHeap PaperCoreControl PaperHeapObservation

/-- Preserve successful reads, including the exact immutable payload. -/
def HeapLookupPreserved (old new : Heap) : Prop :=
  ∀ identity payload, lookupHeap old identity = some payload →
    lookupHeap new identity = some payload

theorem observationStep_transport {old new source target}
    (hp : HeapLookupPreserved old new) (hs : ObservationStep old source target) :
    ObservationStep new source target := by
  induction hs with
  | graphRead lookup => exact .graphRead (hp _ _ lookup)
  | typeBeta beta => exact .typeBeta beta
  | typeApplication step ih => exact .typeApplication ih

theorem observationTrace_transport {old new source target}
    (hp : HeapLookupPreserved old new) (path : ObservationTrace old source target) :
    ObservationTrace new source target := by
  induction path with
  | refl => exact .refl _
  | cons step path ih => exact .cons (observationStep_transport hp step) ih

/-- Actual fresh allocation preserves every already successful observation. -/
theorem allocation_observationStep {block rho heap source target}
    (fresh : ∀ r, r ∈ ids block → r ∉ heap.map Prod.fst)
    (hs : ObservationStep heap source target) :
    ObservationStep (allocate block rho heap) source target :=
  observationStep_transport (fun _ _ => heap_old_success block rho heap fresh) hs

theorem allocation_observationTrace {block rho heap source target}
    (fresh : ∀ r, r ∈ ids block → r ∉ heap.map Prod.fst)
    (path : ObservationTrace heap source target) :
    ObservationTrace (allocate block rho heap) source target :=
  observationTrace_transport (fun _ _ => heap_old_success block rho heap fresh) path

theorem stack_graphWeaken {d old new e stack a result}
    (hp : GraphLookupPreserved old new) (ht : StackTyped d old e stack a result) :
    StackTyped d new e stack a result := by
  induction ht with
  | nil => exact .nil
  | cons body rest ih => exact .cons (body.graphWeaken hp) ih

theorem state_graphWeaken {d old new e state result}
    (hp : GraphLookupPreserved old new) (ht : StateTyped d old e state result) :
    StateTyped d new e state result := by
  obtain ⟨a, head, stack⟩ := ht
  exact ⟨a, head.graphWeaken hp, stack_graphWeaken hp stack⟩

/-- The allocated body and heap use one simultaneous substitution and one graph.
This is the body/payload component of rec, not an execution rule for the still
unrepresented `Computation.recursive` typing case. -/
theorem allocation_body
    {d old source e rho block heap body stack a result}
    (unique : (ids block).Nodup)
    (freshGraph : ∀ r, r ∈ ids block → r ∉ old.map Prod.fst)
    (freshHeap : ∀ r, r ∈ ids block → r ∉ heap.map Prod.fst)
    (hr : TermSubstitutionTyped d old source e rho)
    (hb : BlockTyped d old source block)
    (hh : HeapPayloadTyped d old e heap)
    (bodyTyped : PaperComputationTyped d old ((formals block).map Prod.snd ++ source) body a)
    (stackTyped : StackTyped d old e stack a result) :
    GraphLookupPreserved old (formals block ++ old) ∧
    HeapLookupPreserved heap (allocate block rho heap) ∧
    HeapPayloadTyped d (formals block ++ old) e (allocate block rho heap) ∧
    termSubstituteComputation (graphFormalReplacements (formals block) rho) body =
      some (replaceTermComputation (graphFormalReplacements (formals block) rho) body) ∧
    StateTyped d (formals block ++ old) e
      ⟨replaceTermComputation (graphFormalReplacements (formals block) rho) body, stack⟩ result := by
  obtain ⟨hg, hn, _, _, _, _, hlookup, heapTyped⟩ :=
    finite_allocation unique freshGraph freshHeap hr hb hh
  have replacement := graphFormalReplacements_typed (formals block) hg hn hr
  refine ⟨hg, hlookup, heapTyped, ?_, a,
    (bodyTyped.graphWeaken hg).termReplace replacement, stack_graphWeaken hg stackTyped⟩
  simp only [termSubstituteComputation, bodyTyped.termSupported, ↓reduceIte]

/-- The complete exposed packet, with its actual operation instance and code.
There is no saved graph, heap, mutable world or typing certificate in this data. -/
structure SavedRequest where
  operation : OperationInstance
  payload : Value
  responseBinder : TermName
  body : Computation

def SavedRequest.request (saved : SavedRequest) : Computation :=
  .request saved.operation saved.payload (.continuation [] saved.responseBinder saved.body)

def SavedRequest.state (saved : SavedRequest) : State := ⟨saved.request, []⟩

def SavedRequest.resume (saved : SavedRequest) (response : Value) : State :=
  ⟨.resume (.continuation [] saved.responseBinder saved.body) response, []⟩

def SavedRequestTyped (d : DeclarationTable) (g : GraphEnvironment)
    (e : TypeEnvironment) (saved : SavedRequest) (result : Ty) : Prop :=
  PaperComputationTyped d g e saved.request result

def SavedRequestsTyped (d : DeclarationTable) (g : GraphEnvironment)
    (e : TypeEnvironment) (saved : List SavedRequest) (result : Ty) : Prop :=
  ∀ packet, packet ∈ saved → SavedRequestTyped d g e packet result

/-- Both payload and continuation use the fields of the same actual instance. -/
theorem saved_request_components {d g e saved result}
    (ht : SavedRequestTyped d g e saved result) :
    PaperValueTyped d g e saved.payload saved.operation.payloadType ∧
    PaperContinuationTyped d g e (.continuation [] saved.responseBinder saved.body)
      saved.operation.responseType result := by
  rcases saved with ⟨operation, payload, responseBinder, body⟩
  cases ht with
  | request resolved arity instanceEq payload continuation =>
      cases instanceEq
      exact ⟨payload, continuation⟩

theorem saved_requests_graphWeaken {d old new e saved result}
    (hp : GraphLookupPreserved old new)
    (ht : SavedRequestsTyped d old e saved result) :
    SavedRequestsTyped d new e saved result := by
  intro packet member
  exact (ht packet member).graphWeaken hp

theorem saved_response_eq (saved : SavedRequest) (response : Value) :
    PaperExtendedExecution.responseStep response saved.state =
      some (saved.resume response) := rfl

theorem saved_response_typed {d g e saved response result}
    (ht : SavedRequestTyped d g e saved result)
    (hr : PaperValueTyped d g e response saved.operation.responseType) :
    StateTyped d g e (saved.resume response) result :=
  ⟨result, PaperResumeExecution.resume_typed (saved_request_components ht).2 hr, .nil⟩

/-- A finite record of existing operations on shared witnesses. `save` only
records an exposed request; it does not move the executor. A response starts at
that same exposed request and is checked at the current graph. All saved data
is retained literally by allocation, execution, observation and response.
Initial saved data is empty, so no saved continuation typing is an input. -/
inductive History (d : DeclarationTable) (binder : TermName) (e : TypeEnvironment)
    (initialGraph : GraphEnvironment) (initialHeap : Heap) (initialState : State) :
    GraphEnvironment → Heap → State → List SavedRequest → Type where
  | initial : History d binder e initialGraph initialHeap initialState
      initialGraph initialHeap initialState []
  | internal {g heap state saved next} :
      History d binder e initialGraph initialHeap initialState g heap state saved →
      PaperExtendedExecution.controlStep d binder state = some next →
      History d binder e initialGraph initialHeap initialState g heap next saved
  | allocation {g heap state saved source rho block} :
      History d binder e initialGraph initialHeap initialState g heap state saved →
      (ids block).Nodup →
      (∀ r, r ∈ ids block → r ∉ g.map Prod.fst) →
      (∀ r, r ∈ ids block → r ∉ heap.map Prod.fst) →
      TermSubstitutionTyped d g source e rho → BlockTyped d g source block →
      History d binder e initialGraph initialHeap initialState
        (formals block ++ g) (allocate block rho heap) state saved
  | save {g heap saved packet} :
      History d binder e initialGraph initialHeap initialState g heap packet.state saved →
      History d binder e initialGraph initialHeap initialState
        g heap packet.state (packet :: saved)
  | response {g heap saved packet response} :
      History d binder e initialGraph initialHeap initialState g heap packet.state saved →
      PaperValueTyped d g e response packet.operation.responseType →
      History d binder e initialGraph initialHeap initialState
        g heap (packet.resume response) (packet :: saved)
  | observedForce {g heap saved source body stack} :
      History d binder e initialGraph initialHeap initialState
        g heap ⟨.force source, stack⟩ saved →
      ObservationTrace heap source (.delay body) →
      History d binder e initialGraph initialHeap initialState g heap ⟨body, stack⟩ saved

/-- Every existing finite interaction segment embeds, retaining all previously
saved packets and recording the exact packet at each response boundary. -/
theorem interaction_history
    {d binder e initialGraph initialHeap initialState g heap first last saved}
    (start : History d binder e initialGraph initialHeap initialState g heap first saved)
    (path : PaperExtendedExecution.InteractionTrace d binder first last)
    (protocol : PaperExtendedExecution.ProtocolTyped g e path) :
    ∃ retained, Nonempty (History d binder e initialGraph initialHeap initialState
      g heap last retained) ∧ ∀ packet, packet ∈ saved → packet ∈ retained := by
  induction path generalizing saved with
  | refl => exact ⟨saved, ⟨start⟩, fun _ member => member⟩
  | tail path event ih =>
      obtain ⟨middleSaved, ⟨earlier⟩, retained⟩ := ih start protocol.1
      cases event with
      | internal step => exact ⟨middleSaved, ⟨.internal earlier step⟩, retained⟩
      | response op payload responseBinder body response =>
          let packet : SavedRequest := ⟨op, payload, responseBinder, body⟩
          exact ⟨packet :: middleSaved,
            ⟨.response (packet := packet) earlier protocol.2⟩,
            fun p member => List.mem_cons_of_mem packet (retained p member)⟩

/-- No typing is needed for the literal old graph/heap and suffix identities. -/
theorem history_extension {d binder e initialGraph initialHeap initialState g heap state saved}
    (history : History d binder e initialGraph initialHeap initialState g heap state saved) :
    GraphLookupPreserved initialGraph g ∧ HeapLookupPreserved initialHeap heap ∧
      ∃ front, heap = front ++ initialHeap := by
  induction history with
  | initial => exact ⟨fun _ _ h => h, fun _ _ h => h, [], rfl⟩
  | internal history step ih => exact ih
  | @allocation g heap state saved source rho block history unique freshGraph freshHeap hr hb ih =>
      obtain ⟨hg, hh, front, he⟩ := ih
      refine ⟨fun r a h => graph_old_lookup block g freshGraph r a (hg r a h),
        fun r v h => heap_old_success block rho heap freshHeap (hh r v h),
        nodes block rho ++ front, ?_⟩
      simp only [allocate, he, List.append_assoc]
  | save history ih => exact ih
  | response history response ih => exact ih
  | observedForce history path ih => exact ih

/-- The invariant is proved from the initial state/heap and the actual history.
In particular no final graph typing or saved-body typing is a hypothesis. -/
theorem history_preservation
    {d binder e initialGraph initialHeap initialState g heap state saved result}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (hh : HeapPayloadTyped d initialGraph e initialHeap)
    (ht : StateTyped d initialGraph e initialState result)
    (history : History d binder e initialGraph initialHeap initialState g heap state saved) :
    HeapPayloadTyped d g e heap ∧ StateTyped d g e state result ∧
      SavedRequestsTyped d g e saved result := by
  induction history with
  | initial => exact ⟨hh, ht, fun _ member => by cases member⟩
  | internal history step ih =>
      exact ⟨ih.1, PaperExtendedExecution.preservation hd ih.2.1 step, ih.2.2⟩
  | allocation history unique freshGraph freshHeap hr hb ih =>
      obtain ⟨hp, _, _, _, _, _, _, heapTyped⟩ :=
        finite_allocation unique freshGraph freshHeap hr hb ih.1
      exact ⟨heapTyped, state_graphWeaken hp ih.2.1, saved_requests_graphWeaken hp ih.2.2⟩
  | @save g heap saved packet history ih =>
      refine ⟨ih.1, ih.2.1, ?_⟩
      intro found member
      rcases List.mem_cons.mp member with eq | old
      · subst found
        exact PaperPerformLetExecution.external_request ih.2.1
      · exact ih.2.2 found old
  | @response g heap saved packet response history responseTyped ih =>
      have packetTyped : SavedRequestTyped d g e packet result :=
        PaperPerformLetExecution.external_request ih.2.1
      refine ⟨ih.1, saved_response_typed packetTyped responseTyped, ?_⟩
      intro found member
      rcases List.mem_cons.mp member with eq | old
      · subst found; exact packetTyped
      · exact ih.2.2 found old
  | @observedForce g heap saved source body stack history path ih =>
      have hs := PaperExtendedExecution.controlStep_force_delay d binder body stack
      have observed := PaperHeapExecution.observed_force_control hd ih.1 ih.2.1 path hs
      exact ⟨ih.1, observed.2.1, ih.2.2⟩

/-- Every old observation remains an observation on the same final heap. -/
theorem history_observation_transport
    {d binder e initialGraph initialHeap initialState g heap state saved source target}
    (history : History d binder e initialGraph initialHeap initialState g heap state saved)
    (path : ObservationTrace initialHeap source target) : ObservationTrace heap source target :=
  observationTrace_transport (history_extension history).2.1 path

/-- The application to the preservation part of the original finite-prefix
claim, with the current heap/state and every actually saved packet together. -/
theorem finite_history
    {d binder e initialGraph initialHeap initialState g heap state saved result}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (hh : HeapPayloadTyped d initialGraph e initialHeap)
    (ht : StateTyped d initialGraph e initialState result)
    (history : History d binder e initialGraph initialHeap initialState g heap state saved) :
    GraphLookupPreserved initialGraph g ∧ HeapLookupPreserved initialHeap heap ∧
    (∃ front, heap = front ++ initialHeap) ∧ HeapPayloadTyped d g e heap ∧
    StateTyped d g e state result ∧ PaperComputationTyped d g e (erase state) result ∧
    ∀ packet, packet ∈ saved →
      SavedRequestTyped d g e packet result ∧
      PaperValueTyped d g e packet.payload packet.operation.payloadType ∧
      PaperContinuationTyped d g e (.continuation [] packet.responseBinder packet.body)
        packet.operation.responseType result := by
  have extension := history_extension history
  have preserved := history_preservation hd hh ht history
  refine ⟨extension.1, extension.2.1, extension.2.2, preserved.1,
    preserved.2.1, erase_typed preserved.2.1, ?_⟩
  intro packet member
  have typed := preserved.2.2 packet member
  exact ⟨typed, saved_request_components typed⟩

/-- A retained packet can be invoked again at the current graph. This theorem
constructs the real exposed-response boundary and checks an actual executor
prefix from it; it does not assert a scheduler jump from the current state. -/
theorem saved_response_prefix
    {d binder e initialGraph initialHeap initialState g heap state saved result packet response last}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (hh : HeapPayloadTyped d initialGraph e initialHeap)
    (ht : StateTyped d initialGraph e initialState result)
    (history : History d binder e initialGraph initialHeap initialState g heap state saved)
    (member : packet ∈ saved)
    (responseTyped : PaperValueTyped d g e response packet.operation.responseType)
    (path : PaperExtendedExecution.Trace d binder (packet.resume response) last) :
    PaperExtendedExecution.responseStep response packet.state = some (packet.resume response) ∧
    StateTyped d g e last result ∧ PaperComputationTyped d g e (erase last) result ∧
    PaperExtendedExecution.ErasureTrace d binder (erase (packet.resume response)) (erase last) ∧
    SavedRequestTyped d g e packet result ∧
    PaperContinuationTyped d g e (.continuation [] packet.responseBinder packet.body)
      packet.operation.responseType result := by
  have packetTyped := (history_preservation hd hh ht history).2.2 packet member
  have branch := PaperExtendedExecution.finite_prefix hd
    (saved_response_typed packetTyped responseTyped) path
  exact ⟨saved_response_eq packet response, branch.1, branch.2.1, branch.2.2,
    packetTyped, (saved_request_components packetTyped).2⟩

/-- Reuse a saved packet with the current heap/graph, then permit another finite
history with further allocations. The original and new saved packets all remain
typed at the final graph. The same theorem can be applied repeatedly to the same
`packet`; neither its payload, body nor operation instance is modified. -/
theorem saved_response_history
    {d binder e initialGraph initialHeap initialState g heap state saved result packet response
      finalGraph finalHeap last newSaved}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (hh : HeapPayloadTyped d initialGraph e initialHeap)
    (ht : StateTyped d initialGraph e initialState result)
    (history : History d binder e initialGraph initialHeap initialState g heap state saved)
    (member : packet ∈ saved)
    (responseTyped : PaperValueTyped d g e response packet.operation.responseType)
    (branch : History d binder e g heap (packet.resume response) finalGraph finalHeap last newSaved) :
    PaperExtendedExecution.responseStep response packet.state = some (packet.resume response) ∧
    HeapPayloadTyped d finalGraph e finalHeap ∧ StateTyped d finalGraph e last result ∧
    PaperComputationTyped d finalGraph e (erase last) result ∧
    SavedRequestsTyped d finalGraph e (newSaved ++ saved) result ∧
    PaperContinuationTyped d finalGraph e (.continuation [] packet.responseBinder packet.body)
      packet.operation.responseType result := by
  have before := history_preservation hd hh ht history
  have packetTyped := before.2.2 packet member
  have branchTyped := history_preservation hd before.1
    (saved_response_typed packetTyped responseTyped) branch
  have extension := (history_extension branch).1
  have oldSaved := saved_requests_graphWeaken extension before.2.2
  refine ⟨saved_response_eq packet response, branchTyped.1, branchTyped.2.1,
    erase_typed branchTyped.2.1, ?_, (saved_request_components (oldSaved packet member)).2⟩
  intro p hm
  rcases List.mem_append.mp hm with new | old
  · exact branchTyped.2.2 p new
  · exact oldSaved p old

/-- Enter the finite history directly from source block/body typing. Neither
the initial allocated state nor any final/saved typing is supplied as a law. -/
theorem allocated_body_history
    {d binder old source e rho block heap body stack a result g finalHeap state saved}
    (hd : PaperTemplateExecution.BodiesTyped d)
    (unique : (ids block).Nodup)
    (freshGraph : ∀ r, r ∈ ids block → r ∉ old.map Prod.fst)
    (freshHeap : ∀ r, r ∈ ids block → r ∉ heap.map Prod.fst)
    (hr : TermSubstitutionTyped d old source e rho)
    (hb : BlockTyped d old source block)
    (hh : HeapPayloadTyped d old e heap)
    (bodyTyped : PaperComputationTyped d old ((formals block).map Prod.snd ++ source) body a)
    (stackTyped : StackTyped d old e stack a result)
    (history : History d binder e (formals block ++ old) (allocate block rho heap)
      ⟨replaceTermComputation (graphFormalReplacements (formals block) rho) body, stack⟩
      g finalHeap state saved) :
    GraphLookupPreserved old g ∧ HeapLookupPreserved heap finalHeap ∧
    HeapPayloadTyped d g e finalHeap ∧ StateTyped d g e state result ∧
    PaperComputationTyped d g e (erase state) result ∧ SavedRequestsTyped d g e saved result := by
  have entry := allocation_body unique freshGraph freshHeap hr hb hh bodyTyped stackTyped
  have extension := history_extension history
  have preserved := history_preservation hd entry.2.2.1 entry.2.2.2.2 history
  exact ⟨fun r t h => extension.1 r t (entry.1 r t h),
    fun r v h => extension.2.1 r v (entry.2.1 r v h),
    preserved.1, preserved.2.1, erase_typed preserved.2.1, preserved.2.2⟩

/-! A closed discriminator: save before allocating any node; respond with a
fresh graph-backed thunk; allocate another thunk during its execution; read the
unchanged old node; then reuse the same saved body with the new current node.
The two invocations return different Booleans without changing the saved code. -/

def exampleDeclaration : OperationDeclaration :=
  ⟨71, 0, .base .unit, .thunk (.base .bool)⟩

def exampleTable : DeclarationTable := ⟨[exampleDeclaration], [], [], [], 0⟩

def examplePacket (binder : TermName) : SavedRequest :=
  ⟨exampleDeclaration.instantiate [], .literal .unit, binder, .force (.variable 0)⟩

def exampleBlock (identity : Nat) (value : Bool) : Block :=
  [(identity, .thunk (.base .bool), .delay (.ret (.literal (.boolean value))))]

def exampleGraph : GraphEnvironment := formals (exampleBlock 20 false) ++ formals (exampleBlock 10 true)

def exampleHeap : Heap :=
  allocate (exampleBlock 20 false) Value.variable (allocate (exampleBlock 10 true) Value.variable [])

theorem example_block_typed (d g e identity value) :
    BlockTyped d g e (exampleBlock identity value) := by
  intro r a v member
  have eq := List.mem_singleton.mp member
  cases eq
  exact .delay (.ret .literal)

theorem example_packet_typed (binder : TermName) :
    StateTyped exampleTable [] [] (examplePacket binder).state (.base .bool) := by
  have resolved : OperationDeclarationResolved exampleTable.operations 71 exampleDeclaration := by
    refine ⟨by simp [exampleTable], rfl, ?_⟩
    intro other member _
    exact List.mem_singleton.mp member
  exact ⟨.base .bool,
    .request resolved rfl rfl .literal (.continuation (.force (.variable rfl))), .nil⟩

theorem example_resume_step (binder : TermName) (identity : Nat) :
    PaperExtendedExecution.controlStep exampleTable binder
      ((examplePacket binder).resume (.graphReference identity)) =
      some ⟨.force (.graphReference identity), []⟩ := by
  apply PaperExtendedExecution.controlStep_extends
  unfold SavedRequest.resume
  rw [PaperCombinedExecution.controlStep_resume]
  simp [examplePacket, PaperResumeExecution.resumeStep, termSubstituteComputation,
    supportedTermComputation, supportedTermValue, replaceTermComputation, replaceTermValue,
    PaperCoreStep.singleReplacement]

/-- The second response is unavailable in the save-time graph and has the
required type in the actual current graph. A saved graph snapshot would fail. -/
theorem example_response_requires_extension :
    ¬ PaperValueTyped exampleTable [] [] (.graphReference 20) (.thunk (.base .bool)) ∧
    PaperValueTyped exampleTable exampleGraph [] (.graphReference 20) (.thunk (.base .bool)) := by
  constructor
  · intro typed
    cases typed with
    | graphReference lookup => cases lookup
  · exact .graphReference (by simp [exampleGraph, formals, exampleBlock, lookupGraphEnvironment])

/-- All allocation, response, substitution, observation and executable steps
are constructed; no final typing, graph extension or future step is assumed. -/
theorem fresh_response_replay (binder : TermName) :
    Nonempty (History exampleTable binder [] [] [] (examplePacket binder).state
      exampleGraph exampleHeap ⟨.ret (.literal (.boolean true)), []⟩
      [examplePacket binder, examplePacket binder]) ∧
    Nonempty (History exampleTable binder [] exampleGraph exampleHeap
      ((examplePacket binder).resume (.graphReference 20))
      exampleGraph exampleHeap ⟨.ret (.literal (.boolean false)), []⟩ []) ∧
    StateTyped exampleTable exampleGraph [] ⟨.ret (.literal (.boolean true)), []⟩ (.base .bool) ∧
    StateTyped exampleTable exampleGraph [] ⟨.ret (.literal (.boolean false)), []⟩ (.base .bool) ∧
    PaperContinuationTyped exampleTable exampleGraph []
      (.continuation [] binder (.force (.variable 0))) (.thunk (.base .bool)) (.base .bool) := by
  have hd : PaperTemplateExecution.BodiesTyped exampleTable := by
    intro entry member
    cases member
  have hh : HeapPayloadTyped exampleTable [] [] [] := by
    intro r v member
    cases member
  have hr (g : GraphEnvironment) : TermSubstitutionTyped exampleTable g [] [] Value.variable := by
    intro n a lookup
    cases lookup
  let start : History exampleTable binder [] [] [] (examplePacket binder).state
      [] [] (examplePacket binder).state [examplePacket binder] := .save .initial
  let firstAllocation := History.allocation (block := exampleBlock 10 true) start
    (by simp [ids, exampleBlock]) (by simp [ids]) (by simp [ids])
    (hr []) (example_block_typed exampleTable [] [] 10 true)
  have response10 : PaperValueTyped exampleTable (formals (exampleBlock 10 true) ++ []) []
      (.graphReference 10) (examplePacket binder).operation.responseType := by
    exact .graphReference (by simp [formals, exampleBlock, lookupGraphEnvironment,
      examplePacket, exampleDeclaration, OperationDeclaration.instantiate, subst])
  let answered := History.response firstAllocation response10
  let resumed := History.internal answered (example_resume_step binder 10)
  let secondAllocation := History.allocation (block := exampleBlock 20 false) resumed
    (by simp [ids, exampleBlock])
    (by simp [ids, formals, exampleBlock])
    (by simp [ids, allocate, nodes, exampleBlock])
    (hr _) (example_block_typed exampleTable _ [] 20 false)
  have lookup10 : lookupHeap exampleHeap 10 =
      some (.delay (.ret (.literal (.boolean true)))) := by
    simp [exampleHeap, exampleBlock, allocate, nodes, lookupHeap, replaceTermValue, replaceTermComputation]
  have lookup20 : lookupHeap exampleHeap 20 =
      some (.delay (.ret (.literal (.boolean false)))) := by
    simp [exampleHeap, exampleBlock, allocate, nodes, lookupHeap, replaceTermValue, replaceTermComputation]
  let first : History exampleTable binder [] [] [] (examplePacket binder).state
      exampleGraph exampleHeap ⟨.ret (.literal (.boolean true)), []⟩
      [examplePacket binder, examplePacket binder] :=
    .observedForce secondAllocation (.cons (.graphRead lookup10) (.refl _))
  let second : History exampleTable binder [] exampleGraph exampleHeap
      ((examplePacket binder).resume (.graphReference 20)) exampleGraph exampleHeap
      ⟨.ret (.literal (.boolean false)), []⟩ [] :=
    .observedForce (.internal .initial (example_resume_step binder 20))
      (.cons (.graphRead lookup20) (.refl _))
  have response20 : PaperValueTyped exampleTable exampleGraph []
      (.graphReference 20) (examplePacket binder).operation.responseType := by
    exact .graphReference (by simp [exampleGraph, formals, exampleBlock, lookupGraphEnvironment,
      examplePacket, exampleDeclaration, OperationDeclaration.instantiate, subst])
  have firstTyped := history_preservation hd hh (example_packet_typed binder) first
  have replay := saved_response_history hd hh (example_packet_typed binder) first
    (by simp) response20 second
  exact ⟨⟨first⟩, ⟨second⟩, firstTyped.2.1, replay.2.2.1, replay.2.2.2.2.2⟩

end YulangClosure.PaperTypes.PaperAllocationExecution
