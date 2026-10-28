import YulangClosure.HandlerGraphRecInteraction

/-! A concrete application of source allocation to persistent interaction.
The operation-75 payload is the freshly allocated callback's own reference.
This is a finite research-machine trace, not a native correspondence theorem. -/
namespace YulangClosure.HandlerGraph.Combined.RecursiveTrace
open HigherOrder (Ty Context emptyContext extend OperationInstance)
open YulangClosure.HandlerGraph.Extension
open YulangClosure.HandlerGraph.Extension.Demo
open YulangClosure.HandlerGraph.Recursive
open YulangClosure.HandlerGraph.Combined.ConcreteSourceRun

abbrev FirstRef := Sum (Fin 1) (Fin 1)
abbrev SecondRef := Sum FirstRef (Fin 1)

/-- This literal handler is justified by closing the WHOLE source lambda below.
Closing the open source handler alone would omit the lambda binder lift. -/
def closedHandler : Handler FirstRef Empty :=
  .mk 92 unitTy unitTy
    (.cons (.request recursiveOperation recursiveResponse
      (.ret (.inRight (.var 0)))) .nil) .nil

def closedCallback : Value FirstRef Empty :=
  .lambda .computation receipt unitTy unitTy unitTy
    (.handle closedHandler (.ret .unit)) identityAdapter

/-- The nested value-arm variable 2 becomes precisely recursive slot zero.
No endpoint equation or graph-node equation is an input to this proof. -/
theorem whole_source_closure :
    sourceCloseValue captures 1 recursiveCallback = closedCallback := rfl

theorem actual_fresh_node :
    recursiveFresh (0 : Fin 1) = closedCallback := whole_source_closure

theorem actual_graph_node :
    recursiveGraph (.inr (0 : Fin 1)) = closedCallback := actual_fresh_node

def recursivePlan : LambdaEntryPlan FirstRef :=
  ⟨.computation, receipt, unitTy, unitTy, unitTy,
    .handle closedHandler (.ret .unit), identityAdapter, carrier⟩

def recursiveSaved : Saved FirstRef :=
  ⟨recursiveOperation, recursiveResponse,
    .bind (.waitValue closedHandler .unit .nil (.ret (.inRight (.var 0))))
      (.ret (.var 0))⟩

def recursiveEvents : List (Event FirstRef) :=
  [.lookup (.inr 0), .lambdaEntry recursivePlan,
    .silent, .silent, .silent, .silent]

/-- Lookup and lambda entry, then value-handler dispatch, arm attempt, wait
propagation and bind propagation expose the actual root request. -/
theorem recursive_callback_reaches_own_request :
    Prefix recursiveGraph ((saved.map Sum.inl).resume recursiveResponse)
      recursiveEvents recursiveSaved.suspended := by
  exact .cons .callRef
    (.cons .callLambda
      (.cons (.bind .handleReturn)
        (.cons (.bind .valueCons)
          (.cons (.bind .valueRequest)
            (.cons .bindRequest (.refl _))))))

theorem endpoint_operation : recursiveSaved.operation = recursiveOperation := rfl

theorem endpoint_own_payload :
    recursiveSaved.payload = .ref (Sum.inr (0 : Fin 1)) := rfl

/-- Capture typing is derived from this source-generated reachable endpoint. -/
theorem reached_saved_typed : SavedTyped recursiveTypes recursiveSaved unitTy := by
  have invariant := run_invariant old_typed saved_actual_request
    recursive_callback_answers_old_entry
  exact capture_reached recursiveGraph_typed invariant.2.1
    recursive_callback_reaches_own_request

theorem recursive_request_published :
    Run (Fin 1) old oldTypes saved.suspended
      FirstRef recursiveGraph recursiveTypes recursiveSaved.suspended
      [recursiveSaved, saved.map Sum.inl] :=
  .publish recursiveSaved
    (run_internal_prefix recursive_callback_answers_old_entry
      recursive_callback_reaches_own_request)

def secondCaptures : Nat → Value FirstRef Empty := fun _ => .unit
def secondRhs : Fin 1 → Value FirstRef Empty := fun _ => .unit
def secondFresh : Fin 1 → Value SecondRef Empty := sourceFresh secondCaptures secondRhs

theorem secondCaptures_typed : CapturesTyped recursiveTypes emptyContext secondCaptures := by
  intro i a h
  cases h

theorem secondRhs_typed (s : Fin 1) :
    ValueTyped recursiveTypes emptyTy
      (sourceContext (fun _ : Fin 1 => unitTy) emptyContext) (secondRhs s) unitTy := .unit

def secondGraph : Graph SecondRef := allocate recursiveGraph secondFresh
def secondTypes : SecondRef → Ty := joinTy recursiveTypes (fun _ => unitTy)

theorem secondGraph_typed : WellTyped secondGraph secondTypes :=
  allocate_typed recursiveGraph_typed _
    (sourceFresh_typed secondRhs_typed secondCaptures_typed)

theorem secondFresh_noCycle : FreshNoCycle secondFresh :=
  GuardedValueGraph.FiniteDecision.noCycle_of_terminal (fun _ => rfl)

def secondGraph_guard : GuardedValueGraph.Guarded (projectGraph secondGraph) :=
  allocationGuard recursiveGraph_guard _ secondFresh_noCycle

def secondEmbedding : Embedding recursiveGraph recursiveTypes secondGraph secondTypes :=
  sourceEmbedding recursiveGraph recursiveTypes (fun _ : Fin 1 => unitTy)
    secondCaptures secondRhs

def secondArena : List (Saved SecondRef) :=
  [recursiveSaved.map Sum.inl, (saved.map Sum.inl).map Sum.inl]

/-- The second allocation is also an actual source RHS allocation. Both
published entries survive with their own transported payloads and code. -/
theorem second_source_extension :
    Run (Fin 1) old oldTypes saved.suspended
      SecondRef secondGraph secondTypes
      ((recursiveSaved.map Sum.inl).suspended) secondArena := by
  exact run_source_extension recursive_request_published recursiveGraph_typed
    secondRhs secondRhs_typed secondCaptures secondCaptures_typed

def transportedResponse : Value SecondRef Empty := .ref (.inl (.inr 0))

theorem transportedResponse_typed :
    ValueTyped secondTypes emptyTy emptyContext transportedResponse callableTy := .ref _

/-- Reuse the original operation-73 entry, not the later operation-75 entry. -/
theorem original_entry_reused :
    Run (Fin 1) old oldTypes saved.suspended SecondRef secondGraph secondTypes
      (((saved.map Sum.inl).map Sum.inl).resume transportedResponse) secondArena := by
  apply Run.answer second_source_extension
  · exact List.mem_cons.mpr (.inr (List.mem_cons.mpr (.inl rfl)))
  · exact .matched (s := (saved.map Sum.inl).map Sum.inl)
      operation rfl transportedResponse
  · exact transportedResponse_typed

/-- Transport of the established raw trace proves a second appearance of
operation 75 after reuse. This states no unbounded recurrence property. -/
theorem reused_entry_reaches_own_request :
    Prefix secondGraph
      (((saved.map Sum.inl).map Sum.inl).resume transportedResponse)
      (recursiveEvents.map (mapEvent Sum.inl))
      ((recursiveSaved.map Sum.inl).suspended) := by
  change Prefix secondGraph
    (((saved.map Sum.inl).map Sum.inl).resume (mapValue Sum.inl recursiveResponse))
    (recursiveEvents.map (mapEvent Sum.inl))
    (mapComp Sum.inl recursiveSaved.suspended)
  rw [saved_map_resume]
  exact map_prefix secondEmbedding recursive_callback_reaches_own_request

def embedFirstRef : FirstRef → SecondRef := Sum.inl

theorem transported_endpoint_own_payload :
    (recursiveSaved.map embedFirstRef).payload = .ref (embedFirstRef (.inr (0 : Fin 1))) := rfl

/-- Actual graph guards cover every finite prefix after the original answer. -/
theorem first_answer_every_prefix_safe
    {trace : List (Event FirstRef)} {last : Comp FirstRef Empty}
    (steps : Prefix recursiveGraph ((saved.map Sum.inl).resume recursiveResponse) trace last) :
    CompTyped recursiveTypes emptyTy emptyContext last unitTy ∧
      CanProgress recursiveGraph last := recursive_callback_prefix_safe steps

/-- Every finite prefix after reuse retains the original result type and all
saved-entry typings. The guard is constructed for this second actual graph. -/
theorem reused_entry_every_prefix_safe
    {trace : List (Event SecondRef)} {last : Comp SecondRef Empty}
    (steps : Prefix secondGraph
      (((saved.map Sum.inl).map Sum.inl).resume transportedResponse) trace last) :
    CompTyped secondTypes emptyTy emptyContext last unitTy ∧
      CanProgress secondGraph last ∧
      (∀ s, s ∈ secondArena → SavedTyped secondTypes s unitTy) :=
  run_prefix_safety old_typed saved_actual_request original_entry_reused
    secondGraph_guard steps

end YulangClosure.HandlerGraph.Combined.RecursiveTrace
