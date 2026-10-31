import YulangClosure.FormalPermissionConnectedCuts

/-! R14 source-directed control flow for lib.rs::with_term_events. Nat payloads
are opaque observations, including errors and the returned Term. In particular,
arena contents are distinct from the returned Term. No input certifies Rust
execution, constructor correctness or resource availability. Test-only fields
are identities, not production effects. -/
namespace YulangClosure.FormalPermissionTermCallControl
open FormalPermissionSourceOrigin FormalPermissionCaptureConstruction
open FormalPermissionConstructorRealization FormalPermissionExportWitness
open FormalPermissionSiteTraversal FormalPermissionSourceAllocation
open FormalPermissionSourceInstance FormalPermissionHelperFrames
open FormalPermissionConnectedCuts
noncomputable section

structure ConstructorOutcome where
  terms : Nat
  result : Except Nat Nat

/-- One ordered snapshot and the supplied sampler outcome. counters is the
sampler-owned production counter state even on failure; failure is permitted
after partial sampler writes. Availability is not inferred. -/
structure EventOutcome where
  snapshot : Nat
  counters : List Nat
  result : Except Nat Unit

def snapshots (events : List EventOutcome) : List Nat := events.map EventOutcome.snapshot

def mapConstructor (errorMap : Nat → Nat) : Except Nat Nat → Except Nat Nat
  | .ok term => .ok term
  | .error error => .error (errorMap error)

/-- Only production counters are written here. R12's extra sampleResult
fields are copied from the current state, preserving test instrumentation. -/
def sampleState (event : EventOutcome) (s : HelperState) : HelperState :=
  {s with routeAttemptPhysicalChange := true, executionCounters := event.counters}

def sampleOps (event : EventOutcome) (s : HelperState) : List HelperOp :=
  [.physicalChange, .sampleResult event.counters s.resourceBoundarySamples
    s.resourceLedger s.f5cMatrixObserver]

theorem sample_ops_refine (event : EventOutcome) (s : HelperState) :
    runOps (sampleOps event s) s = sampleState event s := by
  cases s
  rfl

theorem run_ops_append (xs ys : List HelperOp) (s : HelperState) :
    runOps (xs ++ ys) s = runOps ys (runOps xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (applyOp x s)

/-- Stop at the first failure, retaining its counter delta and failure flag.
The unvisited suffix contributes neither operations nor state updates. -/
def loopOps : List EventOutcome → HelperState → List HelperOp
  | [], _ => []
  | event :: rest, s =>
      sampleOps event s ++ match event.result with
        | .error _ => [.eventSampleFailed]
        | .ok _ => loopOps rest (sampleState event s)

def loopState : List EventOutcome → HelperState → HelperState
  | [], s => s
  | event :: rest, s =>
      match event.result with
      | .error _ => applyOp .eventSampleFailed (sampleState event s)
      | .ok _ => loopState rest (sampleState event s)

def loopError : List EventOutcome → Option Nat
  | [] => none
  | event :: rest =>
      match event.result with
      | .error error => some error
      | .ok _ => loopError rest

theorem loop_ops_refine (events : List EventOutcome) (s : HelperState) :
    runOps (loopOps events s) s = loopState events s := by
  induction events generalizing s with
  | nil => rfl
  | cons event rest ih =>
      cases h : event.result <;>
        simp only [loopOps, loopState, h, run_ops_append, sample_ops_refine,
          runOps, ih]

def drained (constructor : ConstructorOutcome) (events : List EventOutcome)
    (s : HelperState) : HelperState :=
  applyOp .takeCapacityEvents (applyOp (.termConstructor constructor.terms (snapshots events)) s)

def controlOps (constructor : ConstructorOutcome) (events : List EventOutcome)
    (accounting : Bool) (s : HelperState) : List HelperOp :=
  .termConstructor constructor.terms (snapshots events) :: .takeCapacityEvents ::
    (if accounting then loopOps events (drained constructor events s) else [])

def controlState (constructor : ConstructorOutcome) (events : List EventOutcome)
    (accounting : Bool) (s : HelperState) : HelperState :=
  if accounting then loopState events (drained constructor events s)
  else drained constructor events s

def controlResult (errorMap : Nat → Nat) (constructor : ConstructorOutcome)
    (events : List EventOutcome) (accounting : Bool) : Except Nat Nat :=
  if accounting then
    match loopError events with
    | some error => .error error
    | none => mapConstructor errorMap constructor.result
  else mapConstructor errorMap constructor.result

theorem control_ops_refine (constructor : ConstructorOutcome) (events : List EventOutcome)
    (accounting : Bool) (s : HelperState) :
    runOps (controlOps constructor events accounting s) s =
      controlState constructor events accounting s := by
  cases accounting <;>
    simp [controlOps, controlState, runOps, drained, loop_ops_refine]

theorem no_accounting (errorMap : Nat → Nat) (constructor : ConstructorOutcome)
    (events : List EventOutcome) (s : HelperState) :
    controlOps constructor events false s =
      [.termConstructor constructor.terms (snapshots events), .takeCapacityEvents] ∧
    controlResult errorMap constructor events false = mapConstructor errorMap constructor.result := by
  exact ⟨rfl, rfl⟩

def AllSamplesOk (events : List EventOutcome) : Prop :=
  ∀ event ∈ events, event.result = .ok ()

theorem loop_error_none (events : List EventOutcome) (success : AllSamplesOk events) :
    loopError events = none := by
  revert success
  induction events with
  | nil => intro _; rfl
  | cons event rest ih =>
      intro success
      have head := success event (by simp)
      have tail : AllSamplesOk rest := fun e he => success e (by simp [he])
      simp only [loopError, head, ih tail]

/-- Constructor errors survive when all samples succeed, including zero events. -/
theorem constructor_error_preserved (errorMap : Nat → Nat) (constructor : ConstructorOutcome)
    (events : List EventOutcome) (accounting : Bool) (error : Nat)
    (failed : constructor.result = .error error) (success : AllSamplesOk events) :
    controlResult errorMap constructor events accounting = .error (errorMap error) := by
  cases accounting <;>
    simp [controlResult, loop_error_none events success, failed, mapConstructor]

theorem loop_first_error (before after : List EventOutcome) (failedEvent : EventOutcome)
    (error : Nat) (success : AllSamplesOk before)
    (failed : failedEvent.result = .error error) :
    loopError (before ++ failedEvent :: after) = some error := by
  revert success
  induction before with
  | nil => intro _; simp only [List.nil_append, loopError, failed]
  | cons event rest ih =>
      intro success
      have head := success event (by simp)
      have tail : AllSamplesOk rest := fun e he => success e (by simp [he])
      simpa only [List.cons_append, loopError, head] using ih tail

/-- Sample error takes precedence over either constructor outcome. -/
theorem sample_error_precedence (errorMap : Nat → Nat) (constructor : ConstructorOutcome)
    (before after : List EventOutcome) (failedEvent : EventOutcome) (error : Nat)
    (success : AllSamplesOk before) (failed : failedEvent.result = .error error) :
    controlResult errorMap constructor (before ++ failedEvent :: after) true = .error error := by
  simp only [controlResult, if_true, loop_first_error before after failedEvent error success failed]

/-- Immediate failure does not execute the suffix, even for an arena error. -/
theorem first_failure_stops (event : EventOutcome) (rest : List EventOutcome)
    (s : HelperState) (error : Nat) (failed : event.result = .error error) :
    loopOps (event :: rest) s = sampleOps event s ++ [.eventSampleFailed] ∧
    loopState (event :: rest) s = applyOp .eventSampleFailed (sampleState event s) := by
  simp only [loopOps, loopState, failed, and_self]

theorem successful_event_order (event : EventOutcome) (rest : List EventOutcome)
    (s : HelperState) (success : event.result = .ok ()) :
    loopOps (event :: rest) s = sampleOps event s ++ loopOps rest (sampleState event s) := by
  simp only [loopOps, success]

/-- These are successful outcome observations, not a constructor/sampler
availability theorem. All sampler outcomes are explicit even if accounting is off. -/
structure SuccessfulInput where
  constructor : ConstructorOutcome
  events : List EventOutcome
  accounting : Bool
  term : Nat
  constructorOk : constructor.result = .ok term
  samplesOk : AllSamplesOk events

def successfulTermCall (input : SuccessfulInput) (s : HelperState) : TermCall :=
  ⟨input.constructor.terms, snapshots input.events,
    if input.accounting then loopOps input.events (drained input.constructor input.events s) else []⟩

theorem successful_term_call (input : SuccessfulInput) (s : HelperState)
    (errorMap : Nat → Nat) :
    (successfulTermCall input s).ops =
      controlOps input.constructor input.events input.accounting s ∧
    runOps (successfulTermCall input s).ops s =
      controlState input.constructor input.events input.accounting s ∧
    controlResult errorMap input.constructor input.events input.accounting = .ok input.term := by
  refine ⟨rfl, control_ops_refine _ _ _ _, ?_⟩
  cases input.accounting <;>
    simp [controlResult, loop_error_none input.events input.samplesOk,
      input.constructorOk, mapConstructor]

private theorem sample_path (event : EventOutcome) (s : HelperState) :
    (sampleState event s).path = s.path := rfl

theorem loop_path (events : List EventOutcome) (s : HelperState) :
    (loopState events s).path = s.path := by
  induction events generalizing s with
  | nil => rfl
  | cons event rest ih =>
      cases h : event.result <;>
        simp only [loopState, h, applyOp, ih, sample_path]

/-- cfg(test) instrumentation is deliberately observed but never updated. -/
def testFields (s : HelperState) :=
  (s.incomingTermEventCount, s.incomingTermEventSnapshots, s.incomingRouteSampleAttempts,
    s.resourceBoundarySamples, s.resourceLedger, s.f5cMatrixObserver)

theorem loop_test_fields (events : List EventOutcome) (s : HelperState) :
    testFields (loopState events s) = testFields s := by
  induction events generalizing s with
  | nil => rfl
  | cons event rest ih =>
      cases h : event.result with
      | error error => simp only [loopState, h]; rfl
      | ok unit =>
          simpa only [loopState, h] using
            (ih (sampleState event s)).trans (show testFields (sampleState event s) = testFields s from rfl)

theorem control_test_fields (constructor : ConstructorOutcome) (events : List EventOutcome)
    (accounting : Bool) (s : HelperState) :
    testFields (controlState constructor events accounting s) = testFields s := by
  cases accounting <;> simp [controlState, loop_test_fields, drained, applyOp, testFields]

theorem control_preserves_allocator_path (constructor : ConstructorOutcome)
    (events : List EventOutcome) (accounting : Bool) (s : HelperState) :
    (controlState constructor events accounting s).allocator = s.allocator ∧
    (controlState constructor events accounting s).path = s.path := by
  refine ⟨?_, ?_⟩
  · rw [← control_ops_refine]
    exact operations_preserve_allocator _ _
  · cases accounting <;> simp [controlState, loop_path, drained, applyOp]

structure SuccessfulPair where
  positive : SuccessfulInput
  negative : SuccessfulInput

def SuccessfulPair.port (input : SuccessfulPair) (s : HelperState) : Call .portCompletion :=
  let positive := successfulTermCall input.positive s
  .port positive (successfulTermCall input.negative (runOps positive.ops s))

def SuccessfulPair.function (input : SuccessfulPair) (s : HelperState) : Call .functionCompletion :=
  let positive := successfulTermCall input.positive s
  .function positive (successfulTermCall input.negative (runOps positive.ops s))

def SuccessfulPair.tuple (input : SuccessfulPair) (s : HelperState) : Call .tupleCompletion :=
  let positive := successfulTermCall input.positive s
  .tuple positive (successfulTermCall input.negative (runOps positive.ops s))

theorem successful_pair_refines (input : SuccessfulPair) (s : HelperState) :
    runOps (input.port s).ops s =
      controlState input.negative.constructor input.negative.events input.negative.accounting
        (controlState input.positive.constructor input.positive.events input.positive.accounting s) ∧
    (input.function s).ops = (input.port s).ops ∧
    (input.tuple s).ops = (input.port s).ops := by
  refine ⟨?_, rfl, rfl⟩
  simp only [SuccessfulPair.port, Call.ops, run_ops_append]
  rw [(successful_term_call input.positive s id).2.1]
  exact (successful_term_call input.negative _ id).2.1

/-- Eight paired term-call cuts, all generated; leaves are fixed cached reads.
Capacity/backing observations remain the existing explicit R13 inputs. -/
structure SourceCalls where
  firstArgumentPort : SuccessfulPair
  firstResultPort : SuccessfulPair
  firstTerms : SuccessfulPair
  secondArgumentPort : SuccessfulPair
  secondResultPort : SuccessfulPair
  secondTerms : SuccessfulPair
  innerTuple : SuccessfulPair
  rootTuple : SuccessfulPair
  firstPathCapacity : Nat
  firstConcreteCapacity : Nat
  firstBacking : Nat
  secondPathCapacity : Nat
  secondConcreteCapacity : Nat
  secondBacking : Nat

/-- Reproduce connect's state threading to generate each transcript at its
actual entry state. No Call, handling list, frame or endpoint is an input. -/
def sourceCalls (inputs : SourceCalls) (initial : HelperState) (level : Nat) : Calls :=
  let n := initial.allocator.bounds.length
  let c1 := enter [.element 0, .argument] initial
  let c2 := enter FormalPermissionAuthenticatedNativeDecode.firstPath (finish .leaf c1)
  let c3 := birth level (enter [.element 0, .argument] (finish .leaf c2))
  let argumentPort := inputs.firstArgumentPort.port c3
  let c4 := prepareAppend (firstEntry n) inputs.firstPathCapacity inputs.firstConcreteCapacity inputs.firstBacking
    (birth level (enter FormalPermissionAuthenticatedNativeDecode.firstPath (finish argumentPort c3)))
  let resultPort := inputs.firstResultPort.port c4
  let c5 := enter [.element 0] (finish resultPort c4)
  let terms := inputs.firstTerms.function c5
  let c6 := enter [.element 1, .element 0] (finish terms c5)
  let c7 := enter [.element 1, .element 1, .argument] (finish .leaf c6)
  let c8 := enter FormalPermissionAuthenticatedNativeDecode.secondPath (finish .leaf c7)
  let c9 := birth level (enter [.element 1, .element 1, .argument] (finish .leaf c8))
  let argumentPort2 := inputs.secondArgumentPort.port c9
  let c10 := prepareAppend (secondEntry n) inputs.secondPathCapacity inputs.secondConcreteCapacity inputs.secondBacking
    (birth level (enter FormalPermissionAuthenticatedNativeDecode.secondPath (finish argumentPort2 c9)))
  let resultPort2 := inputs.secondResultPort.port c10
  let c11 := enter [.element 1, .element 1] (finish resultPort2 c10)
  let terms2 := inputs.secondTerms.function c11
  let c12 := enter [.element 1] (finish terms2 c11)
  let tuple := inputs.innerTuple.tuple c12
  let c13 := enter [] (finish tuple c12)
  { firstArgument := .leaf, firstResult := .leaf,
    firstArgumentPort := argumentPort, firstResultPort := resultPort, firstTerms := terms,
    innerInt := .leaf, secondArgument := .leaf, secondResult := .leaf,
    secondArgumentPort := argumentPort2, secondResultPort := resultPort2, secondTerms := terms2,
    innerTuple := tuple, rootTuple := inputs.rootTuple.tuple c13,
    firstPathCapacity := inputs.firstPathCapacity, firstConcreteCapacity := inputs.firstConcreteCapacity,
    firstBacking := inputs.firstBacking, secondPathCapacity := inputs.secondPathCapacity,
    secondConcreteCapacity := inputs.secondConcreteCapacity, secondBacking := inputs.secondBacking }

theorem source_calls_at_cuts (inputs : SourceCalls) (initial : HelperState) (level : Nat) :
    let calls := sourceCalls inputs initial level
    let t := connect calls initial level
    calls.firstArgumentPort = inputs.firstArgumentPort.port t.c3 ∧
    calls.firstResultPort = inputs.firstResultPort.port t.c4 ∧
    calls.firstTerms = inputs.firstTerms.function t.c5 ∧
    calls.secondArgumentPort = inputs.secondArgumentPort.port t.c9 ∧
    calls.secondResultPort = inputs.secondResultPort.port t.c10 ∧
    calls.secondTerms = inputs.secondTerms.function t.c11 ∧
    calls.innerTuple = inputs.innerTuple.tuple t.c12 ∧
    calls.rootTuple = inputs.rootTuple.tuple t.c13 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Apply the generated calls to R13's same source derivation and R9 output.
Reservations, primitive authenticity and execution linkage remain external. -/
theorem exact_tree_r9_from_term_control (s : State) (initial : HelperState) (level : Nat)
    (length : initial.allocator.bounds.length = s.nextEffect)
    (aligned : Aligned initial.allocator) (ready : Reservations initial.allocator level)
    (inputs : SourceCalls) :
    ∃ out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s,
      SourcePair FormalPermissionAuthenticatedNativeDecode.context false FormalPermissionAuthenticatedNativeDecode.tree (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out ∧
      out = FormalPermissionAuthenticatedNativeDecode.output s 0 1 ∧ out.entries = FormalPermissionAuthenticatedNativeDecode.retained s.nextEffect ∧
      out.births = [s.nextEffect, s.nextEffect + 1, s.nextEffect + 2, s.nextEffect + 3] ∧
      out.state = {s with nextEffect := s.nextEffect + 4} ∧
      Aligned (afterFour initial.allocator level) ∧
      (afterFour initial.allocator level).permissions = initial.allocator.permissions ++ out.entries :=
  exact_tree_r9_from_connected s initial level length aligned ready (sourceCalls inputs initial level)

end
end YulangClosure.FormalPermissionTermCallControl
