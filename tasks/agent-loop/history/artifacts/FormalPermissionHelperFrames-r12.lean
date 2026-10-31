import YulangClosure.FormalPermissionSourceInstance

/-! R12 operation-footprint transcription. Opaque Nat/List Nat payloads stand
for term arena and accounting contents, not an implementation of those APIs.
Every permitted operation explicitly updates its owning fields. A program is
an operation transcript, not evidence of a successful Rust return. Source-to-
transcript, alias/primitive-library and path-projection correspondence remain
external. Permission append is deliberately absent from HelperOp. -/
namespace YulangClosure.FormalPermissionHelperFrames
open FormalPermissionSourceOrigin FormalPermissionCaptureConstruction
open FormalPermissionConstructorRealization FormalPermissionExportWitness
open FormalPermissionSiteTraversal FormalPermissionSourceAllocation
open FormalPermissionSourceInstance
noncomputable section

/-- Capacity storage is separate from all vector contents. Lane identifies
which capacity changes; it never authorizes a row append. -/
inductive CapacityLane where
  | effectBounds | effectLevels | effectMetadata | effectMarks
  | localPermissions | retainedPath | concrete | positiveTuple | negativeTuple
  deriving DecidableEq

/-- Actual mutated field families, with opaque contents where only a write
footprint is justified. `allocator.permissions` is the operation-local Vec,
not the graph's published formal_permissions map. Test-only thread-local
instrumentation and error payloads are not execution-modeled here. -/
structure HelperState where
  allocator : Allocator
  capacities : CapacityLane → Nat
  storeTerms : Nat
  termCapacityEvents : List Nat
  routeAttemptPhysicalChange : Bool
  incomingRouteEventSampleFailed : Bool
  incomingTermEventCount : Nat
  incomingTermEventSnapshots : List Nat
  incomingRouteSampleAttempts : Nat
  executionCounters : List Nat
  resourceBoundarySamples : List Nat
  resourceLedger : List Nat
  f5cMatrixObserver : List Nat
  graphScratchBytes : Nat
  permissionNestedBytes : Nat
  scratchBytes : Nat
  retainedPath : List Step
  concrete : List Nat
  positiveTuple : List Nat
  negativeTuple : List Nat
  path : List Step

/-- `with_term_events` lends only the term arena to its constructor. Sample
writes are separately listed; opaque results do not receive the allocator. -/
inductive HelperOp where
  | collectedLeafRead
  | termConstructor (terms : Nat) (capacityEvents : List Nat)
  | takeCapacityEvents
  | physicalChange
  | eventSampleFailed
  | eventSnapshot (snapshots : List Nat)
  | sampleAttempt
  | sampleResult (counters samples ledger observer : List Nat)
  | reserveCapacity (lane : CapacityLane) (capacity : Nat)
  | copyRetainedPath (path : List Step)
  | copyConcrete (concrete : List Nat)
  | chargePermissionBacking (bytes : Nat)
  | tupleBuffers (positive negative : List Nat)
  | setPath (path : List Step)
  | releaseTupleScratch (bytes : Nat)

/-- These are write effects after the corresponding Rust checks, if reached.
Nat arithmetic here does not claim machine-size arithmetic/check success. -/
def applyOp (op : HelperOp) (s : HelperState) : HelperState :=
  match op with
  | .collectedLeafRead => s
  | .termConstructor terms events =>
      {s with storeTerms := terms, termCapacityEvents := events}
  | .takeCapacityEvents => {s with termCapacityEvents := []}
  | .physicalChange => {s with routeAttemptPhysicalChange := true}
  | .eventSampleFailed => {s with incomingRouteEventSampleFailed := true}
  | .eventSnapshot snapshots =>
      {s with incomingTermEventCount := s.incomingTermEventCount + 1, incomingTermEventSnapshots := snapshots}
  | .sampleAttempt => {s with incomingRouteSampleAttempts := s.incomingRouteSampleAttempts + 1}
  | .sampleResult counters samples ledger observer =>
      {s with executionCounters := counters, resourceBoundarySamples := samples, resourceLedger := ledger, f5cMatrixObserver := observer}
  | .reserveCapacity lane capacity =>
      {s with capacities := fun selected => if selected = lane then capacity else s.capacities selected}
  | .copyRetainedPath path => {s with retainedPath := path}
  | .copyConcrete concrete => {s with concrete := concrete}
  | .chargePermissionBacking bytes =>
      {s with graphScratchBytes := s.graphScratchBytes + bytes, permissionNestedBytes := s.permissionNestedBytes + bytes, scratchBytes := s.scratchBytes + bytes}
  | .tupleBuffers positive negative => {s with positiveTuple := positive, negativeTuple := negative}
  | .setPath path => {s with path := path}
  | .releaseTupleScratch bytes => {s with graphScratchBytes := s.graphScratchBytes - bytes}

def runOps : List HelperOp → HelperState → HelperState
  | [], s => s
  | op :: rest, s => runOps rest (applyOp op s)

/-- Every operation preserves the entire four-vector/permission data, which
implies the weaker R11 count projection. No endpoint equality is a premise. -/
theorem operation_preserves_allocator (op : HelperOp) (s : HelperState) :
    (applyOp op s).allocator = s.allocator := by
  cases op <;> rfl

theorem operations_preserve_allocator (ops : List HelperOp) (s : HelperState) :
    (runOps ops s).allocator = s.allocator := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih => exact (ih (applyOp op s)).trans (operation_preserves_allocator op s)

/-- Arbitrary preexisting permission priorPermissions is retained. Dropping its length
only selects the local suffix; no path, metadata or row is rewritten. -/
def localProjection (priorPermissions : List Retained) (s : HelperState) : Projection :=
  ⟨s.allocator.bounds.length, s.allocator.permissions.drop priorPermissions.length⟩

private theorem op_projection (op : HelperOp) (priorPermissions : List Retained) (s : HelperState) :
    localProjection priorPermissions (applyOp op s) = localProjection priorPermissions s := by
  unfold localProjection
  rw [operation_preserves_allocator]

private theorem program_frame (ops : List HelperOp) (priorPermissions : List Retained) (s : HelperState) :
    HelperFrames (localProjection priorPermissions s) (localProjection priorPermissions (runOps ops s)) := by
  induction ops generalizing s with
  | nil => exact .nil _
  | cons op rest ih =>
      have same := op_projection op priorPermissions s
      exact .cons (congrArg Projection.effectLength same).symm
        (congrArg Projection.permissions same).symm (ih (applyOp op s))

/-- Public lifting requires a genuinely nonempty operation transcript. Its
base case closes only the interpreted tail, never an unknown native call. -/
theorem nonempty_operations_frame (first : HelperOp) (rest : List HelperOp)
    (priorPermissions : List Retained) (s : HelperState) :
    HelperFrames (localProjection priorPermissions s)
      (localProjection priorPermissions (runOps (first :: rest) s)) :=
  program_frame (first :: rest) priorPermissions s

/-- Reservation is a capacity write, not a successful reserve witness and
not an allocator push. Contents, length and permissions are unchanged. -/
theorem reservation_projection (s : HelperState) (lane : CapacityLane) (capacity : Nat) :
    (applyOp (.reserveCapacity lane capacity) s).capacities lane = capacity ∧
    (applyOp (.reserveCapacity lane capacity) s).allocator = s.allocator := by
  exact ⟨by simp [applyOp], operation_preserves_allocator _ _⟩

/-- The designated local permission append is outside HelperOp. -/
def pushPermission (s : HelperState) (entry : Retained) : HelperState :=
  {s with allocator := {s.allocator with permissions := s.allocator.permissions ++ [entry]}}

theorem permission_append_delta (s : HelperState) (entry : Retained) :
    (pushPermission s entry).allocator.bounds = s.allocator.bounds ∧
    (pushPermission s entry).allocator.permissions = s.allocator.permissions ++ [entry] := by
  exact ⟨rfl, rfl⟩

/-- Explicit source order before the designated permission append. Capacity
payloads and byte counts are observations to be justified by the execution
bridge, not successful reserve/arithmetic witnesses. The exact entry supplies
the path and concrete members copied; no metadata/path is replaced. -/
def concretePreparation (entry : Retained) (pathCapacity concreteCapacity backing : Nat) :
    List HelperOp :=
  [.reserveCapacity .retainedPath pathCapacity, .copyRetainedPath entry.path,
    .reserveCapacity .concrete concreteCapacity, .copyConcrete entry.metadata.concrete,
    .chargePermissionBacking backing]

/-- Copy/accounting priorPermissions; one designated append; completion suffix. This
claims an append delta for the combined segment, never a frame for append. -/
theorem concrete_port_prefix_delta (before after : List HelperOp)
    (s : HelperState) (entry : Retained) :
    (runOps after (pushPermission (runOps before s) entry)).allocator.bounds = s.allocator.bounds ∧
    (runOps after (pushPermission (runOps before s) entry)).allocator.permissions =
      s.allocator.permissions ++ [entry] := by
  rw [operations_preserve_allocator]
  simp only [pushPermission]
  rw [operations_preserve_allocator]
  exact ⟨rfl, rfl⟩

/-- Ordered concrete preparation and completion retain the full arbitrary
permission priorPermissions and append exactly the same designated record. -/
theorem ordered_concrete_port_delta (entry : Retained)
    (pathCapacity concreteCapacity backing : Nat) (after : List HelperOp) (s : HelperState) :
    (runOps after (pushPermission
      (runOps (concretePreparation entry pathCapacity concreteCapacity backing) s) entry)).allocator.bounds =
        s.allocator.bounds ∧
    (runOps after (pushPermission
      (runOps (concretePreparation entry pathCapacity concreteCapacity backing) s) entry)).allocator.permissions =
        s.allocator.permissions ++ [entry] :=
  concrete_port_prefix_delta (concretePreparation entry pathCapacity concreteCapacity backing) after s entry

/-- Term construction result plus the explicitly supplied event processing
transcript. No assertion of callback correctness, event count or success. -/
structure TermCall where
  terms : Nat
  events : List Nat
  handling : List HelperOp

def TermCall.ops (call : TermCall) : List HelperOp :=
  .termConstructor call.terms call.events :: .takeCapacityEvents :: call.handling

inductive CallKind where
  | leaf | portCompletion | functionCompletion | tupleCompletion

/-- Intended call shape is recorded separately from execution authenticity.
Leaf calls read two cached terms. Other cuts execute two arena calls. -/
inductive Call : CallKind → Type where
  | leaf : Call .leaf
  | port (positive negative : TermCall) : Call .portCompletion
  | function (positive negative : TermCall) : Call .functionCompletion
  | tuple (positive negative : TermCall) : Call .tupleCompletion

def Call.ops {kind : CallKind} : Call kind → List HelperOp
  | .leaf => [.collectedLeafRead, .collectedLeafRead]
  | .port positive negative => positive.ops ++ negative.ops
  | .function positive negative => positive.ops ++ negative.ops
  | .tuple positive negative => positive.ops ++ negative.ops

private theorem call_nonempty {kind : CallKind} (call : Call kind) : call.ops ≠ [] := by
  cases call <;> simp [Call.ops, TermCall.ops]

/-- Data at an individual cut: entry coordinates and a nonempty operation
program. There is no target-state equality, HelperFrames or success premise.
The priorPermissions and suffix are exact retained records, including their paths. -/
structure Cut (kind : CallKind) (n : Nat) (entries : List Retained) where
  initial : HelperState
  priorPermissions : List Retained
  rowsAtEntry : initial.allocator.bounds.length = n
  permissionsAtEntry : initial.allocator.permissions = priorPermissions ++ entries
  call : Call kind

private theorem cut_frame {kind : CallKind} {n : Nat} {entries : List Retained}
    (cut : Cut kind n entries) : Frame n entries := by
  obtain ⟨first, rest, transcript⟩ : ∃ first rest, cut.call.ops = first :: rest := by
    cases h : cut.call.ops with
    | nil => exact False.elim (call_nonempty cut.call h)
    | cons first rest => exact ⟨first, rest, rfl⟩
  have frame := nonempty_operations_frame first rest cut.priorPermissions cut.initial
  rw [← transcript] at frame
  have initial : localProjection cut.priorPermissions cut.initial = (⟨n, entries⟩ : Projection) := by
    simp only [localProjection, cut.rowsAtEntry, cut.permissionsAtEntry, List.drop_left]
  have final : localProjection cut.priorPermissions (runOps cut.call.ops cut.initial) =
      localProjection cut.priorPermissions cut.initial := by
    unfold localProjection
    rw [operations_preserve_allocator]
  rw [final, initial] at frame
  exact frame

/-- Thirteen local operation witnesses, following R11's sequential cuts.
These are operation programs with concrete write footprints, not endpoint
frame equalities. Linking each program to an actual Rust call is still OPEN. -/
structure FunctionOperations (s : State) (row : SourceRow) where
  argument : Cut .leaf s.nextEffect []
  result : Cut .leaf s.nextEffect []
  argumentPort : Cut .portCompletion (s.nextEffect + 1) []
  resultPort : Cut .portCompletion (s.nextEffect + 1 + 1)
    [localEntry row [] (s.nextEffect + 1)]
  terms : Cut .functionCompletion (s.nextEffect + 1 + 1)
    [localEntry row [.result] (s.nextEffect + 1)]

structure TreeOperations (s : State) where
  first : FunctionOperations s FormalPermissionAuthenticatedNativeDecode.firstRow
  innerInt : Cut .leaf (s.nextEffect + 2) []
  second : FunctionOperations {s with nextEffect := s.nextEffect + 2}
    FormalPermissionAuthenticatedNativeDecode.secondRow
  innerTuple : Cut .tupleCompletion (s.nextEffect + 4)
    [localEntry FormalPermissionAuthenticatedNativeDecode.secondRow [.element 1, .result] (s.nextEffect + 3)]
  rootTuple : Cut .tupleCompletion (s.nextEffect + 4)
    (FormalPermissionAuthenticatedNativeDecode.retained s.nextEffect)

private def functionFrames {s : State} {row : SourceRow}
    (ops : FunctionOperations s row) : FunctionFrames s row :=
  ⟨cut_frame ops.argument, cut_frame ops.result, cut_frame ops.argumentPort,
    cut_frame ops.resultPort, cut_frame ops.terms⟩

/-- Only the operation-model frame obligations are discharged here. Native
program alignment, primitive behavior, allocation availability and publication
are not inferred from these data. -/
theorem tree_frames_from_operations (s : State) (ops : TreeOperations s) : TreeFrames s :=
  ⟨functionFrames ops.first, cut_frame ops.innerInt, functionFrames ops.second,
    cut_frame ops.innerTuple, cut_frame ops.rootTuple⟩

/-- Apply the supported frames to the same R11 source output/derivation and
R9 application. No native successful execution or initial ordinal is chosen. -/
theorem exact_tree_r9_from_operations (s : State) (a : Allocator) (level : Nat)
    (length : a.bounds.length = s.nextEffect) (aligned : Aligned a)
    (ready : Reservations a level) (ops : TreeOperations s) :
    ∃ out : ValueDecoded FormalPermissionAuthenticatedNativeDecode.context false s,
      SourcePair FormalPermissionAuthenticatedNativeDecode.context false
        FormalPermissionAuthenticatedNativeDecode.tree
        (FormalPermissionAuthenticatedNativeDecode.code 0 1) s out ∧
      out = FormalPermissionAuthenticatedNativeDecode.output s 0 1 ∧
      out.entries = FormalPermissionAuthenticatedNativeDecode.retained s.nextEffect ∧
      out.births = [s.nextEffect, s.nextEffect + 1, s.nextEffect + 2, s.nextEffect + 3] ∧
      out.state = {s with nextEffect := s.nextEffect + 4} ∧
      Aligned (afterFour a level) ∧
      (afterFour a level).permissions = a.permissions ++ out.entries :=
  exact_tree_r9_application s a level length aligned ready (tree_frames_from_operations s ops)

end
end YulangClosure.FormalPermissionHelperFrames
