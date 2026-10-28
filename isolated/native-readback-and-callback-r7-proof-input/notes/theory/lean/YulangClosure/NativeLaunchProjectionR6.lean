import Init

/-!
R6 candidate write-footprint model. CONSTRUCTED, UNCHECKED.
Baseline 7b3ad7074; contract 01236acb3ef9134788e58aa888ec7d498ddd24fa9f64250c4f1fc2837f03034a;
amendment 770332723483bb646936c71eb4bf7e83e9dfaf5ee6cf9898ff0bbefe98ff5296.

The immutable context input is native-launch-projection-r6-proof-input, hash
57114491a4b1333f30e3ad68cb6e1c8a5c735e2d142c1456745eaef8ed56f30e.
The lib input is native-launch-projection-r6, hash
ac3c0701958e82da2ce5174a3b52b1c02adfc8c93d582b68147a085e682a6d07.

This models the prefix ending BEFORE clear_diagnostic_scratch (lib:14196).
It does not model seed, transfer/enqueue, passive attribution or Running.
Resource arithmetic and allocation results are explicit nondeterministic data;
no theorem asserts that a particular successful result occurs. Resource payloads
are opaque record images. Their exact byte arithmetic and Rust-to-model
realization are OPEN, as is native identity encoding. The proved candidate
calculations concern write footprints, not concrete native execution.

Original parent: Contracts.SourceProblem.InferenceSoundness, preserving all
source/scope/constraint/solution quantifiers and ONE shared source witness.
No instance of that parent, NativeCorrespondence or LocalLaws is supplied.
No R5 declarations are imported or assumed.
-/
namespace YulangClosure.NativeLaunchProjectionR6

inductive Task where
  | value (lower upper : Nat)
  | effect (lower upper : Nat)
  deriving DecidableEq, Repr

structure Ack where
  operation : Nat
  index : Nat
  deriving DecidableEq, Repr

inductive Wait where
  | idle
  | running (ack : Ack) (index : Nat)
  | ready (ack : Ack) (index transitions : Nat)
  deriving DecidableEq, Repr

structure Operation where
  task : Task
  children : List Nat
  queued : Nat
  consumed : Nat
  retired : Bool
  waiting : Wait
  deriving DecidableEq, Repr

structure Item where
  task : Task
  relation : Option Nat
  ack : Option Ack
  deriving DecidableEq, Repr

/-- Only fields whose exact initial values occur in the prefix conclusion.
The full native frame and subsequent receipt semantics are not identified
with this record. Nat parameters denote abstract native handles, not source
syntax or a replacement source typing domain. -/
structure Frame where
  initial : Task
  occurrence : Nat
  cause : Nat
  previousProcessing : Option Nat
  previousRelation : Option Nat
  current : Option Item := none
  transportStage : Bool := true
  contextConsumed : Option Nat := none
  transitions : Nat := 0
  acks : List Ack := []
  completedAcks : Nat := 0
  preparedAcks : Nat := 0
  terminalPrepared : Bool := false
  functionDispatch : Option Nat := none
  tupleDispatch : Option Nat := none
  recordDispatch : Option Nat := none
  variantDispatch : Option Nat := none
  destination : Option Ack := none
  receipt : Option Nat := none
  deriving DecidableEq, Repr

structure Undo where
  id : Nat
  waiting : Wait
  queued : Nat
  consumed : Nat
  retired : Bool
  deriving DecidableEq, Repr

/-- Resource and instrumentation owners are retained, even when erased by pi.
Payload lists stand for complete counter/ledger/observer images. Their exact
computation is deliberately not claimed by the footprint theorem. -/
structure Resources where
  physicalChange : Bool := false
  sampleFailed : Bool := false
  sampleAttempts : Nat := 0
  sampledUndoCapacity : Nat := 0
  counters : List Nat := []
  ledger : List Nat := []
  sampleCount : Nat := 0
  trace : List Nat := []
  matrixObserver : Option (List Nat) := none
  deriving DecidableEq, Repr

structure State where
  operations : Nat → Option Operation
  frames : List Frame
  queue : List Item
  processing : Option Nat
  processingRelation : Option Nat
  journalPresent : Bool
  incomingActive : Bool
  undo : List Undo
  undoCapacity : Nat
  frameCapacity : Nat
  resources : Resources

/-- Exactly the evidence used by the bounded prefix readback below. -/
structure Projection where
  operations : Nat → Option Operation
  frames : List Frame
  queue : List Item
  processing : Option Nat
  processingRelation : Option Nat

def pi (s : State) : Projection :=
  ⟨s.operations, s.frames, s.queue, s.processing, s.processingRelation⟩

/-- Concrete resource-owner writes from lib:9253,10774,10821,11017 and
20414. Read-only arithmetic is not silently replaced by success. Observer
panic/Err exits are represented separately below. No constructor can write
operations, frames, worklist contents or processing. This restriction is a
source footprint candidate, still requiring independent correspondence review. -/
inductive ResourceWrite where
  | markPhysical
  | markFailed
  | attempt
  | undoPeak (capacity : Nat)
  | publishCounters (image : List Nat)
  | publishLedger (image : List Nat)
  | publishSamples (count : Nat)
  | traceEvent (event : Nat)
  | takeMatrix
  | restoreMatrix (image : List Nat)
  deriving Repr

def ResourceWrite.apply (w : ResourceWrite) (s : State) : State :=
  { s with resources := match w with
    | .markPhysical => { s.resources with physicalChange := true }
    | .markFailed => { s.resources with sampleFailed := true }
    | .attempt => { s.resources with sampleAttempts := s.resources.sampleAttempts + 1 }
    | .undoPeak n => { s.resources with sampledUndoCapacity := max s.resources.sampledUndoCapacity n }
    | .publishCounters a => { s.resources with counters := a }
    | .publishLedger a => { s.resources with ledger := a }
    | .publishSamples n => { s.resources with sampleCount := n }
    | .traceEvent n => { s.resources with trace := s.resources.trace ++ [n] }
    | .takeMatrix => { s.resources with matrixObserver := none }
    | .restoreMatrix a => { s.resources with matrixObserver := some a } }

def applyWrites (s : State) : List ResourceWrite → State
  | [] => s
  | w :: ws => applyWrites (w.apply s) ws

theorem resourceWrite_projection (s : State) (w : ResourceWrite) :
    pi (w.apply s) = pi s := by
  cases w <;> rfl

theorem resourceTrace_projection (s : State) (ws : List ResourceWrite) :
    pi (applyWrites s ws) = pi s := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    exact (ih (w.apply s)).trans (resourceWrite_projection s w)

inductive Exit where
  | returned | error | panicked
  deriving DecidableEq, Repr

/-- Sample outcome is data, not a successful-call premise. A native arithmetic
or instrumentation realization of this data remains outside the theorem. -/
structure SamplePlan where
  testing : Bool
  prepublicationExit : Exit
  counters : List Nat
  ledger : List Nat
  samples : Nat
  matrix : Option (List Nat)
  matrixPanics : Bool

structure CallbackResult where
  state : State
  exit : Exit

def sampleWrites (s : State) (p : SamplePlan) : List ResourceWrite :=
  (if p.testing then [.traceEvent 0, .attempt] ++
    (if s.journalPresent then [.undoPeak s.undoCapacity] else []) else []) ++
  (match p.prepublicationExit with
    | .error => []
    | .panicked => []
    | .returned =>
      (if p.testing then [.publishLedger p.ledger] else []) ++
      [.publishCounters p.counters] ++
      (if p.testing then [.publishSamples p.samples, .traceEvent 1] else []) ++
      (match p.matrix with
        | none => []
        | some image => [.takeMatrix] ++
            (if p.matrixPanics then [] else [.restoreMatrix image])))

def sampleExit (p : SamplePlan) : Exit :=
  match p.prepublicationExit with
  | .error => .error
  | .panicked => .panicked
  | .returned => if p.matrix.isSome && p.matrixPanics then .panicked else .returned

def sample (s : State) (p : SamplePlan) : CallbackResult :=
  ⟨applyWrites s (sampleWrites s p), sampleExit p⟩

theorem sample_projection (s : State) (p : SamplePlan) :
    pi (sample s p).state = pi s :=
  resourceTrace_projection s (sampleWrites s p)

/-- lib:9253 writes the physical flag BEFORE sampling, and the failure flag
only on Result::Err. A panic does not return through that Err handler. -/
def observeCapacity (s : State) (p : SamplePlan) : CallbackResult :=
  if s.incomingActive then
    let r := sample (ResourceWrite.markPhysical.apply s) p
    match r.exit with
    | .error => ⟨ResourceWrite.markFailed.apply r.state, .error⟩
    | .returned => r
    | .panicked => r
  else ⟨s, .returned⟩

theorem observeCapacity_projection (s : State) (p : SamplePlan) :
    pi (observeCapacity s p).state = pi s := by
  unfold observeCapacity
  split
  · cases h : (sample (ResourceWrite.markPhysical.apply s) p).exit <;>
      simp only [h] <;>
      first
      | exact (resourceWrite_projection _ .markFailed).trans
          ((sample_projection _ p).trans (resourceWrite_projection s .markPhysical))
      | exact (sample_projection _ p).trans (resourceWrite_projection s .markPhysical)
  · rfl

/-- Exact prepare_replay_ack append, context:2376. -/
def appendUndo (s : State) (id : Nat) (op : Operation) (capacity : Nat) : State :=
  { s with undoCapacity := capacity,
    undo := s.undo ++ [⟨id, op.waiting, op.queued, op.consumed, op.retired⟩] }

theorem appendUndo_projection (s : State) (id : Nat) (op : Operation) (capacity : Nat) :
    pi (appendUndo s id op capacity) = pi s := rfl

/-- Actual allocator outcome; None is reserve failure. Capacities are supplied
observations, not a theorem that any capacity or success is native-realizable. -/
structure PreparePlan where
  reserve : Option Nat
  sample : SamplePlan

inductive PrepareResult where
  | missing (s : State)
  | reserveFailed (s : State)
  | observed (s : State) (exit : Exit)

def PrepareResult.state : PrepareResult → State
  | .missing s => s
  | .reserveFailed s => s
  | .observed s _ => s

def prepare (s : State) (id : Nat) (p : PreparePlan) : PrepareResult :=
  match s.operations id with
  | none => .missing s
  | some op =>
    if s.journalPresent then
      match p.reserve with
      | none => .reserveFailed s
      | some capacity =>
        let t := appendUndo s id op capacity
        if capacity = s.undoCapacity then .observed t .returned
        else
          let r := if s.incomingActive then observeCapacity t p.sample else sample t p.sample
          .observed r.state r.exit
    else .observed s .returned

theorem prepare_projection (s : State) (id : Nat) (p : PreparePlan) :
    pi (prepare s id p).state = pi s := by
  unfold prepare
  cases lookup : s.operations id with
  | none => rfl
  | some op =>
    simp only [lookup]
    split
    · cases reservation : p.reserve with
      | none => rfl
      | some capacity =>
        simp only [reservation]
        split
        · rfl
        · split
          · exact (observeCapacity_projection _ p.sample).trans
              (appendUndo_projection s id op capacity)
          · exact (sample_projection _ p.sample).trans
              (appendUndo_projection s id op capacity)
    · rfl

/-- Context:2249 saves the two independent processing fields before clearing.
Every other listed field is initialized to its native launch value. -/
def newFrame (s : State) (item : Item) (occurrence cause : Nat) : Frame :=
  { initial := item.task, occurrence := occurrence, cause := cause,
    previousProcessing := s.processing, previousRelation := s.processingRelation }

def beginAndClearProcessing (s : State) (item : Item) (occurrence cause capacity : Nat) : State :=
  { s with frames := s.frames ++ [newFrame s item occurrence cause],
    frameCapacity := capacity, processing := none, processingRelation := none }

theorem beginAndClearProcessing_exact (s : State) (item : Item)
    (occurrence cause capacity : Nat) :
    (beginAndClearProcessing s item occurrence cause capacity).operations = s.operations ∧
    (beginAndClearProcessing s item occurrence cause capacity).queue = s.queue ∧
    (beginAndClearProcessing s item occurrence cause capacity).frames =
      s.frames ++ [newFrame s item occurrence cause] ∧
    (beginAndClearProcessing s item occurrence cause capacity).processing = none ∧
    (beginAndClearProcessing s item occurrence cause capacity).processingRelation = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Entry guards are computed, including failed lookup. No desired operation,
child, successful callback, frame reserve or driver return is an input premise.
The non-Idle and NoChild branches end at explicit out-of-scope boundaries. -/
inductive PrefixResult where
  | missingOperation (s : State)
  | otherWait (s : State)
  | cursorMismatch (s : State)
  | queueNonempty (s : State)
  | prepareError (s : State)
  | preparePanic (s : State)
  | noChildBoundary (s : State)
  | frameReserveError (s : State)
  | clearDiagnosticsBoundary (s : State) (index : Nat) (item : Item)

def runPrefix (s : State) (id occurrence cause : Nat)
    (p : PreparePlan) (frameReserve : Option Nat) : PrefixResult :=
  match s.operations id with
  | none => .missingOperation s
  | some op =>
    match op.waiting with
    | .running _ _ => .otherWait s
    | .ready _ _ _ => .otherWait s
    | .idle =>
      if op.queued != op.consumed then .cursorMismatch s
      else
        let item := op.children[op.consumed]?.map fun relation =>
          { task := op.task, relation := some relation,
            ack := some ⟨id, op.consumed⟩ : Item }
        if s.queue != [] then .queueNonempty s
        else
          match prepare s id p with
          | .missing t => .missingOperation t
          | .reserveFailed t => .prepareError t
          | .observed t .error => .prepareError t
          | .observed t .panicked => .preparePanic t
          | .observed t .returned =>
            match item with
            | none => .noChildBoundary t
            | some selected =>
              match frameReserve with
              | none => .frameReserveError t
              | some capacity => .clearDiagnosticsBoundary
                  (beginAndClearProcessing t selected occurrence cause capacity)
                  t.frames.length selected

/- runPrefix is an executable candidate definition, not a delivered theorem.
No composition/readback theorem for it has been constructed. Its allocation
and sample inputs overapproximate native observations. In particular a native
realization and full trace extraction are still independent obligations. -/

/- The first unmodeled native owner is clear_diagnostic_scratch,
lib:15934, called at lib:14196. In particular reserve_workspace_undo,
workspace_payload_after, reserve_f5b, replace of delta, observer failure,
then the corresponding index sequence must precede any seed theorem.
A source-local successful Idle/Some-to-Running theorem is NOT delivered. -/

#print resourceWrite_projection
#print axioms resourceWrite_projection
#print resourceTrace_projection
#print axioms resourceTrace_projection
#print sample_projection
#print axioms sample_projection
#print observeCapacity_projection
#print axioms observeCapacity_projection
#print appendUndo_projection
#print axioms appendUndo_projection
#print prepare_projection
#print axioms prepare_projection
#print beginAndClearProcessing_exact
#print axioms beginAndClearProcessing_exact

end YulangClosure.NativeLaunchProjectionR6
