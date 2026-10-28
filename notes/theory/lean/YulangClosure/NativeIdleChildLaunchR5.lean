import Std

/-!
Constructed, UNCHECKED local write cuts for NATIVE-IDLE-CHILD-LAUNCH/r5.

Source: candidate_context.rs and lib.rs at the pins in the r5 contract.
These declarations do not constitute a successful native launch trace. In
particular, no transition is supplied for the capacity-growth resource observer
in candidate_prepare_replay_wait. It occurs before start_typed_drain. The local
frame and suffix calculations below cannot be composed across that boundary.

Nat payloads stand for retained native identities. They carry no interpretation
of source typing, relation validity, scope transformers, or effect permissions.
No R4 candidate is imported. No StartTypedDrain/DriverReturns law is assumed.
-/
namespace YulangClosure.NativeIdleChildLaunchR5

structure Ack where
  operation : Nat
  index : Nat
  deriving DecidableEq, Repr

inductive Wait where
  | idle
  | running (ack : Ack) (drainIndex : Nat)
  | ready (ack : Ack) (drainIndex completion : Nat)
  deriving DecidableEq, Repr

structure Operation where
  task : Nat
  inputs : Nat × Nat
  heads : Option Nat × Option Nat
  prior : Option Nat × Option Nat
  incomingUse : Bool
  children : List Nat
  queued : Nat
  consumed : Nat
  retired : Bool
  restoration : Option Nat
  waitingChild : Wait
  deriving DecidableEq, Repr

structure Item where
  task : Nat
  relation : Option Nat
  replayAck : Option Ack
  deriving DecidableEq, Repr

structure Undo where
  id : Nat
  waitingChild : Wait
  queued : Nat
  consumed : Nat
  retired : Bool
  deriving DecidableEq, Repr

def snapshot (id : Nat) (op : Operation) : Undo :=
  ⟨id, op.waitingChild, op.queued, op.consumed, op.retired⟩

/-- The logical push after try_reserve has succeeded. Allocation and subsequent
capacity observation are not supplied by this local function. -/
def pushPreparedUndo (id : Nat) (op : Operation) (undo : List Undo) : List Undo :=
  undo ++ [snapshot id op]

/-- The item is selected before the fallible replay-wait preparation. -/
def selectedItem (id : Nat) (op : Operation) : Option Item :=
  (op.children[op.consumed]?).map fun relation =>
    ⟨op.task, some relation, some ⟨id, op.consumed⟩⟩

theorem selectedItem_of_lookup (id : Nat) (op : Operation) (relation : Nat)
    (found : op.children[op.consumed]? = some relation) :
    selectedItem id op =
      some ⟨op.task, some relation, some ⟨id, op.consumed⟩⟩ := by
  unfold selectedItem
  rw [found]
  rfl

theorem selectedItem_no_child (id : Nat) (op : Operation)
    (absent : op.children[op.consumed]? = none) :
    selectedItem id op = none := by
  unfold selectedItem
  rw [absent]
  rfl

theorem preparedUndo_exact (id : Nat) (op : Operation) (undo : List Undo) :
    pushPreparedUndo id op undo =
      undo ++ [⟨id, op.waitingChild, op.queued, op.consumed, op.retired⟩] := by
  rfl

/-- All native stage tags are retained; only Transport initialization is proved. -/
inductive Stage where
  | transport | context | dispatch | functionAdmission | functionEnqueue
  | tupleAdmission | tupleEnqueue | recordAdmission | recordEnqueue
  | variantAdmission | variantEnqueue | diagnostics | acknowledgements | returnReady
  deriving DecidableEq, Repr

structure SourceReceipt where
  drainIndex : Nat
  incomingRelation : Option Nat
  replayAck : Option Ack
  createdSeed : Nat
  selectedRelation : Nat
  originIndex : Nat
  task : Nat
  cause : Nat
  completed : Bool
  deriving DecidableEq, Repr

/-- All 19 fields written by begin_typed_drain, in source order. Dispatch
payloads are identity placeholders because their initial values are none. -/
structure Frame where
  initial : Nat
  occurrence : Nat
  cause : Nat
  previousProcessing : Option Nat
  previousRelation : Option Nat
  current : Option Item
  stage : Stage
  contextConsumed : Option Bool
  transitions : Nat
  replayAcks : List Ack
  completedAcks : Nat
  preparedAcks : Nat
  terminalPrepared : Bool
  function : Option Nat
  tuple : Option Nat
  record : Option Nat
  variant : Option Nat
  replayDestination : Option Ack
  sourceDrainReceipt : Option SourceReceipt
  deriving DecidableEq, Repr

def initialFrame (task occurrence cause : Nat)
    (previousProcessing previousRelation : Option Nat) : Frame :=
  { initial := task, occurrence := occurrence, cause := cause
    previousProcessing := previousProcessing, previousRelation := previousRelation
    current := none, stage := .transport, contextConsumed := none
    transitions := 0, replayAcks := [], completedAcks := 0, preparedAcks := 0
    terminalPrepared := false, function := none, tuple := none, record := none
    variant := none, replayDestination := none, sourceDrainReceipt := none }

/-- Successful push's returned index and exact vector value, after reservation.
This is a local vector write, not a model of the caller's preceding execution. -/
def appendFrame (frames : List Frame) (task occurrence cause : Nat)
    (previousProcessing previousRelation : Option Nat) : Nat × List Frame :=
  (frames.length,
    frames ++ [initialFrame task occurrence cause previousProcessing previousRelation])

theorem appendFrame_exact (frames : List Frame) (task occurrence cause : Nat)
    (previousProcessing previousRelation : Option Nat) :
    appendFrame frames task occurrence cause previousProcessing previousRelation =
      (frames.length,
        frames ++ [initialFrame task occurrence cause previousProcessing previousRelation]) := by
  rfl

theorem initialFrame_saved (task occurrence cause : Nat)
    (previousProcessing previousRelation : Option Nat) :
    let frame := initialFrame task occurrence cause previousProcessing previousRelation
    frame.initial = task ∧ frame.occurrence = occurrence ∧ frame.cause = cause ∧
      frame.previousProcessing = previousProcessing ∧
      frame.previousRelation = previousRelation := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem initialFrame_empty (task occurrence cause : Nat)
    (previousProcessing previousRelation : Option Nat) :
    let frame := initialFrame task occurrence cause previousProcessing previousRelation
    frame.current = none ∧ frame.stage = .transport ∧ frame.contextConsumed = none ∧
      frame.transitions = 0 ∧ frame.replayAcks = [] ∧ frame.completedAcks = 0 ∧
      frame.preparedAcks = 0 ∧ frame.terminalPrepared = false ∧
      frame.function = none ∧ frame.tuple = none ∧ frame.record = none ∧
      frame.variant = none ∧ frame.replayDestination = none ∧
      frame.sourceDrainReceipt = none := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def writeDestination (frame : Frame) (ack : Ack) : Frame :=
  { frame with replayDestination := some ack }

def writeRunning (op : Operation) (ack : Ack) (index : Nat) : Operation :=
  { op with waitingChild := .running ack index }

theorem writeDestination_exact (frame : Frame) (ack : Ack) :
    writeDestination frame ack = { frame with replayDestination := some ack } := by
  rfl

theorem writeDestination_preserves_payload (frame : Frame) (ack : Ack) :
    let updated := writeDestination frame ack
    updated.initial = frame.initial ∧ updated.occurrence = frame.occurrence ∧
      updated.cause = frame.cause ∧
      updated.previousProcessing = frame.previousProcessing ∧
      updated.previousRelation = frame.previousRelation ∧
      updated.sourceDrainReceipt = frame.sourceDrainReceipt := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem writeRunning_exact (op : Operation) (ack : Ack) (index : Nat) :
    (writeRunning op ack index).waitingChild = .running ack index ∧
      (writeRunning op ack index).queued = op.queued ∧
      (writeRunning op ack index).consumed = op.consumed ∧
      (writeRunning op ack index).children = op.children ∧
      (writeRunning op ack index).retired = op.retired := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Native relation selection retains the incoming Some relation, even when a
different seed was created. No seed execution/preservation is assumed. -/
def selectRelation (incoming seed : Option Nat) : Option Nat :=
  match incoming with
  | some relation => some relation
  | none => seed

theorem incoming_relation_selected (relation : Nat) (seed : Option Nat) :
    selectRelation (some relation) seed = some relation := by
  rfl

/-- The receipt is a post-enqueue local value calculation. Neither this value
nor its completed=false flag proves that enqueue or drain completion occurred. -/
def receiptValue (index incoming created selected origin task cause : Nat)
    (ack : Ack) : SourceReceipt :=
  ⟨index, some incoming, some ack, created, selected, origin, task, cause, false⟩

theorem receiptValue_exact (index incoming created selected origin task cause : Nat)
    (ack : Ack) :
    (receiptValue index incoming created selected origin task cause ack).completed = false ∧
    (receiptValue index incoming created selected origin task cause ack).incomingRelation =
      some incoming ∧
    (receiptValue index incoming created selected origin task cause ack).selectedRelation =
      selected ∧
    (receiptValue index incoming created selected origin task cause ack).replayAck = some ack := by
  exact ⟨rfl, rfl, rfl, rfl⟩

end YulangClosure.NativeIdleChildLaunchR5
