import Init

/-!
R8 CONDITIONAL CANDIDATE; R9 syntax/proof repair, constructed, unchecked.
R9 contract d57ddde8ea97eff2f6641370b2d58d34c06c51398d16941b26a8244893e9783a.
R9 inputs 9268a0d7cd0eb3a674ba10fd2ec4dba63a25007c2f32fd513510ce44f47cc544.
Contract 125f46e39e973d67f7831355cfe9bac1df1c583788b6f03601f9d3d973a72740.
Inputs 076b26e9fd35fb60cdc3ce4ca0cab926a424ca3b64cd22aa45b28ae49ecda577.

The source footprint is: context.replay_operations/context.typed_drains/
session.typed_worklist/session.processing/context.processing versus session
resource counters/ledger and disjoint TRACE, WALKER_LEDGER and SINK TLS owners.
See pinned context:949-992; lib:9253,10774-11446,20414-20744;
f5c_draft_heap:299-319,378-397,540-554,1000-1027,1150-1168;
incoming_sample_trace:142-238. No std implementation is assumed proved.

Images below preserve opaque owner contents without interpreting native handles
as source syntax. Lists of images retain intermediate mutation/panic prefixes.
The IO interface has access only to Writer, never State or launch evidence.
It permits arbitrary partial progress, buffer advances, error, panic and abort.
Its byte-order/progress correctness and native realization remain OPEN.

The theorem native_frame_conditional explicitly requires complete source trace
extraction and every intermediate native state, including unwind/drop. This is
an unproved premise, not a concrete instance or proof of source correspondence.
The full parent Contracts.SourceProblem.InferenceSoundness and its one shared
source witness are unchanged. NativeCorrespondence, clear_diagnostic_scratch,
seed/enqueue/Running, original source coverage and production remain OPEN.
-/
namespace YulangClosure.NativeExternalEffectFrameR8

abbrev Image := List Nat
abbrev Bytes := List Nat

def modulus : Nat := 2 ^ 64

def littleEndian (word : Nat) : Bytes :=
  [word % 256, (word / 256) % 256, (word / 256^2) % 256,
   (word / 256^3) % 256, (word / 256^4) % 256,
   (word / 256^5) % 256, (word / 256^6) % 256, (word / 256^7) % 256]

/-- Complete abstract launch evidence, with separate processing owners. Native
encoding of every image/handle is part of the explicit extraction premise. -/
structure LaunchEvidence where
  operations : Image
  frames : Image
  worklist : Image
  sessionProcessing : Option Nat
  contextProcessing : Option Nat
  deriving DecidableEq, Repr

/-- A progress event can flush old buffered bytes while accepting part of the
new word. consumed counts accepted input bytes, not file bytes. No atomic-write
assumption or equality of these counts is made. -/
structure Progress where
  bufferAfter : Bytes
  fileAppend : Bytes
  consumed : Nat
  deriving Repr

structure Writer where
  /-- Ghost call serial permits a different reply on identical byte requests. -/
  calls : Nat
  buffer : Bytes
  fileTrace : Bytes
  progress : List Progress
  deriving Repr

structure Sink where
  writer : Writer
  nextId : Nat
  count : Nat
  checksum : Nat
  failed : Bool
  excludedDirty : Bool
  excludedIntervalCapacity : Nat
  excludedIntervalBytes : Nat
  excludedCapacity : Nat
  excludedBytes : Nat
  deriving Repr

inductive Exit where
  | ok | error | panic | abort
  deriving DecidableEq, Repr

/-- Used by non-Result callbacks. error is unavailable here. -/
inductive LocalExit where
  | returned | panic | abort
  deriving DecidableEq, Repr

def LocalExit.exit : LocalExit → Exit
  | .returned => .ok
  | .panic => .panic
  | .abort => .abort

structure Reply where
  progress : List Progress
  exit : Exit

/-- This is an opaque external interface, not a theorem about std::io.
No launch field or State is passed to this interface. -/
abbrev WriteAll := Writer → Bytes → Reply

structure Observables where
  physicalChange : Bool
  sampleFailed : Bool
  attempts : Nat
  sampledRouteJournalValueRowsCapacity : Nat
  replayUndoCapacity : Nat
  ledger : Image
  counters : Image
  samples : Nat
  trace : Image
  walkerLedger : Image
  sink : Option Sink
  matrix : Option Image
  detachedMatrix : Option Image
  milestones : List Nat

structure State where
  evidence : LaunchEvidence
  observed : Observables

def pi (s : State) : LaunchEvidence := s.evidence

/-- Each constructor corresponds to an actual mutable owner. In particular,
there is no write constructor for replay evidence or replayUndoCapacity. -/
inductive Effect where
  | physical | failed
  | attempts (n : Nat)
  | journalPeak (capacity : Nat)
  | ledger (image : Image)
  | counters (image : Image)
  | samples (n : Nat)
  | trace (image : Image)
  | walker (image : Image)
  | sink (image : Sink)
  | takeMatrix
  | detached (image : Image)
  | dropDetached
  | restoreMatrix (image : Image)
  | milestone (tag : Nat)

def Effect.apply (effect : Effect) (s : State) : State :=
  { s with observed := match effect with
    | .physical => { s.observed with physicalChange := true }
    | .failed => { s.observed with sampleFailed := true }
    | .attempts n => { s.observed with attempts := n }
    | .journalPeak n => { s.observed with sampledRouteJournalValueRowsCapacity := max s.observed.sampledRouteJournalValueRowsCapacity n }
    | .ledger a => { s.observed with ledger := a }
    | .counters a => { s.observed with counters := a }
    | .samples n => { s.observed with samples := n }
    | .trace a => { s.observed with trace := a }
    | .walker a => { s.observed with walkerLedger := a }
    | .sink a => { s.observed with sink := some a }
    | .takeMatrix => { s.observed with matrix := none, detachedMatrix := s.observed.matrix }
    | .detached a => { s.observed with detachedMatrix := some a }
    | .dropDetached => { s.observed with detachedMatrix := none }
    | .restoreMatrix a => { s.observed with matrix := some a, detachedMatrix := none }
    | .milestone n => { s.observed with milestones := s.observed.milestones ++ [n] } }

def applyEffects (s : State) : List Effect → State
  | [] => s
  | e :: es => applyEffects (e.apply s) es

structure Segment where
  effects : List Effect
  exit : Exit

def done (exit : Exit := .ok) : Segment := ⟨[], exit⟩
def emit (effects : List Effect) : Segment := ⟨effects, .ok⟩

/-- Only normal return continues. In particular sidecar IO Err is swallowed
inside writeWord; callback Result Err and panic are different exits. -/
def andThen (a b : Segment) : Segment :=
  match a.exit with
  | .ok => ⟨a.effects ++ b.effects, b.exit⟩
  | _ => a

def «scoped» (effects : List Effect) (exit : LocalExit) : Segment :=
  ⟨effects, exit.exit⟩

structure SinkRun where
  sink : Sink
  segment : Segment

def progressSink (s : Sink) (p : Progress) : Sink :=
  { s with writer :=
    { calls := s.writer.calls
      buffer := p.bufferAfter
      fileTrace := s.writer.fileTrace ++ p.fileAppend
      progress := s.writer.progress ++ [p] } }

def progressRun (s : Sink) : List Progress → SinkRun
  | [] => ⟨s, done⟩
  | p :: ps =>
    let next := progressSink s p
    let rest := progressRun next ps
    ⟨rest.sink, ⟨Effect.sink next :: rest.segment.effects, rest.segment.exit⟩⟩

/-- Partial writer effects happen before is_err and wrapping checksum.
A panic/abort leaves every preceding buffer/file change visible, and does not
execute either the Err arm or checksum update for the current word. -/
def writeWord (io : WriteAll) (s : Sink) (word : Nat) : SinkRun :=
  let reply := io s.writer (littleEndian word)
  let called := { s with writer := { s.writer with calls := s.writer.calls + 1 } }
  let advanced := progressRun called reply.progress
  let «partial» := { advanced with segment := ⟨[Effect.sink called] ++ advanced.segment.effects, advanced.segment.exit⟩ }
  match reply.exit with
  | .panic => ⟨«partial».sink, ⟨«partial».segment.effects, .panic⟩⟩
  | .abort => ⟨«partial».sink, ⟨«partial».segment.effects, .abort⟩⟩
  | returned =>
    let failed := if returned == .error then
      { «partial».sink with failed := true } else «partial».sink
    let failureEffects := if returned == .error then [Effect.sink failed] else []
    let summed := { failed with checksum := (failed.checksum + word) % modulus }
    ⟨summed, ⟨«partial».segment.effects ++ failureEffects ++ [Effect.sink summed], .ok⟩⟩

/-- The loop continues after every returned write_all Err. count is checked only
after all eight words; overflow preserves writer/checksum/failure effects. -/
def writeLoop (io : WriteAll) (s : Sink) : List Nat → SinkRun
  | [] =>
    if s.count + 1 < modulus then
      let next := { s with count := s.count + 1 }
      ⟨next, emit [Effect.sink next]⟩
    else ⟨s, done .panic⟩
  | w :: ws =>
    let first := writeWord io s w
    match first.segment.exit with
    | .ok =>
      let rest := writeLoop io first.sink ws
      ⟨rest.sink, andThen first.segment rest.segment⟩
    | _ => first

structure Words where
  a : Nat
  b : Nat
  c : Nat
  d : Nat
  e : Nat
  f : Nat
  g : Nat
  h : Nat

def Words.bytes (w : Words) : List Nat :=
  [w.a,w.b,w.c,w.d,w.e,w.f,w.g,w.h].map (fun word => word % modulus)
def writeWords (io : WriteAll) (s : Sink) (w : Words) : SinkRun :=
  writeLoop io s w.bytes

/-- Excluded interval record finishes before the three interval assignments.
The baseline record starts only after this whole function returns normally. -/
def flushExcluded (io : WriteAll) (s : Sink) : SinkRun :=
  if s.excludedDirty then
    let record := writeWords io s ⟨0,0,10,0,s.excludedCapacity,s.excludedBytes,
      s.excludedIntervalCapacity,s.excludedIntervalBytes⟩
    match record.segment.exit with
    | .ok =>
      let cap := { record.sink with excludedIntervalCapacity := record.sink.excludedCapacity }
      let bytes := { cap with excludedIntervalBytes := cap.excludedBytes }
      let clean := { bytes with excludedDirty := false }
      ⟨clean, andThen record.segment (emit [Effect.sink cap,Effect.sink bytes,Effect.sink clean])⟩
    | _ => record
  else ⟨s, done⟩

def record (io : WriteAll) (s : Sink) (w : Words) : SinkRun :=
  let flushed := flushExcluded io s
  match flushed.segment.exit with
  | .ok =>
    let written := writeWords io flushed.sink w
    ⟨written.sink, andThen flushed.segment written.segment⟩
  | _ => flushed

/-- Caller-supplied complete images for each local WalkerLedger mutation,
including decomposition, sample increment, observe_session and assertion exits.
Their arithmetic and source extraction are explicit unresolved bridge duties. -/
structure BaselinePlan where
  entryExit : LocalExit
  recordBorrowExit : LocalExit
  walkerPrefixes : List Image
  walkerExit : LocalExit
  sinkAtRecord : Option Sink
  boundary : Nat
  session : Nat
  owner : Nat
  closed : Nat
  route : Nat

def baseline (io : WriteAll) (p : BaselinePlan) : Segment :=
  andThen (done p.entryExit.exit)
    (match p.sinkAtRecord with
    | none => done
    | some sink =>
      andThen («scoped» (p.walkerPrefixes.map Effect.walker) p.walkerExit)
        (andThen (done p.recordBorrowExit.exit)
          (record io sink ⟨p.boundary,0,8,0,p.session,p.owner,p.closed,p.route⟩).segment))

/-- Matrix sync/RELEASE/unwind may write the same sidecar and walker ledger.
These effects cannot write the session ledger or launch evidence. Opaque
matrix images include its own live/structured owner states and release flags. -/
inductive MatrixStep where
  | image (a : Image)
  | walker (a : Image)
  | sidecar (sink : Sink) (words : Words)

def matrixSteps (io : WriteAll) : List MatrixStep → Segment
  | [] => done
  | .image a :: xs => andThen (emit [.detached a]) (matrixSteps io xs)
  | .walker a :: xs => andThen (emit [.walker a]) (matrixSteps io xs)
  | .sidecar s words :: xs => andThen (record io s words).segment (matrixSteps io xs)

structure MatrixPlan where
  present : Bool
  body : List MatrixStep
  bodyExit : LocalExit
  finalImage : Image
  unwind : List MatrixStep
  unwindExit : LocalExit

/-- Drop can emit RELEASE records before the detached observer is destroyed.
A second panic in unwind is an abort boundary, never an ordinary return.
The explicit native bridge must account for destructor order and termination. -/
def matrix (io : WriteAll) (p : MatrixPlan) : Segment :=
  if p.present then
    let body := andThen (matrixSteps io p.body) (done p.bodyExit.exit)
    let cleanup := andThen (matrixSteps io p.unwind) (done p.unwindExit.exit)
    let terminal : Segment := match body.exit with
      | .ok => emit [.restoreMatrix p.finalImage]
      | .error => done .abort
      | .abort => done .abort
      | .panic =>
        let cleanupEffects := cleanup.effects
        match cleanup.exit with
        | .ok => ⟨cleanupEffects ++ [.dropDetached], .panic⟩
        | _ => ⟨cleanupEffects, .abort⟩
    andThen (emit [.takeMatrix])
      ⟨body.effects ++ terminal.effects, terminal.exit⟩
  else done

structure CallbackPlan where
  testing : Bool
  probe : Bool
  tracePrefixes : List Image
  traceExit : LocalExit
  previousAttempts : Nat
  usizeLimit : Nat
  overflowChecked : Bool
  routeJournalValueRowsCapacity : Option Nat
  journalPeakExit : LocalExit
  preparationExit : Exit
  ledger : Image
  counters : Image
  samples : Nat
  routeFoldExit : LocalExit
  baseline : BaselinePlan
  argumentExit : LocalExit
  completedTracePrefixes : List Image
  completedTraceExit : LocalExit
  matrix : MatrixPlan

/-- Milestones: 0 sample TLS return, 1 ledger publication, 2 counters,
3 sample count, 4 baseline return, 5 completed arguments, 6 completed TLS return.
The arguments can panic after publication/baseline but before TRACE is entered.
This is the IncomingRoute/zero finish/None term/None store wrapper path. -/
def callback (io : WriteAll) (p : CallbackPlan) : Segment :=
  let entry := if p.testing then
    andThen («scoped» (p.tracePrefixes.map Effect.trace) p.traceExit)
      (andThen (emit [.milestone 0])
        (if (decide (p.previousAttempts < p.usizeLimit)) || !p.overflowChecked then
          andThen (emit [.attempts ((p.previousAttempts + 1) % (p.usizeLimit + 1))])
            (match p.routeJournalValueRowsCapacity with
              | none => done
              | some n => andThen (done p.journalPeakExit.exit) (emit [.journalPeak n]))
        else done .panic))
    else done
  let publication := emit
    ((if p.testing then [.ledger p.ledger,.milestone 1] else []) ++
      [.counters p.counters,.milestone 2] ++
      (if p.testing then [.samples p.samples,.milestone 3] else []))
  let baselinePart := if p.probe then
    andThen (done p.routeFoldExit.exit)
      (andThen (baseline io p.baseline) (emit [.milestone 4]))
    else done
  let completed := if p.testing then
    andThen (done p.argumentExit.exit)
      (andThen (emit [.milestone 5])
        (andThen («scoped» (p.completedTracePrefixes.map Effect.trace) p.completedTraceExit)
          (emit [.milestone 6])))
    else done
  andThen entry (andThen (done p.preparationExit)
    (andThen publication (andThen baselinePart
      (andThen completed (if p.probe then matrix io p.matrix else done)))))

/-- Physical change is written before sampling; only callback Result Err sets
sampleFailed. panic and abort bypass that Rust if-let Err handler. -/
def observeCapacity (io : WriteAll) (changed active : Bool) (p : CallbackPlan) : Segment :=
  if changed && active then
    let sampled := callback io p
    ⟨[.physical] ++ sampled.effects ++
      (if sampled.exit == .error then [.failed] else []), sampled.exit⟩
  else done

theorem effect_frame (s : State) (e : Effect) : pi (e.apply s) = pi s := by
  cases s with
  | mk evidence observed => cases e <;> rfl

theorem effect_keeps_replay_undo (s : State) (e : Effect) :
    (e.apply s).observed.replayUndoCapacity = s.observed.replayUndoCapacity := by
  cases s with
  | mk evidence observed => cases e <;> rfl

theorem effects_frame (s : State) (es : List Effect) :
    pi (applyEffects s es) = pi s := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => exact (ih (e.apply s)).trans (effect_frame s e)

/-- Every finite prefix includes the empty prefix and partial I/O progress. -/
theorem every_prefix_frame (s : State) (es : List Effect) (n : Nat) :
    pi (applyEffects s (es.take n)) = pi s := effects_frame s (es.take n)

theorem callback_frame (s : State) (io : WriteAll) (p : CallbackPlan) :
    pi (applyEffects s (callback io p).effects) = pi s :=
  effects_frame s (callback io p).effects

theorem observed_capacity_frame (s : State) (io : WriteAll)
    (changed active : Bool) (p : CallbackPlan) :
    pi (applyEffects s (observeCapacity io changed active p).effects) = pi s :=
  effects_frame s (observeCapacity io changed active p).effects

/-- This quantifies every native intermediate state, including external writes,
unwinding and secondary panic. It requires exact trace extraction, not a
projection-preservation assertion supplied as an IO axiom. Proving this premise
for the pinned Rust implementation is still the first concrete bridge. -/
theorem native_frame_conditional {Native : Type} (view : Native → State)
    (reaches : Native → Native → Prop) (start : Native)
    (io : WriteAll) (changed active : Bool) (p : CallbackPlan)
    (extract : ∀ stop, reaches start stop → ∃ n : Nat,
      view stop = applyEffects (view start)
        ((observeCapacity io changed active p).effects.take n)) :
    ∀ stop, reaches start stop → pi (view stop) = pi (view start) := by
  intro stop h
  obtain ⟨n, represented⟩ := extract stop h
  exact (congrArg pi represented).trans
    (every_prefix_frame (view start) (observeCapacity io changed active p).effects n)

#print effect_frame
#print axioms effect_frame
#print effect_keeps_replay_undo
#print axioms effect_keeps_replay_undo
#print effects_frame
#print axioms effects_frame
#print every_prefix_frame
#print axioms every_prefix_frame
#print callback_frame
#print axioms callback_frame
#print observed_capacity_frame
#print axioms observed_capacity_frame
#print native_frame_conditional
#print axioms native_frame_conditional

end YulangClosure.NativeExternalEffectFrameR8
