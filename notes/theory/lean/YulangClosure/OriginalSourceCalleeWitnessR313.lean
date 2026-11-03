import YulangClosure.OriginalCalleeArgumentHistoryR312

/-!
R313: source/code ownership and raw Callee Return refinement.
Authority: selected EvalInvoke §§3.1–3.4 and the original scoped App builder.
The finite native receipt is not a general Rust simulation, source typing,
callee membership, or an original-event correspondence proof. All original
source constructors and independent arms remain in the unchanged parent.
-/
namespace YulangClosure.OriginalSourceCalleeWitnessR313

open OriginalSource OriginalScopedClosure OriginalSourceInterpretation
open OriginalSourceEnvironment OriginalSourceChecking OriginalWorldReadout
open NativeClosureEnvironment SourceIdentityWorld OriginalParameterSemantics
open OriginalCalleeArgumentHistoryR312

variable {b : Sorts} {C Dict Rest Schema Body View : Type}

/-- The original App rule is computed from the full original source builder.
Both annotation alternatives, both children and every original premise remain. -/
def callPosition (position : Position) (mark : Mark) : Position :=
  let before := match mark.annotation with
    | none => position
    | some _ => position.child 0
  (atBinder before ⟨mark.site, .viewLogic, 0⟩).position.under
    (.existsE ⟨mark.site, .viewLogic, 0⟩)

def callPremises (context : Context) (mark : Mark)
    (callee argument : Source .expression) : List Premise :=
  ((([.descriptorFormation, .wholeArgumentCompatibility, .completeCallCertificate,
      .sourceCallIncidence, .callableImage] : List AtomKind) ++
      (if singletonFormalCall context callee argument then
        [AtomKind.roleAndInitialCallOrigin] else [])).map
      (fun kind => Premise.atom (atom kind mark.site context [callee.site, argument.site]))) ++
    [.checking ⟨.value, mark.site, context, ⟨callee.site, .returnedValue⟩, ⟨mark.site, .descriptor⟩⟩,
     .checking ⟨.computation, mark.site, context, ⟨mark.site, .callableImage⟩, ⟨mark.site, .synthesis⟩⟩]

def appRule (context : Context) (mark : Mark) (callee argument : Source .expression) : RuleTree :=
  .rule .app mark.site context (callPremises context mark callee argument)
    (.two (sourceRules context callee) (sourceRules context argument))

def originalCall (position : Position) (context : Context) (mark : Mark)
    (callee argument : Source .expression) : CallOccurrence :=
  let call := callPosition position mark
  ⟨call, mark.site, context, callPremises context mark callee argument,
    allocate (call.child 0) (sourceRules context callee),
    allocate ((call.child 0).child 1) (sourceRules context argument)⟩

theorem original_call_occurs (position : Position) (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    Occurs (allocate position (sourceRules context (.app mark callee argument)))
      (originalCall position context mark callee argument).program := by
  rcases mark with ⟨site, annotation⟩
  cases annotation with
  | none =>
      apply Occurs.descend (child := (originalCall position context ⟨site, none⟩ callee argument).program)
      · simp only [originalCall, callPosition, sourceRules,
          atBinder, children, CallOccurrence.program, callPremises]
        exact List.mem_singleton_self _
      · exact .root _
  | some target =>
      apply Occurs.descend
        (child := allocate (position.child 0)
          (.existsE ⟨site, .viewLogic, 0⟩
            (appRule context ⟨site, some target⟩ callee argument)))
      · simp only [sourceRules, allocate, children]
        exact List.mem_singleton_self _
      · apply Occurs.descend (child := (originalCall position context ⟨site, some target⟩ callee argument).program)
        · simp only [originalCall, callPosition, allocate, atBinder,
            children, CallOccurrence.program, appRule,
            callPremises]
          exact List.mem_singleton_self _
        · exact .root _

theorem original_argument_erases (position : Position) (context : Context) (mark : Mark)
    (callee argument : Source .expression) :
    (originalCall position context mark callee argument).argument.erase = sourceRules context argument :=
  erase_allocate _ _

/-- Native instruction data. Retained stands for every other instruction;
it does not reject or remove any original source alternative. -/
inductive Instruction where
  | apply (callee argument : Nat)
  | name (binding : Name) (mode : OriginalNameForceExtraction.NameMode)
  | retained

structure Code where
  owner : Declaration
  site : Site
  source : Source .expression
  instruction : Instruction

def Code.delayCode (code : Code) : OriginalCalleeDelayProvenance.Code :=
  ⟨code.source, match code.instruction with
    | .name name ⟨.parameter, .execute⟩ => .parameterExecute name
    | _ => .retained⟩

/-- One immutable source/code arena. Source-to-original coordinates are an
independent map; equality of numeric sites is never an owner proof. -/
structure Arena where
  code : Nat → Option Code

def Arena.program (arena : Arena) (label : Nat) : Option OriginalCalleeDelayProvenance.Code :=
  (arena.code label).map Code.delayCode

/-- Exact joins from the source occurrence to its Apply and BOTH operand
labels. The occurrence is in an arbitrary original root, not an erased sketch. -/
structure SourceApply (arena : Arena) where
  origin : Declaration
  rootContext : Context
  root : Source .expression
  position : Position
  context : Context
  mark : Mark
  callee : Source .expression
  argument : Source .expression
  present : Occurs (source origin rootContext root)
    (allocate position (sourceRules context (.app mark callee argument)))
  applyLabel : Nat
  calleeLabel : Nat
  argumentLabel : Nat
  applyCode : Code
  calleeCode : Code
  argumentCode : Code
  applyFound : arena.code applyLabel = some applyCode
  applyOwner : applyCode.owner = origin
  applySource : applyCode.source = .app mark callee argument
  applySite : applyCode.site = mark.site
  instruction : applyCode.instruction = .apply calleeLabel argumentLabel
  calleeFound : arena.code calleeLabel = some calleeCode
  argumentFound : arena.code argumentLabel = some argumentCode
  calleeOwner : calleeCode.owner = origin
  argumentOwner : argumentCode.owner = origin
  calleeSource : calleeCode.source = callee
  argumentSource : argumentCode.source = argument

theorem occurs_trans {outer middle selected : Program}
    (first : Occurs outer middle) (second : Occurs middle selected) : Occurs outer selected := by
  induction first with
  | root => exact second
  | descend child prior ih => exact .descend child (ih second)

def SourceApply.toApplySource (arena : Arena) (a : SourceApply arena)
    (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (program : raw.program = arena.program) : ApplySource raw where
  origin := a.origin
  rootContext := a.rootContext
  root := a.root
  call := originalCall a.position a.context a.mark a.callee a.argument
  present := occurs_trans a.present (original_call_occurs _ _ _ _ _)
  calleeLabel := a.calleeLabel
  argumentLabel := a.argumentLabel
  argumentCode := a.argumentCode.delayCode
  decoded := by rw [program]; simp only [Arena.program, a.argumentFound, Option.map_some]
  originalArgument := by
    rw [original_argument_erases, ← a.argumentSource]
    rfl

theorem both_operand_decodes (arena : Arena) (a : SourceApply arena) :
    arena.program a.calleeLabel = some a.calleeCode.delayCode ∧
    arena.program a.argumentLabel = some a.argumentCode.delayCode := by
  simp only [Arena.program, a.calleeFound, a.argumentFound, Option.map_some, and_self]

theorem source_enter_saves (arena : Arena) (a : SourceApply arena)
    (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (program : raw.program = arena.program) (caller : Nat)
    (tail : List OriginalCalleeArgumentHistoryR312.Frame) :
    let original := a.toApplySource arena raw program
    arena.code a.applyLabel = some a.applyCode ∧
    a.applyCode.instruction = .apply a.calleeLabel a.argumentLabel ∧
    (enter original caller tail).control = .evaluate a.calleeLabel caller ∧
    (enter original caller tail).frames = .callee (original.save caller) :: tail ∧
    (original.save caller).callerEnvironment = caller ∧
    (original.save caller).call.position = callPosition a.position a.mark ∧
    Occurs (source a.origin a.rootContext a.root) (original.save caller).call.program := by
  exact ⟨a.applyFound, a.instruction, rfl, rfl, rfl, rfl,
    (a.toApplySource arena raw program).present⟩

/-- Mode is decoded from the executable's exact Delay label and that arena's
actual Name instruction. No caller can supply lexicalObserve as a Boolean. -/
def modeAt (arena : Arena) (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (handle : Nat) : Option OriginalNameForceExtraction.NameMode := do
  let executable ← raw.executables handle
  match executable with
  | .delay label _ =>
      let code ← arena.code label
      match code.instruction with
      | .name _ mode => some mode
      | _ => none
  | _ => none

theorem actual_observe_mode (arena : Arena) (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (handle label environment : Nat) (code : Code) (name : Name)
    (executable : raw.executables handle = some (.delay label environment))
    (decoded : arena.code label = some code)
    (instruction : code.instruction = .name name ⟨.parameter, .observe⟩) :
    modeAt arena raw handle = some ⟨.parameter, .observe⟩ ∧
      (OriginalNameForceExtraction.NameMode.mk .parameter .observe).lexicalObserve = true := by
  simp only [modeAt, executable, Option.bind_eq_bind, Option.bind_some, decoded, instruction]
  exact ⟨trivial, rfl⟩

/-- The Observe Name instruction has no inherited computation root. The
ordinary unknown Delay view is computed, not an assumed metadata result. -/
theorem observe_has_no_inherited_root (arena : Arena) (a : SourceApply arena)
    (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (program : raw.program = arena.program) (name : Name)
    (instruction : a.argumentCode.instruction = .name name ⟨.parameter, .observe⟩)
    (caller : Nat) :
    OriginalCalleeDelayProvenance.directFormalRoot raw a.argumentLabel caller = none ∧
    OriginalCalleeDelayProvenance.delayMetadata raw
      (OriginalCalleeDelayProvenance.directFormalRoot raw a.argumentLabel caller) =
      some ⟨none, true, .ordinary⟩ := by
  have decoded := (both_operand_decodes arena a).2
  rw [← program] at decoded
  have root : OriginalCalleeDelayProvenance.directFormalRoot raw a.argumentLabel caller = none := by
    simp only [OriginalCalleeDelayProvenance.directFormalRoot, decoded,
      Option.bind_eq_bind, Option.bind_some, Code.delayCode, instruction]
    rfl
  exact ⟨root, by rw [root]; rfl⟩

def sourcePreparation (arena : Arena) (a : SourceApply arena)
    (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (program : raw.program = arena.program) (caller : Nat) (name : Name) (site : Site)
    (instruction : a.argumentCode.instruction = .name name ⟨.parameter, .observe⟩)
    (argument : a.argument = .name ⟨site, none⟩ name)
    (calRet : Event (S b C Rest Body View))
    (aligned : calRet.current.world = (OriginalCalleeDelayProvenance.project raw).world) :
    Preparation b C Dict Rest Schema Body View where
  raw := raw
  apply := a.toApplySource arena raw program
  caller := caller
  name := name
  nameSite := site
  sourceName := by change a.argumentCode.source = _; rw [a.argumentSource, argument]
  data := ⟨none, true, .ordinary⟩
  read := (observe_has_no_inherited_root arena a raw program name instruction caller).2
  calRet := calRet
  aligned := aligned

def nativeAdapter (arena : Arena)
    (snapshots : Event (S b C Rest Body View) → OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (handles : b.Carrier → Option Nat)
    (fields : OriginalIdentityCarrier.NameDelay → Event (S b C Rest Body View) →
      OriginalIdentityCarrier.EventReadout (OriginalNameForceExtraction.Base b)) :
    OriginalNameForceExtraction.Native b (OriginalValueEntryDemand.Dispatch C)
      OriginalCalleeDelayProvenance.Metadata Rest Body View where
  handle := handles
  executables := fun event => delaySnapshot (snapshots event)
  nameMode := fun event handle => modeAt arena (snapshots event) handle
  dispatch := OriginalNameForceExtraction.noDictionaries
  fields := fields

theorem allocated_observe_mode (arena : Arena) (a : SourceApply arena)
    (p : Preparation b C Dict Rest Schema Body View)
    (program : p.raw.program = arena.program)
    (sameApply : p.apply = a.toApplySource arena p.raw program)
    (name : Name)
    (instruction : a.argumentCode.instruction = .name name ⟨.parameter, .observe⟩) :
    modeAt arena p.post p.delay.handle = some ⟨.parameter, .observe⟩ := by
  have allocated : p.post.executables p.delay.handle =
      some (.delay a.argumentLabel p.caller) := by
    change (OriginalCalleeDelayProvenance.allocate p.raw p.apply.call.site
      p.apply.argumentLabel p.caller).executables p.raw.values.length = _
    simp only [OriginalCalleeDelayProvenance.allocate, ite_true]
    rw [sameApply]
    rfl
  exact (actual_observe_mode arena p.post p.delay.handle a.argumentLabel p.caller
    a.argumentCode name allocated a.argumentFound instruction).1

theorem initialized_name_force (arena : Arena) (a : SourceApply arena)
    (p : Preparation b C Dict Rest Schema Body View)
    (program : p.raw.program = arena.program)
    (sameApply : p.apply = a.toApplySource arena p.raw program)
    (caller : BoundCaller p) (base : Inputs (S b C Rest Body View))
    (snapshots : Event (S b C Rest Body View) → OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (handles : b.Carrier → Option Nat)
    (fields : OriginalIdentityCarrier.NameDelay → Event (S b C Rest Body View) →
      OriginalIdentityCarrier.EventReadout (OriginalNameForceExtraction.Base b))
    (interface : b.Interface)
    (handle : handles (p.row interface).input.carrier = some p.delay.handle)
    (snapshot : snapshots p.event = p.post)
    (instruction : a.argumentCode.instruction = .name p.name ⟨.parameter, .observe⟩) (n : Nat) :
    let native := nativeAdapter arena snapshots handles fields
    let observed := OriginalNameForceExtraction.observe native (p.row interface).input p.event p.delay (n + 2)
    (OriginalNameForceExtraction.inputs base native).force (p.row interface).input p.event observed ∧
    (OriginalNameForceExtraction.inputs base native).traceForm (observed.atInterface interface) =
      .pureReturn ⟨caller.capture.descriptor, p.event.eta.views.value caller.binding.raw.value,
        p.event.eta.views.root caller.binding.raw.value, observed.event⟩ ∧
    observed.event.current.world.receiving.receipts.cell p.event.current.world.receiving.receipts.size =
      some ⟨p.event.current.world.control.current, caller.binding.raw.view, p.nameSite, none⟩ := by
  apply caller_force_return p caller base (nativeAdapter arena snapshots handles fields)
    interface handle (by change delaySnapshot (snapshots p.event) = _; rw [snapshot])
    ⟨.parameter, .observe⟩
  · change modeAt arena (snapshots p.event) p.delay.handle = _
    rw [snapshot]
    exact allocated_observe_mode arena a p program sameApply p.name instruction
  · rfl
  · rfl

/-- Future readback still needs genuine native snapshots, cell preservation
and view bounds. Its mode and executable projection are derived from the
actual source-owned instruction instead of a lexicalObserve assumption. -/
def sourceNativeRead (arena : Arena) (a : SourceApply arena)
    (p : Preparation b C Dict Rest Schema Body View)
    (program : p.raw.program = arena.program)
    (sameApply : p.apply = a.toApplySource arena p.raw program)
    (caller : BoundCaller p)
    (snapshots : Event (S b C Rest Body View) → OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (handles : b.Carrier → Option Nat)
    (fields : OriginalIdentityCarrier.NameDelay → Event (S b C Rest Body View) →
      OriginalIdentityCarrier.EventReadout (OriginalNameForceExtraction.Base b))
    (interface : b.Interface) (event : Event (S b C Rest Body View))
    (handle : handles (p.row interface).input.carrier = some p.delay.handle)
    (futureProgram : (snapshots event).program = arena.program)
    (executable : (snapshots event).executables p.delay.handle = some (.delay a.argumentLabel p.caller))
    (instruction : a.argumentCode.instruction = .name p.name ⟨.parameter, .observe⟩)
    (cells : List (Option (Received Nat)))
    (vector : event.current.world.cells = vectorStore cells)
    (viewBound : caller.capture.raw.view < event.current.world.receiving.views.size) :
    NativeRead p caller (nativeAdapter arena snapshots handles fields) interface event where
  handle := handle
  cell := by
    have decoded := (both_operand_decodes arena a).2
    rw [← futureProgram] at decoded
    have sourceName : a.argumentCode.source = p.delay.code := by
      have same := p.sourceName
      rw [sameApply] at same
      exact same
    change (delaySnapshot (snapshots event)).cell p.delay.handle = _
    simp only [delaySnapshot, OriginalCalleeDelayProvenance.project,
      OriginalCalleeDelayProvenance.executable, executable, Option.map_some, decoded,
      Code.delayCode, sourceName]
    rfl
  mode := ⟨.parameter, .observe⟩
  modeFound := (actual_observe_mode arena (snapshots event) p.delay.handle a.argumentLabel p.caller
    a.argumentCode p.name executable a.argumentFound instruction).1
  lexical := rfl
  cells := cells
  vector := vector
  viewBound := viewBound

/-- Direct initialized-cell capture at the ACTUAL CalRet snapshot. This does
not infer a pre-bind history from the final machine's cells; CalRet can contain
uninitialized cells which a later suffix fills. -/
def captureFromSnapshot (p : Preparation b C Dict Rest Schema Body View)
    (address : Nat) (received : Received Nat)
    (lookup : lookupKey p.name p.calRet.current.world.environments p.caller = some address)
    (stored : p.calRet.current.world.cells.cell address = some received)
    (mode : received.interface = .value)
    (matching : Matches p.calRet.current.world.receiving received)
    (viewBound : received.view < p.raw.views.length) :
    OriginalIdentityCarrier.CaptureAt p.delay p.event where
  address := address
  raw := received
  lookup := by rw [(preparation_keeps_capture_data p).1]; exact lookup
  stored := by rw [(preparation_keeps_capture_data p).2.1]; exact stored
  mode := mode
  matching := by
    obtain ⟨view, found, same⟩ := matching
    exact ⟨view, ((preparation_keeps_capture_data p).2.2 received.view viewBound).trans found, same⟩

theorem snapshot_initialized_evaluate (p : Preparation b C Dict Rest Schema Body View)
    (capture : OriginalIdentityCarrier.CaptureAt p.delay p.event)
    (addressBound : capture.address < p.event.current.world.cells.size)
    (viewBound : capture.raw.view < p.event.current.world.receiving.views.size) :
    OriginalNameForceExtraction.evaluate OriginalNameForceExtraction.noDictionaries p.delay p.event.current.world =
      .ok (capture.address, capture.raw.atName capture.raw.dispatch) :=
  OriginalNameForceExtraction.initialized_evaluate OriginalNameForceExtraction.noDictionaries
    p.delay p.event.current.world capture.address capture.raw capture.raw.dispatch
    capture.lookup addressBound capture.stored rfl viewBound capture.matching

/-- Snapshot of the actual state immediately before dispatch. A Return state
and saved Callee are raw evidence, independently of any source/event semantics. -/
structure CalleeSnapshot (r : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema) where
  machine : OriginalCalleeArgumentHistoryR312.Machine r

def CalleeSnapshot.returned (snapshot : CalleeSnapshot r) : Option (Received Nat) :=
  match snapshot.machine.control, snapshot.machine.frames with
  | .returned raw, .callee _ :: _ => some raw
  | _, _ => none

def savedMatches (actual expected : SavedCallee) : Bool :=
  decide (actual.call.position = expected.call.position) &&
  decide (actual.calleeLabel = expected.calleeLabel) &&
  decide (actual.argumentLabel = expected.argumentLabel) &&
  decide (actual.callerEnvironment = expected.callerEnvironment)

theorem saved_matches_self (saved : SavedCallee) : savedMatches saved saved = true := by
  simp only [savedMatches, decide_true, Bool.and_self]

def CalleeSnapshot.returnedAt (snapshot : CalleeSnapshot r) (expected : SavedCallee) :
    Option (Received Nat) :=
  match snapshot.machine.control, snapshot.machine.frames with
  | .returned raw, .callee actual :: _ => if savedMatches actual expected then some raw else none
  | _, _ => none

theorem request_has_no_return (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (token : Nat) (frames : List OriginalCalleeArgumentHistoryR312.Frame) (saved : SavedCallee) :
    (CalleeSnapshot.mk (r := raw) ⟨.request token, frames⟩).returnedAt saved = none := rfl

theorem wrong_environment_has_no_return (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (received : Received Nat) (actual expected : SavedCallee)
    (tail : List OriginalCalleeArgumentHistoryR312.Frame)
    (different : actual.callerEnvironment ≠ expected.callerEnvironment) :
    (CalleeSnapshot.mk (r := raw) ⟨.returned received, .callee actual :: tail⟩).returnedAt expected = none := by
  simp only [CalleeSnapshot.returnedAt, savedMatches, decide_eq_false different, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]

/-- The returned logical fields are built ONLY from that snapshot's returned
handle, actual provider vector and actual Closure executable. An arbitrary
same-event triple does not satisfy this function. -/
structure ReturnFields (s : Sorts) (call : Position) where
  callee : RawObservation s
  value : ValueRow s
  provider : s.Provider

def returnedFields (p : Preparation b C Dict Rest Schema Body View)
    (observation : (OriginalNameForceExtraction.Base b).Observation)
    (received : Received Nat) (descriptor : b.Descriptor) (providers : Site → b.Provider)
    (provider : OriginalCalleeDelayProvenance.RuntimeValue) :
    ReturnFields (S b C Rest Body View) p.apply.call.position :=
  ⟨⟨observation, p.calRet⟩,
    ⟨descriptor, p.calRet.eta.views.value received.value, p.calRet.eta.views.root received.value, p.calRet⟩,
    providers provider.source⟩

def calleeWitness (p : Preparation b C Dict Rest Schema Body View)
    (snapshot : CalleeSnapshot p.raw) (observation : (OriginalNameForceExtraction.Base b).Observation)
    (descriptor : b.Descriptor) (providers : Site → b.Provider) :
    Option (ReturnFields (S b C Rest Body View) p.apply.call.position) := do
  let received ← snapshot.returnedAt p.saved
  let provider ← (vectorStore (p.raw.values.map some)).cell received.value
  let view ← (vectorStore (p.raw.views.map some)).cell received.view
  if view.value ≠ received.value then none else do
    let executable ← p.raw.executables received.value
    match executable with
    | .closure _ =>
        pure (returnedFields p observation received descriptor providers provider)
    | _ => none

theorem actual_callee_witness (p : Preparation b C Dict Rest Schema Body View)
    (received : Received Nat) (tail : List OriginalCalleeArgumentHistoryR312.Frame)
    (observation : (OriginalNameForceExtraction.Base b).Observation)
    (descriptor : b.Descriptor) (providers : Site → b.Provider)
    (provider : OriginalCalleeDelayProvenance.RuntimeValue)
    (view : SourceIdentityWorld.View Nat OriginalCalleeDelayProvenance.Metadata)
    (closure : OriginalValueEntryDemand.Closure Schema)
    (provided : (vectorStore (p.raw.values.map some)).cell received.value = some provider)
    (viewFound : (vectorStore (p.raw.views.map some)).cell received.view = some view)
    (matching : view.value = received.value)
    (executable : p.raw.executables received.value = some (.closure closure)) :
    calleeWitness p ⟨⟨.returned received, .callee p.saved :: tail⟩⟩ observation descriptor providers =
      some (returnedFields p observation received descriptor providers provider) ∧
    returnTop p.raw ⟨.returned received, .callee p.saved :: tail⟩ =
      some (p.saved, received, tail, (p.post, .ok p.raw.views.length)) := by
  constructor
  · simp only [calleeWitness, CalleeSnapshot.returnedAt, saved_matches_self, ↓reduceIte,
      Option.bind_eq_bind, Option.bind_some, provided, viewFound, matching, ne_eq,
      not_true_eq_false, executable]
    rfl
  · exact (prepared_allocation p received tail).1

/-! Frozen native fixture projection: SHA-256
7e98da35f51301ff0524cc7ea8b332532e17deb42afc80e029ab4a07e7443ea7.
`name` and `other` are a SINGLE supplied original-coordinate map, and dispatch
and metadata are independent readouts. No original semantic event, history,
typing or world certificate is manufactured from the run-local integers. -/
namespace Fixture

/-- Receipt-local H0/S0 symbols, original HIR occurrence ordinals and byte
ranges. These are not allocations into OriginalSource's Site/Declaration
coordinates and cannot authenticate a different run's HIR. -/
structure NativeCoordinate where
  hir : Nat
  sourceRoot : Nat
  occurrence : Nat
  startByte : Nat
  endByte : Nat
  deriving DecidableEq

def sourceCoordinate : Nat → Option NativeCoordinate
  | 8 => some ⟨0, 0, 12, 113, 118⟩
  | 9 => some ⟨0, 0, 13, 111, 112⟩
  | 10 => some ⟨0, 0, 16, 113, 118⟩
  | _ => none

theorem native_source_coordinates :
    sourceCoordinate 8 = some ⟨0, 0, 12, 113, 118⟩ ∧
    sourceCoordinate 9 = some ⟨0, 0, 13, 111, 112⟩ ∧
    sourceCoordinate 10 = some ⟨0, 0, 16, 113, 118⟩ := ⟨rfl, rfl, rfl⟩

structure NativeSavedFrame where
  token : Nat
  currentOwner : Nat
  calleeLabel : Nat
  argumentLabel : Nat
  callerEnvironment : Nat
  order : Nat

def pendingFrame : NativeSavedFrame := ⟨2, 2, 9, 10, 2, 15⟩
def returnedFrame : NativeSavedFrame := ⟨2, 6, 9, 10, 2, 22⟩

theorem same_saved_frame_across_request :
    pendingFrame.token = returnedFrame.token ∧
    pendingFrame.currentOwner ≠ returnedFrame.currentOwner ∧
    pendingFrame.calleeLabel = returnedFrame.calleeLabel ∧
    pendingFrame.argumentLabel = returnedFrame.argumentLabel ∧
    pendingFrame.callerEnvironment = returnedFrame.callerEnvironment ∧
    pendingFrame.order < returnedFrame.order := by decide

def received : Received Nat := ⟨4, .value, 5, none⟩
def returned : Received Nat := ⟨15, .value, 17, none⟩

/-- The actual three instruction rows. Original site/name coordinates and the
arbitrary original callee subtree are supplied by ONE owner map; all other
code rows remain present through `otherCode`. The finite run does not prove
that this original-coordinate map or an original semantic readout exists. -/
def codeArena (origin : Declaration) (site nameSite : Site) (name : Name)
    (callee : Source .expression) (otherCode : Nat → Option Code) : Arena :=
  ⟨fun label => if label = 8 then
      some ⟨origin, site, .app ⟨site, none⟩ callee (.name ⟨nameSite, none⟩ name), .apply 9 10⟩
    else if label = 9 then some ⟨origin, callee.site, callee, .apply 11 12⟩
    else if label = 10 then
      some ⟨origin, nameSite, .name ⟨nameSite, none⟩ name, .name name ⟨.parameter, .observe⟩⟩
    else otherCode label⟩

def sourceApply (origin : Declaration) (rootContext : Context) (root : Source .expression)
    (position : Position) (context : Context) (site nameSite : Site) (name : Name)
    (callee : Source .expression) (otherCode : Nat → Option Code)
    (present : Occurs (source origin rootContext root)
      (allocate position (sourceRules context (.app ⟨site, none⟩ callee (.name ⟨nameSite, none⟩ name))))) :
    SourceApply (codeArena origin site nameSite name callee otherCode) where
  origin := origin
  rootContext := rootContext
  root := root
  position := position
  context := context
  mark := ⟨site, none⟩
  callee := callee
  argument := .name ⟨nameSite, none⟩ name
  present := present
  applyLabel := 8
  calleeLabel := 9
  argumentLabel := 10
  applyCode := ⟨origin, site, .app ⟨site, none⟩ callee (.name ⟨nameSite, none⟩ name), .apply 9 10⟩
  calleeCode := ⟨origin, callee.site, callee, .apply 11 12⟩
  argumentCode := ⟨origin, nameSite, .name ⟨nameSite, none⟩ name, .name name ⟨.parameter, .observe⟩⟩
  applyFound := rfl
  applyOwner := rfl
  applySource := rfl
  applySite := rfl
  instruction := rfl
  calleeFound := rfl
  argumentFound := rfl
  calleeOwner := rfl
  argumentOwner := rfl
  calleeSource := rfl
  argumentSource := rfl

theorem instruction_rows (origin : Declaration) (site nameSite : Site) (name : Name)
    (callee : Source .expression) (otherCode : Nat → Option Code) :
    ((codeArena origin site nameSite name callee otherCode).code 8).map Code.instruction = some (.apply 9 10) ∧
    ((codeArena origin site nameSite name callee otherCode).code 9).map Code.instruction = some (.apply 11 12) ∧
    ((codeArena origin site nameSite name callee otherCode).code 10).map Code.instruction =
      some (.name name ⟨.parameter, .observe⟩) := ⟨rfl, rfl, rfl⟩

def preparation (origin : Declaration) (rootContext : Context) (root : Source .expression)
    (position : Position) (context : Context) (site nameSite : Site) (name : Name)
    (callee : Source .expression) (otherCode : Nat → Option Code)
    (present : Occurs (source origin rootContext root)
      (allocate position (sourceRules context (.app ⟨site, none⟩ callee (.name ⟨nameSite, none⟩ name)))))
    (raw : OriginalCalleeDelayProvenance.Raw C Dict Rest Schema)
    (program : raw.program = (codeArena origin site nameSite name callee otherCode).program)
    (calRet : Event (S b C Rest Body View))
    (aligned : calRet.current.world = (OriginalCalleeDelayProvenance.project raw).world) :
    Preparation b C Dict Rest Schema Body View :=
  sourcePreparation (codeArena origin site nameSite name callee otherCode)
    (sourceApply origin rootContext root position context site nameSite name callee otherCode present)
    raw program 2 name nameSite rfl rfl calRet aligned

theorem exact_delay_operands (p : Preparation b C Dict Rest Schema Body View)
    (values : p.raw.values.length = 16) (caller : p.caller = 2)
    (argument : p.apply.argumentLabel = 10) :
    p.delay.handle = 16 ∧ p.delay.environment = 2 ∧
    p.post.executables 16 = some (.delay 10 2) ∧ p.post.values.length = 17 := by
  refine ⟨values, caller, ?_, ?_⟩
  · change (OriginalCalleeDelayProvenance.allocate p.raw p.apply.call.site
      p.apply.argumentLabel p.caller).executables 16 = _
    simp only [OriginalCalleeDelayProvenance.allocate, values, ite_true, argument, caller]
  · simp only [Preparation.post, OriginalCalleeDelayProvenance.appendView,
      OriginalCalleeDelayProvenance.allocate, List.length_append, List.length_cons,
      List.length_nil, values]

def cells : List (Option (Received Nat)) :=
  [some ⟨5, .value, 6, none⟩, some ⟨2, .value, 3, none⟩,
   some ⟨0, .value, 0, none⟩, none, some ⟨1, .computation, 2, none⟩,
   some received, some ⟨7, .value, 8, none⟩, some ⟨7, .value, 8, none⟩,
   some ⟨11, .value, 12, none⟩, some ⟨12, .computation, 14, none⟩]

def beforeEnvironments (other : Nat → Name) (dispatch : D) : NativeClosureEnvironment.Arena Name D :=
  .append (.root dispatch) 0 (some (other 1, 4)) dispatch

def callerEnvironments (name : Name) (other : Nat → Name) (dispatch : D) :
    NativeClosureEnvironment.Arena Name D :=
  .append (beforeEnvironments other dispatch) 0 (some (name, 5)) dispatch

def environments (name : Name) (other : Nat → Name) (dispatch : D) :
    NativeClosureEnvironment.Arena Name D :=
  .append (.append (.append (.append (callerEnvironments name other dispatch)
    0 (some (other 3, 6)) dispatch) 1 (some (other 4, 7)) dispatch)
    4 (some (other 5, 8)) dispatch) 0 (some (other 6, 9)) dispatch

def views (metadata : Nat → OriginalCalleeDelayProvenance.Metadata) :
    List (SourceIdentityWorld.View Nat OriginalCalleeDelayProvenance.Metadata) :=
  ([0,1,1,2,3,4,5,6,7,8,9,10,11,12,12,13,14,15].zipIdx).map
    fun (value, index) => ⟨value, metadata index⟩

theorem environment_extension (name : Name) (other : Nat → Name) (dispatch : D) :
    Extends (callerEnvironments name other dispatch) (environments name other dispatch) := by
  exact .step (.step (.step (.step .refl (by change 0 < 3; decide))
    (by change 1 < 4; decide)) (by change 4 < 5; decide)) (by change 0 < 6; decide)

theorem initialized_caller_snapshot (name : Name) (other : Nat → Name) (dispatch : D)
    (metadata : Nat → OriginalCalleeDelayProvenance.Metadata) :
    lookupKey name (environments name other dispatch) 2 = some 5 ∧
    (vectorStore cells).cell 5 = some received ∧
    (vectorStore cells).cell 3 = none ∧
    (vectorStore (views metadata |>.map some)).cell 5 = some ⟨4, metadata 5⟩ ∧
    (vectorStore (views metadata |>.map some)).cell 17 = some ⟨15, metadata 17⟩ ∧
    (environments name other dispatch).size = 7 ∧ cells.length = 10 ∧ (views metadata).length = 18 := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exact (lookup_history (environment_extension name other dispatch)
    (fun key => decide (key = name)) 2 (by change 2 < 3; decide)).trans
    (parameter_shadows (beforeEnvironments other dispatch) 0 5 name dispatch)

/-- The recorded original caller bind is env2/cell5, not the selected returned
closure's subsequent env7/cell10 bind. Only actual native readout equations
are inputs; History, desired carrier Meaning and Force success are absent. -/
def boundCaller (p : Preparation b C Dict Rest Schema Body View)
    (before : Event (S b C Rest Body View))
    (other : Nat → Name) (dispatch : OriginalValueEntryDemand.Dispatch C)
    (metadata : Nat → OriginalCalleeDelayProvenance.Metadata)
    (descriptor : b.Descriptor) (fields : EventFields (OriginalNameForceExtraction.Base b))
    (beforeEnvironment : before.current.world.environments = beforeEnvironments other dispatch)
    (beforeCells : before.current.world.cells.size = 5)
    (caller : p.caller = 2)
    (returnEnvironment : p.calRet.current.world.environments = environments p.name other dispatch)
    (returnCells : p.calRet.current.world.cells = vectorStore cells)
    (returnViews : p.raw.views = views metadata)
    (value : OriginalCalleeDelayProvenance.RuntimeValue)
    (valueFound : (vectorStore (p.raw.values.map some)).cell 4 = some value) : BoundCaller p where
  binding := {
    before := before, parent := 0, raw := received, node := ⟨none, none, dispatch⟩,
    found := by rw [beforeEnvironment]; rfl,
    descriptor := descriptor, fields := fields }
  saved := by rw [caller, beforeEnvironment]; rfl
  environments := by
    change Extends (.append before.current.world.environments 0
      (some (p.name, before.current.world.cells.size)) dispatch) p.calRet.current.world.environments
    rw [returnEnvironment, beforeEnvironment, beforeCells]
    exact environment_extension p.name other dispatch
  stored := by rw [beforeCells, returnCells]; rfl
  matching := by
    rw [p.aligned]
    refine ⟨⟨4, metadata 5⟩, ?_, rfl⟩
    change (vectorStore (p.raw.views.map some)).cell 5 = _
    rw [returnViews]
    rfl
  viewBound := by rw [returnViews]; change 5 < 18; decide
  cells := cells
  vector := returnCells
  value := value
  valueFound := valueFound

theorem name_readback (p : Preparation b C Dict Rest Schema Body View)
    (before : Event (S b C Rest Body View))
    (other : Nat → Name) (dispatch : OriginalValueEntryDemand.Dispatch C)
    (metadata : Nat → OriginalCalleeDelayProvenance.Metadata)
    (descriptor : b.Descriptor) (fields : EventFields (OriginalNameForceExtraction.Base b))
    (beforeEnvironment : before.current.world.environments = beforeEnvironments other dispatch)
    (beforeCells : before.current.world.cells.size = 5)
    (caller : p.caller = 2)
    (returnEnvironment : p.calRet.current.world.environments = environments p.name other dispatch)
    (returnCells : p.calRet.current.world.cells = vectorStore cells)
    (returnViews : p.raw.views = views metadata)
    (value : OriginalCalleeDelayProvenance.RuntimeValue)
    (valueFound : (vectorStore (p.raw.values.map some)).cell 4 = some value) :
    OriginalNameForceExtraction.evaluate OriginalNameForceExtraction.noDictionaries p.delay p.event.current.world =
      .ok (5, received) := by
  have computed := caller_name_evaluate p (boundCaller p before other dispatch metadata descriptor fields
    beforeEnvironment beforeCells caller returnEnvironment returnCells returnViews value valueFound)
  change OriginalNameForceExtraction.evaluate OriginalNameForceExtraction.noDictionaries
    p.delay p.event.current.world = .ok (before.current.world.cells.size, received) at computed
  rw [beforeCells] at computed
  exact computed

theorem actual_return_witness (p : Preparation b C Dict Rest Schema Body View)
    (tail : List OriginalCalleeArgumentHistoryR312.Frame)
    (observation : (OriginalNameForceExtraction.Base b).Observation)
    (descriptor : b.Descriptor) (providers : Site → b.Provider)
    (provider : OriginalCalleeDelayProvenance.RuntimeValue)
    (closure : OriginalValueEntryDemand.Closure Schema)
    (metadata : Nat → OriginalCalleeDelayProvenance.Metadata)
    (returnViews : p.raw.views = views metadata)
    (provided : (vectorStore (p.raw.values.map some)).cell 15 = some provider)
    (executable : p.raw.executables 15 = some (.closure closure)) :
    calleeWitness p ⟨⟨.returned returned, .callee p.saved :: tail⟩⟩ observation descriptor providers =
      some (returnedFields p observation returned descriptor providers provider) ∧
    returnTop p.raw ⟨.returned returned, .callee p.saved :: tail⟩ =
      some (p.saved, returned, tail, (p.post, .ok p.raw.views.length)) := by
  exact actual_callee_witness p returned tail observation descriptor providers provider
    ⟨15, metadata 17⟩ closure provided (by rw [returnViews]; rfl) rfl executable

end Fixture
end YulangClosure.OriginalSourceCalleeWitnessR313
