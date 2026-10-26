import YulangClosure.OriginalIdentityRealization

/-!
The concrete initialized-Name argument Delay. Its one-layer execution is
computed before its original carrier meaning is introduced. The original
Inputs are unchanged; native extraction, independent history/guard evidence,
and dictionary dispatch remain explicit at their owning boundaries.
-/
namespace YulangClosure.OriginalIdentityCarrier

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalParameterWorld OriginalParameterSemantics
open OriginalFormalAdmission OriginalFormalShared OriginalSourceClosure
open OriginalSourceChecking OriginalCheckingAdmission OriginalWorldReadout
open NativeClosureEnvironment SourceIdentityWorld OriginalIdentityRealization

variable {b s : Sorts} {D ViewData Rest Body View : Type}

/-- The actual Callee-frame Delay contains code and its lexical environment.
The handle is the allocated computation, not the value that its Name returns. -/
structure NameDelay where
  handle : Nat
  environment : Nat
  name : Name
  site : Site

def NameDelay.code (delay : NameDelay) : Source .expression :=
  .name ⟨delay.site, none⟩ delay.name

def NameDelay.closure (delay : NameDelay) : Closure (Source .expression) :=
  capture delay.environment delay.code

theorem delay_is_inert (delay : NameDelay) (caller : Nat) :
    delay.closure.body = .name ⟨delay.site, none⟩ delay.name ∧
    entryEnvironment delay.closure caller = delay.environment := ⟨rfl, rfl⟩

/-- Native values allocate at the previous value-vector length. The optional
executable projection retains non-executable entries as None; its size is not
the number of entries in Rust's sparse executable map. -/
structure Allocation (delay : NameDelay) where
  before : List (Option (Closure (Source .expression)))
  fresh : delay.handle = before.length

def Allocation.after {delay : NameDelay} (allocation : Allocation delay) :
    Store (Option (Closure (Source .expression))) :=
  (vectorStore (allocation.before.map some)).push (some delay.closure)

theorem allocation_keeps_actual_code {delay : NameDelay} (allocation : Allocation delay) :
    allocation.after.cell delay.handle = some (some delay.closure) ∧
    delay.closure.savedEnvironment = delay.environment ∧
    delay.closure.body = .name ⟨delay.site, none⟩ delay.name := by
  refine ⟨?_, rfl, rfl⟩
  rw [allocation.fresh]
  simpa only [Allocation.after, vectorStore, List.length_map] using
    push_current (vectorStore (allocation.before.map some)) (some delay.closure)

theorem allocation_preserves_old {delay : NameDelay} (allocation : Allocation delay)
    (index : Nat) (old : index < allocation.before.length) :
    allocation.after.cell index = (vectorStore (allocation.before.map some)).cell index := by
  exact push_old _ _ index (by simpa only [vectorStore, List.length_map] using old)

theorem allocation_distinct_from_old_value {delay : NameDelay} (allocation : Allocation delay)
    (value : Nat) (existing : value < allocation.before.length) : delay.handle ≠ value := by
  rw [allocation.fresh]
  exact (Nat.ne_of_lt existing).symm

/-- Request and unavailable states are retained in the operational carrier
machine. The computed initialized-Name run below reaches neither. -/
inductive Phase where
  | force
  | name
  | returned (raw : Received Nat)
  | request
  | unavailable

structure Machine (D ViewData Rest : Type) where
  world : World Name D Nat ViewData Nat Rest
  phase : Phase

def step (delay : NameDelay) (dispatch : Option Nat)
    (state : Machine D ViewData Rest) : Option (Machine D ViewData Rest) :=
  match state.phase with
  | .force => some ⟨state.world, .name⟩
  | .name =>
      match observeName state.world delay.closure.savedEnvironment delay.name delay.site dispatch with
      | some (world, raw) => some ⟨world, .returned raw⟩
      | none => some ⟨state.world, .unavailable⟩
  | .returned _ | .request | .unavailable => none

def run (delay : NameDelay) (dispatch : Option Nat)
    (world : World Name D Nat ViewData Nat Rest) : Nat → Machine D ViewData Rest
  | 0 => ⟨world, .force⟩
  | n + 1 =>
      let previous := run delay dispatch world n
      (step delay dispatch previous).getD previous

def namedWorld (world : World Name D Nat ViewData Nat Rest)
    (delay : NameDelay) (raw : Received Nat) : World Name D Nat ViewData Nat Rest :=
  {world with receiving := world.receiving.record world.control.current raw.view delay.site none}

theorem run_zero (delay : NameDelay) (dispatch : Option Nat)
    (world : World Name D Nat ViewData Nat Rest) :
    run delay dispatch world 0 = ⟨world, .force⟩ := rfl

theorem run_open (delay : NameDelay) (dispatch : Option Nat)
    (world : World Name D Nat ViewData Nat Rest) :
    run delay dispatch world 1 = ⟨world, .name⟩ := rfl

/-- Exact initialized-cell execution, with the same raw value and view. No
latent callable or retained computation stored in that value is executed. -/
theorem run_return (delay : NameDelay) (dispatch : Option Nat)
    (world : World Name D Nat ViewData Nat Rest) (raw : Received Nat)
    (read : observe (fun name => decide (name = delay.name)) world.environments
      delay.environment world.cells.cell = some raw)
    (matching : Matches world.receiving raw) (n : Nat) :
    run delay dispatch world (n + 2) =
      ⟨namedWorld world delay raw, .returned (raw.atName dispatch)⟩ := by
  have native := name_success (site := delay.site) (dispatch := dispatch) read matching
  induction n with
  | zero => simp [run, step, NameDelay.closure, capture, native, namedWorld]
  | succ n ih =>
      change (step delay dispatch (run delay dispatch world (n + 2))).getD
        (run delay dispatch world (n + 2)) = _
      rw [ih]
      rfl

/-- A real constructor instance: bind the received Value, save that new
lexical environment in the argument Delay, then Force its Name code. The
lookup premise is discharged by the actual bind implementation. -/
theorem bound_name_delay_run (world : World Name D Nat ViewData Nat Rest)
    (parent : Nat) (name : Name) (raw : Received Nat) (node : Node Name D)
    (found : nodeAt world.environments parent = some node)
    (matching : Matches world.receiving raw) (handle site : Nat)
    (dispatch : Option Nat) (n : Nat) :
    let delay : NameDelay := ⟨handle, world.environments.size, name, site⟩
    let bound := bindValue world parent name raw node found
    run delay dispatch bound (n + 2) =
      ⟨namedWorld bound delay raw.asValue, .returned (raw.asValue.atName dispatch)⟩ := by
  exact run_return ⟨handle, world.environments.size, name, site⟩ dispatch
    (bindValue world parent name raw node found) raw.asValue
    (bind_read world parent name raw node found) matching n

/-- The error branch is present, rather than being removed from the native
machine by a semantic admission predicate. -/
theorem run_unavailable (delay : NameDelay) (dispatch : Option Nat)
    (world : World Name D Nat ViewData Nat Rest)
    (failed : observeName world delay.environment delay.name delay.site dispatch = none) :
    run delay dispatch world 2 = ⟨world, .unavailable⟩ := by
  simp [run, step, NameDelay.closure, capture, failed]

theorem run_cases (delay : NameDelay) (dispatch : Option Nat)
    (world : World Name D Nat ViewData Nat Rest) (raw : Received Nat)
    (read : observe (fun name => decide (name = delay.name)) world.environments
      delay.environment world.cells.cell = some raw)
    (matching : Matches world.receiving raw) (n : Nat) :
    run delay dispatch world n = ⟨world, .force⟩ ∨
    run delay dispatch world n = ⟨world, .name⟩ ∨
    run delay dispatch world n =
      ⟨namedWorld world delay raw, .returned (raw.atName dispatch)⟩ := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
      cases n with
      | zero => exact Or.inr (Or.inl rfl)
      | succ n => exact Or.inr (Or.inr (run_return delay dispatch world raw read matching n))

theorem run_no_request_or_error (delay : NameDelay) (dispatch : Option Nat)
    (world : World Name D Nat ViewData Nat Rest) (raw : Received Nat)
    (read : observe (fun name => decide (name = delay.name)) world.environments
      delay.environment world.cells.cell = some raw)
    (matching : Matches world.receiving raw) (n : Nat) :
    (run delay dispatch world n).phase ≠ .request ∧
    (run delay dispatch world n).phase ≠ .unavailable := by
  rcases run_cases delay dispatch world raw read matching n with h | h | h <;>
    rw [h] <;> constructor <;> intro impossible <;> cases impossible

/-- Current configuration and evidence are read at the actual prefix. The
native world is computed by run; the residual machine state is not identified
with the creation configuration. -/
structure EventReadout (b : Sorts) where
  residual : Nat → b.Configuration
  fields : Nat → EventFields b

def eventAt (delay : NameDelay) (dispatch : Option Nat)
    (before : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (readout : EventReadout b) (n : Nat) :
    Event (OriginalReturnWorld.S b D ViewData Rest Body View) :=
  if n = 0 then before else
    let fields := readout.fields n
    {before with
      history := fields.history
      current := {before.current with residual := readout.residual n, world := (run delay dispatch before.current.world n).world}
      eta := {before.eta with original := fields.assignment}
      witness := {before.witness with current := fields.witness}
      scope := fields.scope, authority := fields.authority,
      incidence := fields.incidence, dictionary := fields.dictionary}

theorem event_zero (delay : NameDelay) (dispatch : Option Nat)
    (before : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (readout : EventReadout b) : eventAt delay dispatch before readout 0 = before := by
  simp [eventAt]

theorem run_immutable_fields (delay : NameDelay) (dispatch : Option Nat)
    (world : World Name D Nat ViewData Nat Rest) (raw : Received Nat)
    (read : observe (fun name => decide (name = delay.name)) world.environments
      delay.environment world.cells.cell = some raw)
    (matching : Matches world.receiving raw) (n : Nat) :
    (run delay dispatch world n).world.environments = world.environments ∧
    (run delay dispatch world n).world.cells = world.cells := by
  rcases run_cases delay dispatch world raw read matching n with h | h | h <;>
    rw [h] <;> exact ⟨rfl, rfl⟩

/-- Positive readouts projected from the independently valid input world.
Constructors contain raw installed equations and ordinary logical scopes;
there is no trace/carrier membership certificate or unrestricted query hole. -/
inductive WorldFields (operator : Inputs s) (event : Event s) : Positive s → Prop where
  | guard (fact : Prop) (proof : fact) : WorldFields operator event (.guard fact)
  | world : WorldFields operator event (.field (.world event))
  | value (address : Nat) (descriptor : s.Descriptor) (value : s.Value) (root : s.Root)
      (found : operator.installed event address = some (.value descriptor value root)) :
      WorldFields operator event (.field (.value ⟨descriptor, value, root, event⟩))
  | carrier (address : Nat) (interface : s.Interface) (carrier : s.Carrier) (root : s.Root)
      (found : operator.installed event address = some (.carrier interface carrier root)) :
      WorldFields operator event (.field (.carrier ⟨interface, carrier, root, event⟩))
  | both {left right} : WorldFields operator event left → WorldFields operator event right →
      WorldFields operator event (.both left right)
  | left {left right} : WorldFields operator event left → WorldFields operator event (.either left right)
  | right {left right} : WorldFields operator event right → WorldFields operator event (.either left right)
  | all (Domain : Type) (body : Domain → Positive s) :
      (∀ value, WorldFields operator event (body value)) → WorldFields operator event (.all Domain body)
  | existsE (Domain : Type) (body : Domain → Positive s) (value : Domain) :
      WorldFields operator event (body value) → WorldFields operator event (.existsE Domain body)

theorem world_fields_hold (operator : Inputs s) (event : Event s)
    (world : Meaning operator (.world event)) (fields : Positive s)
    (projection : WorldFields operator event fields) : fields.Holds (Meaning operator) := by
  induction projection with
  | guard _ proof => exact proof
  | world => exact world
  | value address descriptor value root found =>
      exact world_installed operator event world address _ found
  | carrier address interface carrier root found =>
      exact world_installed operator event world address _ found
  | both _ _ left right => exact ⟨left, right⟩
  | left _ proof => exact Or.inl proof
  | right _ proof => exact Or.inr proof
  | all _ _ _ proof => exact proof
  | existsE _ _ value _ proof => exact ⟨value, proof⟩

theorem run_returned_unique (delay : NameDelay) (dispatch : Option Nat)
    (world : World Name D Nat ViewData Nat Rest) (raw : Received Nat)
    (read : observe (fun name => decide (name = delay.name)) world.environments
      delay.environment world.cells.cell = some raw)
    (matching : Matches world.receiving raw) (n : Nat) (result : Received Nat)
    (complete : (run delay dispatch world n).phase = .returned result) :
    result = raw.atName dispatch := by
  rcases run_cases delay dispatch world raw read matching n with h | h | h
  · rw [h] at complete; cases complete
  · rw [h] at complete; cases complete
  · rw [h] at complete
    exact (Phase.returned.inj complete).symm

/-- The source Name is already resolved to an initialized Value cell.
This is raw lexical/cell evidence, not a descriptor membership certificate. -/
structure CaptureAt (delay : NameDelay)
    (event : Event (OriginalReturnWorld.S b D ViewData Rest Body View)) where
  address : Nat
  raw : Received Nat
  lookup : lookupKey delay.name event.current.world.environments delay.environment = some address
  stored : event.current.world.cells.cell address = some raw
  mode : raw.interface = .value
  matching : Matches event.current.world.receiving raw

theorem CaptureAt.read {delay : NameDelay}
    {event : Event (OriginalReturnWorld.S b D ViewData Rest Body View)}
    (capture : CaptureAt delay event) :
    observe (fun name => decide (name = delay.name)) event.current.world.environments
      delay.environment event.current.world.cells.cell = some capture.raw := by
  change (lookupKey delay.name event.current.world.environments delay.environment).bind _ = _
  rw [capture.lookup]
  exact capture.stored

def CaptureAt.descriptor {delay : NameDelay}
    {event : Event (OriginalReturnWorld.S b D ViewData Rest Body View)}
    (capture : CaptureAt delay event) : b.Descriptor :=
  event.eta.views.descriptor capture.address capture.raw.view

theorem CaptureAt.installed {delay : NameDelay}
    {event : Event (OriginalReturnWorld.S b D ViewData Rest Body View)}
    (capture : CaptureAt delay event) :
    installed event capture.address = some (.value capture.descriptor
      (event.eta.views.value capture.raw.value) (event.eta.views.root capture.raw.value)) := by
  have present := every_native_some event capture.address capture.raw capture.stored
  simpa only [viewAssignment, ViewAssignment.received, capture.mode, CaptureAt.descriptor] using present

/-- All native registry projections are unchanged by opening and observing
this Name. Receiving receipts and the residual machine state are not erased. -/
theorem event_registry (delay : NameDelay) (dispatch : Option Nat)
    (before : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (capture : CaptureAt delay before) (readout : EventReadout b)
    (references : Body → Nat → Option Name) (n : Nat) :
    installed (eventAt delay dispatch before readout n) = installed before ∧
    aliasAt (eventAt delay dispatch before readout n) = aliasAt before ∧
    captureAt references (eventAt delay dispatch before readout n) = captureAt references before ∧
    (eventAt delay dispatch before readout n).witness.shared = before.witness.shared ∧
    (eventAt delay dispatch before readout n).eta.views = before.eta.views := by
  have unchanged := run_immutable_fields delay dispatch before.current.world capture.raw
    capture.read capture.matching n
  by_cases zero : n = 0
  · subst n; simp [eventAt]
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simp [eventAt, zero, installed, viewAssignment, unchanged.2]
    · funext first second
      simp [eventAt, zero, aliasAt, unchanged.1]
    · funext provider name
      simp [eventAt, zero, captureAt, captureAddress, unchanged.1]
    · simp [eventAt, zero]
    · simp [eventAt, zero]

theorem event_cells (delay : NameDelay) (dispatch : Option Nat)
    (before : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (capture : CaptureAt delay before) (readout : EventReadout b) (n : Nat) :
    (eventAt delay dispatch before readout n).current.world.cells = before.current.world.cells := by
  have unchanged := (run_immutable_fields delay dispatch before.current.world capture.raw
    capture.read capture.matching n).2
  by_cases zero : n = 0
  · subst n; simp [eventAt]
  · simp [eventAt, zero, unchanged]

theorem event_world
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name) (delay : NameDelay) (dispatch : Option Nat)
    (before : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (capture : CaptureAt delay before) (readout : EventReadout b) (n : Nat)
    (world : Meaning (inputs operator references) (.world before))
    (later : operator.compatible before (eventAt delay dispatch before readout n))
    (coherent : operator.eventCoherent (eventAt delay dispatch before readout n))
    (guards : (operator.worldGuards (eventAt delay dispatch before readout n)).Valid) :
    Meaning (inputs operator references) (.world (eventAt delay dispatch before readout n)) := by
  have same := event_registry delay dispatch before capture readout references n
  have old := (world_unfold (inputs operator references) before).mp world
  apply (world_unfold (inputs operator references) _).mpr
  refine ⟨coherent, guards, ?_, ?_, ?_, ?_⟩
  · simpa only [AliasesAgree, inputs, same.1, same.2.1] using old.2.2.1
  · simpa only [CapturesAgree, inputs, same.1, same.2.2.1,
      event_cells delay dispatch before capture readout n] using old.2.2.2.1
  · simpa only [WitnessesAgree, inputs, same.2.2.2.1] using old.2.2.2.2.1
  · intro address object found
    have oldFound : (inputs operator references).installed before address = some object := by
      simpa only [inputs, same.1] using found
    exact installed_restrict (inputs operator references) object before _ later
      (old.2.2.2.2.2 address object oldFound)

/-- Closure under every original compatible event, without assuming that the
opaque compatibility relation is reflexive or transitive. -/
inductive Reach (operator : Inputs s) (origin : Event s) : Event s → Prop where
  | initial : Reach operator origin origin
  | later {before after} : Reach operator origin before → operator.compatible before after →
      Reach operator origin after

/-- Ordinary independent history/world inputs and inert formation. These
inputs precede execution. In particular no trace meaning is a field here. -/
structure History
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name) (row : CarrierRow (OriginalReturnWorld.S b D ViewData Rest Body View))
    (delay : NameDelay) where
  allocation : Allocation delay
  origin : CaptureAt delay row.event
  existingValue : origin.raw.value < allocation.before.length
  environmentBound : delay.environment < row.event.current.world.environments.size
  actualCarrier : row.carrier = row.event.eta.views.carrier delay.handle
  actualRoot : row.root = row.event.eta.views.root delay.handle
  worlds : ∀ event, Reach operator row.event event → Meaning (inputs operator references) (.world event)
  environments : ∀ event, Reach operator row.event event →
    Extends row.event.current.world.environments event.current.world.environments
  stored : ∀ event, Reach operator row.event event → event.current.world.cells.cell origin.address = some origin.raw
  matchingViews : ∀ event, Reach operator row.event event → Matches event.current.world.receiving origin.raw
  views : ∀ event, Reach operator row.event event → event.eta.views = row.event.eta.views
  inert : ∀ event, Reach operator row.event event → (operator.carrierGuards (row.atEvent event)).Valid
  captures : ∀ event, Reach operator row.event event →
    WorldFields (inputs operator references) event (operator.carrierCaptures (row.atEvent event))
  demand : ∀ event, Reach operator row.event event → ∀ atEvent,
    operator.demand (row.atEvent event) atEvent → operator.compatible event atEvent

def History.capture
    {operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View)}
    {references : Body → Nat → Option Name} {row : CarrierRow (OriginalReturnWorld.S b D ViewData Rest Body View)}
    {delay : NameDelay} (history : History operator references row delay)
    (event : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (reachable : Reach operator row.event event) : CaptureAt delay event :=
  ⟨history.origin.address, history.origin.raw,
    (lookup_history (history.environments event reachable) (fun name => decide (name = delay.name))
      delay.environment history.environmentBound).trans history.origin.lookup,
    history.stored event reachable, history.origin.mode, history.matchingViews event reachable⟩

theorem history_same_capture
    {operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View)}
    {references : Body → Nat → Option Name} {row : CarrierRow (OriginalReturnWorld.S b D ViewData Rest Body View)}
    {delay : NameDelay} (history : History operator references row delay)
    (event : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (reachable : Reach operator row.event event) :
    (history.capture event reachable).address = history.origin.address ∧
    (history.capture event reachable).raw = history.origin.raw ∧
    (history.capture event reachable).descriptor = history.origin.descriptor ∧
    delay.handle ≠ (history.capture event reachable).raw.value := by
  refine ⟨rfl, rfl, ?_, allocation_distinct_from_old_value history.allocation _ history.existingValue⟩
  change event.eta.views.descriptor history.origin.address history.origin.raw.view =
    row.event.eta.views.descriptor history.origin.address history.origin.raw.view
  rw [history.views event reachable]

/-- Independent dynamic evidence at every finite native prefix. The raw
configuration is eventAt, which computes the native receipt/world update. -/
structure Execution
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (delay : NameDelay) (demand : Event (OriginalReturnWorld.S b D ViewData Rest Body View)) where
  dispatch : Option Nat
  readout : EventReadout b
  compatible : ∀ n, operator.compatible demand (eventAt delay dispatch demand readout n)
  coherent : ∀ n, operator.eventCoherent (eventAt delay dispatch demand readout n)
  worldGuards : ∀ n, (operator.worldGuards (eventAt delay dispatch demand readout n)).Valid

def resultForm (views : ViewAssignment b Nat) (descriptor : b.Descriptor)
    (event : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (result : Option (Received Nat)) : TraceForm (OriginalReturnWorld.S b D ViewData Rest Body View) :=
  match result with
  | none => .unfinished
  | some returned => .pureReturn ⟨descriptor, views.value returned.value, views.root returned.value, event⟩

/-- An arbitrary raw observation is decoded into a prefix of this actual
execution. None is a zero/admin/unfinished observation; Some is a completed
native Return and must match the computed machine state. Original positive
fields retain their full logical scopes and are projected from that world. -/
structure ObservationAt
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name) (interface : b.Interface) (delay : NameDelay)
    (demand : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (capture : CaptureAt delay demand) (execution : Execution operator delay demand)
    (raw : RawObservation (OriginalReturnWorld.S b D ViewData Rest Body View)) where
  fuel : Nat
  result : Option (Received Nat)
  complete : ∀ returned, result = some returned →
    (run delay execution.dispatch demand.current.world fuel).phase = .returned returned
  event : raw.event = eventAt delay execution.dispatch demand execution.readout fuel
  form : operator.traceForm (raw.atInterface interface) =
    resultForm demand.eta.views capture.descriptor raw.event result
  guards : (operator.observationGuards (raw.atInterface interface)).Valid
  fields : WorldFields (inputs operator references) raw.event
    (operator.observationFields (raw.atInterface interface))

theorem observation_meaning
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name) (interface : b.Interface) (delay : NameDelay)
    (demand : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (capture : CaptureAt delay demand) (execution : Execution operator delay demand)
    (world : Meaning (inputs operator references) (.world demand))
    (raw : RawObservation (OriginalReturnWorld.S b D ViewData Rest Body View))
    (readout : ObservationAt operator references interface delay demand capture execution raw) :
    Meaning (inputs operator references) (.trace (raw.atInterface interface)) := by
  have prefixWorld := event_world operator references delay execution.dispatch demand capture
    execution.readout readout.fuel world (execution.compatible readout.fuel)
      (execution.coherent readout.fuel) (execution.worldGuards readout.fuel)
  have actualWorld : Meaning (inputs operator references) (.world raw.event) := by
    rw [readout.event]; exact prefixWorld
  have same := event_registry delay execution.dispatch demand capture execution.readout references readout.fuel
  have found : installed raw.event capture.address = some (.value capture.descriptor
      (demand.eta.views.value capture.raw.value) (demand.eta.views.root capture.raw.value)) := by
    rw [readout.event, same.1]
    exact capture.installed
  apply (meaning_iff (inputs operator references) (.trace (raw.atInterface interface))).mpr
  change PhiT (inputs operator references) (Meaning (inputs operator references)) _
  refine ⟨((world_unfold (inputs operator references) raw.event).mp actualWorld).1,
    readout.guards, actualWorld, ?_, world_fields_hold _ raw.event actualWorld _ readout.fields⟩
  rw [(native_inputs_keep_trace operator references (raw.atInterface interface)).1, readout.form]
  cases result : readout.result with
  | none => trivial
  | some returned =>
      simp only [resultForm]
      have sameResult := run_returned_unique delay execution.dispatch demand.current.world capture.raw
        capture.read capture.matching readout.fuel returned (readout.complete returned result)
      rw [sameResult]
      exact ⟨rfl, immutable_name_value (inputs operator references) raw.event actualWorld
        capture.address capture.descriptor _ _ found⟩

/-- The still-open native extraction boundary. It retains *every* original
force observation, rather than selecting successful or member observations.
Only independent guards, exact native readback and raw field projections are
required; neither whole-carrier nor observation Meaning is an input. -/
structure NativeExtraction
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name) (row : CarrierRow (OriginalReturnWorld.S b D ViewData Rest Body View))
    (delay : NameDelay) (history : History operator references row delay) where
  execution : ∀ event, (reachable : Reach operator row.event event) → ∀ demand,
    (demanded : operator.demand (row.atEvent event) demand) → Execution operator delay demand
  observations : ∀ event, (reachable : Reach operator row.event event) → ∀ demand,
    (demanded : operator.demand (row.atEvent event) demand) → ∀ raw,
    operator.force (row.atEvent event).input demand raw →
      ObservationAt operator references row.interface delay demand
        (history.capture demand (.later reachable (history.demand event reachable demand demanded)))
        (execution event reachable demand demanded) raw
  incidence : ∀ event, (reachable : Reach operator row.event event) → ∀ demand,
    (demanded : operator.demand (row.atEvent event) demand) → ∀ raw,
    operator.force (row.atEvent event).input demand raw →
      operator.forceIncidence (row.atEvent event) demand raw

/-- Complete original PhiCar for this exact Delay, including the live world,
captures, every admitted demand, every raw prefix and every lawful future.
The only semantic input is the independent surrounding world/history. -/
theorem name_delay_whole
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name) (row : CarrierRow (OriginalReturnWorld.S b D ViewData Rest Body View))
    (delay : NameDelay) (history : History operator references row delay)
    (native : NativeExtraction operator references row delay history) :
    Meaning (inputs operator references) (.carrier row) := by
  let added : Family (OriginalReturnWorld.S b D ViewData Rest Body View) :=
    fun query => ∃ event, Reach operator row.event event ∧ query = .carrier (row.atEvent event)
  let candidate := (Meaning (inputs operator references)).join added
  have included : (Meaning (inputs operator references)).Le candidate := fun _ h => Or.inl h
  have postfixed : candidate.Le (Phi (inputs operator references) candidate) := by
    intro query member
    rcases member with old | fresh
    · exact phi_monotone (inputs operator references) included query
        ((meaning_iff (inputs operator references) query).mp old)
    · obtain ⟨event, reachable, rfl⟩ := fresh
      have world := history.worlds event reachable
      refine ⟨((world_unfold (inputs operator references) event).mp world).1,
        history.inert event reachable, included _ world, ?_, ?_, ?_⟩
      · exact positive_mono included _
          (world_fields_hold (inputs operator references) event world _ (history.captures event reachable))
      · intro demand demanded
        have lawful := history.demand event reachable demand demanded
        refine ⟨lawful, ?_⟩
        intro raw forced
        refine ⟨native.incidence event reachable demand demanded raw forced, included _ ?_⟩
        exact observation_meaning operator references row.interface delay demand
          (history.capture demand (.later reachable lawful))
          (native.execution event reachable demand demanded)
          (history.worlds demand (.later reachable lawful)) raw
          (native.observations event reachable demand demanded raw forced)
      · intro later lawful
        exact Or.inr ⟨later, .later reachable lawful, rfl⟩
  exact greatest_coinduct (Phi (inputs operator references)) candidate postfixed (.carrier row)
    (Or.inr ⟨row.event, .initial, rfl⟩)

/-- Remaining actual Force/Return, native bind and independent event facts.
The whole-carrier semantic field has been removed; it is constructed below. -/
structure EntryFacts
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name) (use : Use b D ViewData Rest Body View source)
    (descriptor : b.Descriptor) where
  demandEvent : Event (OriginalReturnWorld.S b D ViewData Rest Body View)
  demanded : operator.demand (use.carrier operator) demandEvent
  executed : operator.force (use.carrier operator).input demandEvent ⟨use.packet.observation, use.before⟩
  actualReturn : operator.traceForm
    ((⟨use.packet.observation, use.before⟩ : RawObservation (OriginalReturnWorld.S b D ViewData Rest Body View)).atInterface
      (use.carrier operator).interface) =
    .pureReturn ⟨descriptor, use.views.value use.packet.raw.value, use.views.root use.packet.raw.value, use.before⟩
  cells : List (Option (Received Nat))
  vector : use.packet.snapshot.world.cells = vectorStore cells
  savedProviders : ∀ provider closure, use.packet.snapshot.providers provider = some closure →
    closure.savedEnvironment < use.packet.snapshot.world.environments.size
  savedAliases : ∀ reference ∈ use.packet.snapshot.aliases,
    reference.environment < use.packet.snapshot.world.environments.size
  bindLater : operator.compatible use.before (use.bound descriptor)
  bindCoherent : operator.eventCoherent (use.bound descriptor)
  bindGuards : (operator.worldGuards (use.bound descriptor)).Valid
  nameLater : operator.compatible (use.bound descriptor) (use.named descriptor)
  nameCoherent : operator.eventCoherent (use.named descriptor)
  nameGuards : (operator.worldGuards (use.named descriptor)).Valid
  matching : Matches use.packet.snapshot.world.receiving use.packet.raw


def EntryFacts.toForceCut
    {operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View)}
    {references : Body → Nat → Option Name} {source : Identity}
    {use : Use b D ViewData Rest Body View source} {descriptor : b.Descriptor}
    (facts : EntryFacts operator references use descriptor) (delay : NameDelay)
    (history : History operator references (use.carrier operator) delay)
    (native : NativeExtraction operator references (use.carrier operator) delay history) :
    ForceCut operator references use descriptor :=
  {whole := name_delay_whole operator references (use.carrier operator) delay history native
   demandEvent := facts.demandEvent
   demanded := facts.demanded
   executed := facts.executed
   actualReturn := facts.actualReturn
   cells := facts.cells
   vector := facts.vector
   savedProviders := facts.savedProviders
   savedAliases := facts.savedAliases
   bindLater := facts.bindLater
   bindCoherent := facts.bindCoherent
   bindGuards := facts.bindGuards
   nameLater := facts.nameLater
   nameCoherent := facts.nameCoherent
   nameGuards := facts.nameGuards
   matching := facts.matching}

/-- Direct application to the existing original Build theorem. The same
receipt-origin CallInput supplies use.carrier, so neither the raw carrier nor
its checked inlet/root/event is replaced. This supplies whole from the concrete
Name Delay construction and keeps the remaining entry facts explicit. -/
theorem generated_identity_from_name_delay
    (source : Identity) (route : Route)
    (telescope : Telescope (OriginalReturnWorld.S b D ViewData Rest Body View) View source.ambient)
    (assignment : FormalAssignment (OriginalReturnWorld.S b D ViewData Rest Body View) View)
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name)
    (registry : GuardRegistry (inputs operator references))
    (declarations : Declarations (inputs operator references) registry)
    (baseReadout : RuntimeReadout (OriginalReturnWorld.S b D ViewData Rest Body View) View)
    (views : ViewAssignment b Nat) (base : LocalAdmissions (OriginalReturnWorld.S b D ViewData Rest Body View) View)
    (ports : PortReadout (OriginalReturnWorld.S b D ViewData Rest Body View) View)
    (original : Kernel (Payload (OriginalReturnWorld.S b D ViewData Rest Body View) View))
    (prior : Prior (OriginalReturnWorld.S b D ViewData Rest Body View) View) (annotation : Option Declaration)
    (solves : let intro := source.introduction route telescope
      let readout := OriginalReturnWorld.valueReadout baseReadout source.parameter views
        (source.formalDescriptor route telescope assignment)
      Satisfies (closureKernel intro assignment (inputs operator references) registry declarations readout base ports original)
        (priorEnvironment intro prior)
        (Build source.context (.lambda ⟨source.lambdaSite, annotation⟩ source.parameter.formal
          source.parameter.pattern source.parameter.body))) :
    let intro := source.introduction route telescope
    let descriptor := source.formalDescriptor route telescope assignment
    let readout := OriginalReturnWorld.valueReadout baseReadout source.parameter views descriptor
    let kernel := closureKernel intro assignment (inputs operator references) registry declarations readout base ports original
    let environment := priorEnvironment intro prior
    ∃ description view,
      kernel.admitted environment (descriptionBinder source.parameter) description ∧
      kernel.admitted (environment.extend (descriptionBinder source.parameter) description)
        (viewBinder source.parameter) view ∧
      ∀ invocation, kernel.admitted
        ((environment.extend (descriptionBinder source.parameter) description).extend (viewBinder source.parameter) view)
        (invocationBinder source.parameter) invocation →
      ∃ receipt state,
        kernel.admitted
          (((environment.extend (descriptionBinder source.parameter) description).extend (viewBinder source.parameter) view).extend
            (invocationBinder source.parameter) invocation) (receiptBinder source.parameter) receipt ∧
        decode readout (receivedEnvironment environment source.parameter description view invocation receipt) = some state ∧
        formalContract state source.parameter = (intro.selection assignment).contract ∧
      ∃ origin : CallAtReceipt (inputs operator references) readout
          ((environment.extend (descriptionBinder source.parameter) description).extend (viewBinder source.parameter) view)
          source.parameter invocation state,
      ∀ packet nameFields dispatch occurrence,
        let received := receivedEnvironment environment source.parameter description view invocation receipt
        let use : Use b D ViewData Rest Body View source :=
          ⟨baseReadout, views, state, received, origin.input, origin.active, packet, nameFields, dispatch⟩
        let returned := scopeCandidate received occurrence (.runtime (.returnRebind (packet.outcome views source.parameter)))
        kernel.admitted received (returnBinder source.parameter) returned →
        ∀ delay (history : History operator references (use.carrier operator) delay),
        NativeExtraction operator references (use.carrier operator) delay history →
        EntryFacts operator references use descriptor →
        ∃ bodyState,
          decode readout (retainedEnvironment (received.extend (returnBinder source.parameter) returned)
            source.parameter) = some bodyState ∧
          bodyState.assignment.event = use.bound descriptor ∧
          formalContract bodyState source.parameter = (intro.selection assignment).contract ∧
          NameRealization operator references use descriptor := by
  obtain ⟨description, view, descriptionAdmitted, viewAdmitted, every⟩ :=
    generated_identity_name_realization source route telescope assignment operator references
      registry declarations baseReadout views base ports original prior annotation solves
  refine ⟨description, view, descriptionAdmitted, viewAdmitted, ?_⟩
  intro invocation invocationAdmitted
  obtain ⟨receipt, state, receiptAdmitted, decoded, selected, origin, enter⟩ :=
    every invocation invocationAdmitted
  refine ⟨receipt, state, receiptAdmitted, decoded, selected, origin, ?_⟩
  intro packet nameFields dispatch occurrence
  dsimp only
  intro returnedAdmitted delay history native facts
  exact enter packet nameFields dispatch occurrence returnedAdmitted
    (facts.toForceCut delay history native)

end YulangClosure.OriginalIdentityCarrier
