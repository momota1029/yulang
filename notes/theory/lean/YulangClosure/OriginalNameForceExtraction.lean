import YulangClosure.OriginalIdentityCarrier

/-!
The registered Name-argument Delay owns a concrete finite-prefix observation
interpreter. The opaque original Observation sort is instantiated by a tagged
sum retaining its entire prior domain. Only this native constructor's Force,
trace-form, phase and incidence readouts are supplied below; other original
calls and all independent semantic fields remain explicit.
-/
namespace YulangClosure.OriginalNameForceExtraction

open OriginalSource OriginalSourceInterpretation OriginalParameterSemantics
open NativeClosureEnvironment SourceIdentityWorld
open OriginalIdentityCarrier (NameDelay CaptureAt EventReadout)

inductive Failure where
  | missingBinding
  | uninitializedBinding
  | invalidAddress
  | dispatch (code : Nat)
  | invalidViewAddress
  | missingViewSnapshot
  | invalidView
  deriving DecidableEq

inductive Phase where
  | force
  | name
  | returned (address : Nat) (raw : Received Nat)
  | unavailable (error : Failure)

structure Machine (D ViewData Rest : Type) where
  world : World Name D Nat ViewData Nat Rest
  phase : Phase

abbrev Dispatch (D ViewData Rest : Type) :=
  NameDelay → World Name D Nat ViewData Nat Rest → Nat → Received Nat →
    Except Nat (Option Nat)

/-- Instruction::Name first resolves the lexical cell, then dispatches, then
consume/Observe checks the view. Dispatch's separate dictionary store is an
explicit external readout; no receipt is inserted on any failed branch. -/
def evaluate (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) : Except Failure (Nat × Received Nat) := do
  let address ← match lookupKey delay.name world.environments delay.environment with
    | none => .error .missingBinding
    | some address => .ok address
  if address < world.cells.size then
    let raw ← match world.cells.cell address with
      | none => .error .uninitializedBinding
      | some raw => .ok raw
    let chosen ← (dispatch delay world address raw).mapError Failure.dispatch
    if raw.view < world.receiving.views.size then
      match world.receiving.views.cell raw.view with
      | none => .error .missingViewSnapshot
      | some view =>
          if view.value = raw.value then .ok (address, raw.atName chosen)
          else .error .invalidView
    else .error .invalidViewAddress
  else .error .invalidAddress

def finish (delay : NameDelay) (world : World Name D Nat ViewData Nat Rest) :
    Except Failure (Nat × Received Nat) → Machine D ViewData Rest
  | .error error => ⟨world, .unavailable error⟩
  | .ok (address, raw) =>
      ⟨{world with receiving := world.receiving.record world.control.current raw.view delay.site none},
        .returned address raw⟩

/-- The actual known Delay is opened with substitution=None by Value entry.
That branch cannot change the saved environment. After its one Name/Observe
step the local constructor has stopped, including on every error. -/
def run (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) : Nat → Machine D ViewData Rest
  | 0 => ⟨world, .force⟩
  | 1 => ⟨world, .name⟩
  | _ + 2 => finish delay world (evaluate dispatch delay world)

def step (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (state : Machine D ViewData Rest) : Option (Machine D ViewData Rest) :=
  match state.phase with
  | .force => some ⟨state.world, .name⟩
  | .name => some (finish delay state.world (evaluate dispatch delay state.world))
  | .returned _ _ | .unavailable _ => none

theorem run_succ (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) (n : Nat) :
    run dispatch delay world (n + 1) =
      (step dispatch delay (run dispatch delay world n)).getD (run dispatch delay world n) := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
          cases outcome : evaluate dispatch delay world with
          | error error => simp [run, outcome, finish, step]
          | ok returned => cases returned; simp [run, outcome, finish, step]

theorem every_prefix (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) (n : Nat) :
    run dispatch delay world n = ⟨world, .force⟩ ∨
    run dispatch delay world n = ⟨world, .name⟩ ∨
    run dispatch delay world n = finish delay world (evaluate dispatch delay world) := by
  cases n with
  | zero => exact Or.inl rfl
  | succ n =>
      cases n with
      | zero => exact Or.inr (Or.inl rfl)
      | succ n => exact Or.inr (Or.inr rfl)

theorem failed_prefix (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) (error : Failure) (n : Nat)
    (failed : evaluate dispatch delay world = .error error) :
    run dispatch delay world (n + 2) = ⟨world, .unavailable error⟩ := by
  simp only [run, failed, finish]

theorem missing_binding (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest)
    (missing : lookupKey delay.name world.environments delay.environment = none) :
    evaluate dispatch delay world = .error .missingBinding := by
  simp [evaluate, missing, bind, Except.bind]

theorem uninitialized_binding (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) (address : Nat)
    (found : lookupKey delay.name world.environments delay.environment = some address)
    (bound : address < world.cells.size)
    (missing : world.cells.cell address = none) :
    evaluate dispatch delay world = .error .uninitializedBinding := by
  simp [evaluate, found, bound, missing, bind, Except.bind]

theorem dispatch_failure (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) (address : Nat) (raw : Received Nat) (code : Nat)
    (found : lookupKey delay.name world.environments delay.environment = some address)
    (bound : address < world.cells.size)
    (stored : world.cells.cell address = some raw)
    (failed : dispatch delay world address raw = .error code) :
    evaluate dispatch delay world = .error (.dispatch code) := by
  simp [evaluate, found, bound, stored, failed, Except.mapError, bind, Except.bind]

theorem initialized_evaluate (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) (address : Nat) (raw : Received Nat)
    (chosen : Option Nat)
    (found : lookupKey delay.name world.environments delay.environment = some address)
    (bound : address < world.cells.size)
    (stored : world.cells.cell address = some raw)
    (dispatched : dispatch delay world address raw = .ok chosen)
    (viewBound : raw.view < world.receiving.views.size)
    (matching : Matches world.receiving raw) :
    evaluate dispatch delay world = .ok (address, raw.atName chosen) := by
  obtain ⟨view, viewFound, same⟩ := matching
  simp [evaluate, found, bound, stored, dispatched, viewBound, Except.mapError, viewFound, same, bind, Except.bind]

/-- Native vector indexing would panic here. This is a malformed raw-address
boundary, not a new normal RuntimeUnavailable result and not a dropped prefix. -/
theorem dangling_address (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) (address : Nat)
    (found : lookupKey delay.name world.environments delay.environment = some address)
    (outside : world.cells.size ≤ address) :
    evaluate dispatch delay world = .error .invalidAddress := by
  simp [evaluate, found, Nat.not_lt.mpr outside, bind, Except.bind]

inductive Resolution where
  | parameter | local | catchBinder | caseBinder
  | moduleDef | imported | unresolved | ambiguous
  deriving DecidableEq

inductive Consumption where
  | observe | execute
  deriving DecidableEq

structure NameMode where
  resolution : Resolution
  consumption : Consumption

def NameMode.lexicalObserve : NameMode → Bool
  | ⟨.parameter, .observe⟩ | ⟨.local, .observe⟩
  | ⟨.catchBinder, .observe⟩ | ⟨.caseBinder, .observe⟩ => true
  | _ => false

def Machine.project (state : Machine D ViewData Rest) :
    OriginalIdentityCarrier.Machine D ViewData Rest :=
  ⟨state.world, match state.phase with
    | .force => .force
    | .name => .name
    | .returned _ raw => .returned raw
    | .unavailable _ => .unavailable⟩

/-- Tags contain native data only, never a result proof, trace membership,
world certificate or prefix-extraction equation. Returned cell addresses are
the actual addresses computed by evaluate. -/
structure Observation (b : Sorts) where
  carrier : b.Carrier
  root : b.Root
  delay : NameDelay
  fuel : Nat
  phase : Phase

abbrev Base (b : Sorts) : Sorts :=
  {b with Observation := Sum b.Observation (Observation b)}

abbrev S (b : Sorts) (D ViewData Rest Body View : Type) :=
  OriginalReturnWorld.S (Base b) D ViewData Rest Body View

variable {b : Sorts} {D ViewData Rest Body View : Type}

/-- Only raw native owners: actual carrier handle, executable store, dispatch
call result, and current residual/evidence fields. None is a semantic result. -/
structure Native (b : Sorts) (D ViewData Rest Body View : Type) where
  handle : b.Carrier → Option Nat
  executables : Event (S b D ViewData Rest Body View) →
    Store (Option (Closure (Source .expression)))
  nameMode : Event (S b D ViewData Rest Body View) → Nat → Option NameMode
  dispatch : Dispatch D ViewData Rest
  fields : NameDelay → Event (S b D ViewData Rest Body View) → EventReadout (Base b)

def owner (native : Native b D ViewData Rest Body View)
    (input : CarrierInput (S b D ViewData Rest Body View))
    (demand : Event (S b D ViewData Rest Body View)) : Option NameDelay := do
  let handle ← native.handle input.carrier
  let executable ← (native.executables demand).cell handle
  let closure ← executable
  let mode ← native.nameMode demand handle
  if mode.lexicalObserve then
    match closure.body with
    | .name ⟨site, none⟩ name => some ⟨handle, closure.savedEnvironment, name, site⟩
    | _ => none
  else none

def eventAt (native : Native b D ViewData Rest Body View) (delay : NameDelay)
    (demand : Event (S b D ViewData Rest Body View)) (n : Nat) :
    Event (S b D ViewData Rest Body View) :=
  if n = 0 then demand else
    let readout := native.fields delay demand
    let fields := readout.fields n
    {demand with
      history := fields.history
      current := {demand.current with
        residual := readout.residual n
        world := (run native.dispatch delay demand.current.world n).world}
      eta := {demand.eta with original := fields.assignment}
      witness := {demand.witness with current := fields.witness}
      scope := fields.scope, authority := fields.authority,
      incidence := fields.incidence, dictionary := fields.dictionary}

def observe (native : Native b D ViewData Rest Body View)
    (input : CarrierInput (S b D ViewData Rest Body View))
    (demand : Event (S b D ViewData Rest Body View)) (delay : NameDelay) (n : Nat) :
    RawObservation (S b D ViewData Rest Body View) :=
  ⟨.inr ⟨input.carrier, input.root, delay, n, (run native.dispatch delay demand.current.world n).phase⟩,
    eventAt native delay demand n⟩

def phaseValid : Phase → Prop
  | .unavailable _ => False
  | _ => True

def form (row : TraceRow (S b D ViewData Rest Body View)) (observation : Observation b) :
    TraceForm (S b D ViewData Rest Body View) :=
  match observation.phase with
  | .returned address raw =>
      .pureReturn ⟨row.event.eta.views.descriptor address raw.view,
        row.event.eta.views.value raw.value, row.event.eta.views.root raw.value, row.event⟩
  | _ => .unfinished

/-- Full graph of every finite prefix, including failed prefixes. The checked
interface, acceptance, guards and meanings do not select this graph. -/
def force (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    (input : CarrierInput (S b D ViewData Rest Body View))
    (demand : Event (S b D ViewData Rest Body View))
    (raw : RawObservation (S b D ViewData Rest Body View)) : Prop :=
  match owner native input demand with
  | none => base.force input demand raw
  | some delay => ∃ n, raw = observe native input demand delay n

/-- Incidence decodes this same raw tag and checks the actual designated
constructor, input identity, fuel and current event by recomputation. -/
def incidence (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    (row : CarrierRow (S b D ViewData Rest Body View))
    (demand : Event (S b D ViewData Rest Body View))
    (raw : RawObservation (S b D ViewData Rest Body View)) : Prop :=
  match owner native row.input demand with
  | none => base.forceIncidence row demand raw
  | some delay => match raw.observation with
    | .inl _ => False
    | .inr observed => observed.carrier = row.carrier ∧ observed.root = row.root ∧
        observed.delay = delay ∧ raw = observe native row.input demand delay observed.fuel

def inputs (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View) : Inputs (S b D ViewData Rest Body View) :=
  {base with
    force := force base native
    forceIncidence := incidence base native
    traceForm := fun row => match row.observation with
      | .inl _ => base.traceForm row
      | .inr observed => form row observed
    observationGuards := fun row => match row.observation with
      | .inl _ => base.observationGuards row
      | .inr observed => {base.observationGuards row with
          phase := (base.observationGuards row).phase ∧ phaseValid observed.phase}}

theorem owner_from_allocation (native : Native b D ViewData Rest Body View)
    (input : CarrierInput (S b D ViewData Rest Body View))
    (demand : Event (S b D ViewData Rest Body View)) (delay : NameDelay)
    (allocation : OriginalIdentityCarrier.Allocation delay)
    (handle : native.handle input.carrier = some delay.handle)
    (store : native.executables demand = allocation.after)
    (mode : NameMode) (nativeMode : native.nameMode demand delay.handle = some mode)
    (lexical : mode.lexicalObserve = true) :
    owner native input demand = some delay := by
  have code := (OriginalIdentityCarrier.allocation_keeps_actual_code allocation).1
  simp only [owner, handle, Option.bind_eq_bind, Option.bind_some, store, code,
    nativeMode, lexical, ite_true]
  cases delay
  rfl

theorem other_force_unchanged (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    (input : CarrierInput (S b D ViewData Rest Body View))
    (demand : Event (S b D ViewData Rest Body View))
    (raw : RawObservation (S b D ViewData Rest Body View))
    (other : owner native input demand = none) :
    (inputs base native).force input demand raw ↔ base.force input demand raw := by
  simp only [inputs, force, other]

theorem other_incidence_unchanged (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    (row : CarrierRow (S b D ViewData Rest Body View))
    (demand : Event (S b D ViewData Rest Body View))
    (raw : RawObservation (S b D ViewData Rest Body View))
    (other : owner native row.input demand = none) :
    (inputs base native).forceIncidence row demand raw ↔ base.forceIncidence row demand raw := by
  simp only [inputs, incidence, other]

theorem checked_domain_unchanged (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    {row : ValueRow (S b D ViewData Rest Body View)} (challenge : Challenge row) :
    CheckedDomain (inputs base native) challenge ↔ CheckedDomain base challenge := Iff.rfl

theorem actual_admission_unchanged (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    {row : ValueRow (S b D ViewData Rest Body View)} (provider : b.Provider)
    (challenge : Challenge row) :
    ActualAdm (inputs base native) provider challenge ↔ ActualAdm base provider challenge := Iff.rfl

theorem prior_observation_unchanged (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    (interface : b.Interface) (observation : b.Observation)
    (event : Event (S b D ViewData Rest Body View)) :
    (inputs base native).traceForm ⟨interface, .inl observation, event⟩ =
      base.traceForm ⟨interface, .inl observation, event⟩ ∧
    (inputs base native).observationGuards ⟨interface, .inl observation, event⟩ =
      base.observationGuards ⟨interface, .inl observation, event⟩ := ⟨rfl, rfl⟩

theorem other_owners_unchanged (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View) :
    (inputs base native).execute = base.execute ∧
    (inputs base native).demand = base.demand ∧
    (inputs base native).compatible = base.compatible ∧
    (inputs base native).carrierAccepted = base.carrierAccepted ∧
    (@Inputs.checkedObservation _ (inputs base native)) = (@Inputs.checkedObservation _ base) ∧
    (inputs base native).observationFields = base.observationFields :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem every_owned_prefix (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    (input : CarrierInput (S b D ViewData Rest Body View))
    (demand : Event (S b D ViewData Rest Body View)) (delay : NameDelay) (n : Nat)
    (registered : owner native input demand = some delay) :
    (inputs base native).force input demand (observe native input demand delay n) := by
  simp only [inputs, force, registered]
  exact ⟨n, rfl⟩

theorem force_incidence (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    (row : CarrierRow (S b D ViewData Rest Body View))
    (demand : Event (S b D ViewData Rest Body View)) (delay : NameDelay)
    (raw : RawObservation (S b D ViewData Rest Body View))
    (registered : owner native row.input demand = some delay)
    (forced : (inputs base native).force row.input demand raw) :
    (inputs base native).forceIncidence row demand raw := by
  change force base native row.input demand raw at forced
  rw [force, registered] at forced
  obtain ⟨n, rfl⟩ := forced
  change incidence base native row demand (observe native row.input demand delay n)
  rw [incidence, registered]
  exact ⟨rfl, rfl, rfl, rfl⟩

def Phase.result : Phase → Option (Received Nat)
  | .returned _ raw => some raw
  | _ => none

theorem project_run (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) (address : Nat) (raw : Received Nat)
    (chosen : Option Nat)
    (found : lookupKey delay.name world.environments delay.environment = some address)
    (bound : address < world.cells.size)
    (stored : world.cells.cell address = some raw)
    (dispatched : dispatch delay world address raw = .ok chosen)
    (viewBound : raw.view < world.receiving.views.size)
    (matching : Matches world.receiving raw) (n : Nat) :
    (run dispatch delay world n).project = OriginalIdentityCarrier.run delay chosen world n := by
  have read : NativeClosureEnvironment.observe (fun name => decide (name = delay.name))
      world.environments delay.environment world.cells.cell = some raw := by
    change (lookupKey delay.name world.environments delay.environment).bind _ = _
    rw [found]
    exact stored
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
          rw [OriginalIdentityCarrier.run_return delay chosen world raw read matching n]
          simp only [run, initialized_evaluate dispatch delay world address raw chosen found bound stored dispatched viewBound matching,
            finish, Machine.project, OriginalIdentityCarrier.namedWorld, Received.atName]

theorem prefix_event (native : Native b D ViewData Rest Body View)
    (delay : NameDelay) (demand : Event (S b D ViewData Rest Body View))
    (capture : CaptureAt delay demand) (chosen : Option Nat)
    (bound : capture.address < demand.current.world.cells.size)
    (dispatched : native.dispatch delay demand.current.world capture.address capture.raw = .ok chosen)
    (viewBound : capture.raw.view < demand.current.world.receiving.views.size)
    (n : Nat) :
    eventAt native delay demand n =
      OriginalIdentityCarrier.eventAt delay chosen demand (native.fields delay demand) n := by
  have same := congrArg OriginalIdentityCarrier.Machine.world
    (project_run native.dispatch delay demand.current.world capture.address capture.raw chosen
      capture.lookup bound capture.stored dispatched viewBound capture.matching n)
  by_cases zero : n = 0
  · simp [eventAt, OriginalIdentityCarrier.eventAt, zero]
  · simp only [Machine.project] at same
    simp only [eventAt, OriginalIdentityCarrier.eventAt, zero, ite_false, same]

theorem prefix_valid (native : Native b D ViewData Rest Body View)
    (delay : NameDelay) (demand : Event (S b D ViewData Rest Body View))
    (capture : CaptureAt delay demand) (chosen : Option Nat)
    (bound : capture.address < demand.current.world.cells.size)
    (dispatched : native.dispatch delay demand.current.world capture.address capture.raw = .ok chosen)
    (viewBound : capture.raw.view < demand.current.world.receiving.views.size)
    (n : Nat) : phaseValid (run native.dispatch delay demand.current.world n).phase := by
  cases n with
  | zero => trivial
  | succ n =>
      cases n with
      | zero => trivial
      | succ n =>
          simp only [run, initialized_evaluate native.dispatch delay demand.current.world
            capture.address capture.raw chosen capture.lookup bound capture.stored dispatched viewBound capture.matching,
            finish, phaseValid]

theorem prefix_result (native : Native b D ViewData Rest Body View)
    (delay : NameDelay) (demand : Event (S b D ViewData Rest Body View))
    (capture : CaptureAt delay demand) (chosen : Option Nat)
    (bound : capture.address < demand.current.world.cells.size)
    (dispatched : native.dispatch delay demand.current.world capture.address capture.raw = .ok chosen)
    (viewBound : capture.raw.view < demand.current.world.receiving.views.size)
    (n : Nat) (returned : Received Nat)
    (complete : (run native.dispatch delay demand.current.world n).phase.result = some returned) :
    (OriginalIdentityCarrier.run delay chosen demand.current.world n).phase = .returned returned := by
  rw [← project_run native.dispatch delay demand.current.world capture.address capture.raw chosen
    capture.lookup bound capture.stored dispatched viewBound capture.matching n]
  cases phase : (run native.dispatch delay demand.current.world n).phase <;>
    simp [Phase.result, phase] at complete
  case returned address raw =>
    cases complete
    simp [Machine.project, phase]

theorem prefix_form (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    (input : CarrierInput (S b D ViewData Rest Body View)) (interface : b.Interface)
    (delay : NameDelay) (demand : Event (S b D ViewData Rest Body View))
    (capture : CaptureAt delay demand) (chosen : Option Nat)
    (bound : capture.address < demand.current.world.cells.size)
    (dispatched : native.dispatch delay demand.current.world capture.address capture.raw = .ok chosen)
    (viewBound : capture.raw.view < demand.current.world.receiving.views.size)
    (n : Nat) :
    (inputs base native).traceForm ((observe native input demand delay n).atInterface interface) =
      OriginalIdentityCarrier.resultForm demand.eta.views capture.descriptor (eventAt native delay demand n)
        (run native.dispatch delay demand.current.world n).phase.result := by
  cases n with
  | zero => rfl
  | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
          simp [inputs, observe, RawObservation.atInterface, form, run,
            initialized_evaluate native.dispatch delay demand.current.world capture.address capture.raw chosen
              capture.lookup bound capture.stored dispatched viewBound capture.matching,
            finish, Phase.result, OriginalIdentityCarrier.resultForm, eventAt,
            OriginalIdentityCarrier.CaptureAt.descriptor, Received.atName]

/-- Failed runs remain in Force. The concrete phase guard records their
failure; they are never removed by semantic membership or reported as Return. -/
theorem failed_observation (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    (input : CarrierInput (S b D ViewData Rest Body View)) (interface : b.Interface)
    (delay : NameDelay) (demand : Event (S b D ViewData Rest Body View))
    (error : Failure) (n : Nat)
    (registered : owner native input demand = some delay)
    (failed : evaluate native.dispatch delay demand.current.world = .error error) :
    (inputs base native).force input demand (observe native input demand delay (n + 2)) ∧
    (inputs base native).traceForm
      ((observe native input demand delay (n + 2)).atInterface interface) = .unfinished ∧
    ¬ ((inputs base native).observationGuards
      ((observe native input demand delay (n + 2)).atInterface interface)).Valid := by
  refine ⟨every_owned_prefix base native input demand delay (n + 2) registered, ?_, ?_⟩
  · simp [inputs, observe, RawObservation.atInterface, form, run, failed, finish]
  · simp [inputs, observe, RawObservation.atInterface, run, failed, finish,
      ObservationGuards.Valid, phaseValid]

theorem return_receipt (native : Native b D ViewData Rest Body View)
    (delay : NameDelay) (demand : Event (S b D ViewData Rest Body View))
    (capture : CaptureAt delay demand) (chosen : Option Nat)
    (bound : capture.address < demand.current.world.cells.size)
    (dispatched : native.dispatch delay demand.current.world capture.address capture.raw = .ok chosen)
    (viewBound : capture.raw.view < demand.current.world.receiving.views.size)
    (n : Nat) :
    let after := eventAt native delay demand (n + 2)
    after.current.world.receiving.receipts.cell demand.current.world.receiving.receipts.size =
      some ⟨demand.current.world.control.current, capture.raw.view, delay.site, none⟩ ∧
    after.current.world.receiving.receipts.size = demand.current.world.receiving.receipts.size + 1 ∧
    after.current.world.receiving.views = demand.current.world.receiving.views ∧
    after.current.world.cells = demand.current.world.cells := by
  simp [eventAt, run, initialized_evaluate native.dispatch delay demand.current.world capture.address
    capture.raw chosen capture.lookup bound capture.stored dispatched viewBound capture.matching,
    finish, Received.atName, Receiving.record]
  exact ⟨push_current _ _, rfl⟩

/-- The remaining independent semantic/evidence owners. There is no Force
equation, prefix witness, trace form, incidence, returned member, or trace
Meaning in this record. Dictionary dispatch success is explicit raw evidence.
All primitive guards and positive fields of the original base are retained. -/
structure Independent
    (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View) (references : Body → Nat → Option Name)
    (input : CarrierInput (S b D ViewData Rest Body View)) (interface : b.Interface)
    (delay : NameDelay) (demand : Event (S b D ViewData Rest Body View))
    (capture : CaptureAt delay demand) where
  chosen : Option Nat
  addressBound : capture.address < demand.current.world.cells.size
  dispatched : native.dispatch delay demand.current.world capture.address capture.raw = .ok chosen
  viewBound : capture.raw.view < demand.current.world.receiving.views.size
  compatible : ∀ n, base.compatible demand (eventAt native delay demand n)
  coherent : ∀ n, base.eventCoherent (eventAt native delay demand n)
  worldGuards : ∀ n, (base.worldGuards (eventAt native delay demand n)).Valid
  guards : ∀ n, (base.observationGuards
    ((observe native input demand delay n).atInterface interface)).Valid
  fields : ∀ n, OriginalIdentityCarrier.WorldFields
    (OriginalParameterSemantics.inputs (inputs base native) references)
    (eventAt native delay demand n)
    (base.observationFields ((observe native input demand delay n).atInterface interface))

def Independent.execution
    {base : Inputs (S b D ViewData Rest Body View)}
    {native : Native b D ViewData Rest Body View} {references : Body → Nat → Option Name}
    {input : CarrierInput (S b D ViewData Rest Body View)} {interface : b.Interface}
    {delay : NameDelay} {demand : Event (S b D ViewData Rest Body View)}
    {capture : CaptureAt delay demand}
    (evidence : Independent base native references input interface delay demand capture) :
    OriginalIdentityCarrier.Execution (inputs base native) delay demand where
  dispatch := evidence.chosen
  readout := native.fields delay demand
  compatible n := by
    change base.compatible demand _
    rw [← prefix_event native delay demand capture evidence.chosen evidence.addressBound evidence.dispatched evidence.viewBound n]
    exact evidence.compatible n
  coherent n := by
    change base.eventCoherent _
    rw [← prefix_event native delay demand capture evidence.chosen evidence.addressBound evidence.dispatched evidence.viewBound n]
    exact evidence.coherent n
  worldGuards n := by
    change (base.worldGuards _).Valid
    rw [← prefix_event native delay demand capture evidence.chosen evidence.addressBound evidence.dispatched evidence.viewBound n]
    exact evidence.worldGuards n

/-- The native graph supplies fuel, raw result, event and form by computation.
Only the unchanged independent guard/field owners come from evidence. -/
def Independent.observationAt
    {base : Inputs (S b D ViewData Rest Body View)}
    {native : Native b D ViewData Rest Body View} {references : Body → Nat → Option Name}
    {input : CarrierInput (S b D ViewData Rest Body View)} {interface : b.Interface}
    {delay : NameDelay} {demand : Event (S b D ViewData Rest Body View)}
    {capture : CaptureAt delay demand}
    (evidence : Independent base native references input interface delay demand capture) (n : Nat) :
    OriginalIdentityCarrier.ObservationAt (inputs base native) references interface delay demand capture
      evidence.execution (observe native input demand delay n) where
  fuel := n
  result := (run native.dispatch delay demand.current.world n).phase.result
  complete returned complete := prefix_result native delay demand capture evidence.chosen evidence.addressBound evidence.dispatched evidence.viewBound
    n returned complete
  event := prefix_event native delay demand capture evidence.chosen evidence.addressBound evidence.dispatched evidence.viewBound n
  form := prefix_form base native input interface delay demand capture evidence.chosen evidence.addressBound evidence.dispatched evidence.viewBound n
  guards := by
    have valid := prefix_valid native delay demand capture evidence.chosen evidence.addressBound evidence.dispatched evidence.viewBound n
    simpa only [inputs, observe, RawObservation.atInterface, ObservationGuards.Valid, valid, and_true]
      using evidence.guards n
  fields := evidence.fields n

def Independent.everyObservation
    {base : Inputs (S b D ViewData Rest Body View)}
    {native : Native b D ViewData Rest Body View} {references : Body → Nat → Option Name}
    {input : CarrierInput (S b D ViewData Rest Body View)} {interface : b.Interface}
    {delay : NameDelay} {demand : Event (S b D ViewData Rest Body View)}
    {capture : CaptureAt delay demand}
    (evidence : Independent base native references input interface delay demand capture)
    (registered : owner native input demand = some delay)
    (raw : RawObservation (S b D ViewData Rest Body View))
    (forced : (inputs base native).force input demand raw) :
    OriginalIdentityCarrier.ObservationAt (inputs base native) references interface delay demand capture
      evidence.execution raw := by
  change force base native input demand raw at forced
  rw [force, registered] at forced
  let n := match raw.observation with | .inl _ => 0 | .inr observed => observed.fuel
  have same : raw = observe native input demand delay n := by
    obtain ⟨fuel, same⟩ := forced
    subst raw
    rfl
  rw [same]
  exact evidence.observationAt n

/-- Actual source-owned extraction into the frozen Carrier interface. History
is still independently supplied, including its noncircular surrounding worlds.
No NativeExtraction, ObservationAt or whole-carrier premise is accepted here. -/
def nativeExtraction
    (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View) (references : Body → Nat → Option Name)
    (row : CarrierRow (S b D ViewData Rest Body View)) (delay : NameDelay)
    (history : OriginalIdentityCarrier.History (inputs base native) references row delay)
    (registered : ∀ event, OriginalIdentityCarrier.Reach (inputs base native) row.event event →
      ∀ demand, (inputs base native).demand (row.atEvent event) demand →
        owner native (row.atEvent event).input demand = some delay)
    (evidence : ∀ event, (reachable : OriginalIdentityCarrier.Reach (inputs base native) row.event event) →
      ∀ demand, (demanded : (inputs base native).demand (row.atEvent event) demand) →
        Independent base native references (row.atEvent event).input row.interface delay demand
          (history.capture demand (.later reachable (history.demand event reachable demand demanded)))) :
    OriginalIdentityCarrier.NativeExtraction (inputs base native) references row delay history where
  execution event reachable demand demanded := (evidence event reachable demand demanded).execution
  observations event reachable demand demanded raw forced :=
    (evidence event reachable demand demanded).everyObservation
      (registered event reachable demand demanded) raw forced
  incidence event reachable demand demanded raw forced :=
    force_incidence base native (row.atEvent event) demand delay raw
      (registered event reachable demand demanded) forced

theorem name_delay_from_native_prefixes
    (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View) (references : Body → Nat → Option Name)
    (row : CarrierRow (S b D ViewData Rest Body View)) (delay : NameDelay)
    (history : OriginalIdentityCarrier.History (inputs base native) references row delay)
    (registered : ∀ event, OriginalIdentityCarrier.Reach (inputs base native) row.event event →
      ∀ demand, (inputs base native).demand (row.atEvent event) demand →
        owner native (row.atEvent event).input demand = some delay)
    (evidence : ∀ event, (reachable : OriginalIdentityCarrier.Reach (inputs base native) row.event event) →
      ∀ demand, (demanded : (inputs base native).demand (row.atEvent event) demand) →
        Independent base native references (row.atEvent event).input row.interface delay demand
          (history.capture demand (.later reachable (history.demand event reachable demand demanded)))) :
    Meaning (OriginalParameterSemantics.inputs (inputs base native) references) (.carrier row) :=
  OriginalIdentityCarrier.name_delay_whole (inputs base native) references row delay history
    (nativeExtraction base native references row delay history registered evidence)

/-- Native receiving.matches_value directly indexes its vector. A view
outside the vector is a panic boundary, separate from a mismatched value. -/
theorem dangling_view (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) (address : Nat) (raw : Received Nat)
    (chosen : Option Nat)
    (found : lookupKey delay.name world.environments delay.environment = some address)
    (bound : address < world.cells.size) (stored : world.cells.cell address = some raw)
    (dispatched : dispatch delay world address raw = .ok chosen)
    (outside : world.receiving.views.size ≤ raw.view) :
    evaluate dispatch delay world = .error .invalidViewAddress := by
  simp [evaluate, found, bound, stored, dispatched, Nat.not_lt.mpr outside,
    Except.mapError, bind, Except.bind]

/-- A hole below views.size is not a native Vec<View> state. Retaining this
malformed Store projection as its own outcome avoids treating it as either a
successful view match or a normal native RuntimeUnavailable. -/
theorem missing_view (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) (address : Nat) (raw : Received Nat)
    (chosen : Option Nat)
    (found : lookupKey delay.name world.environments delay.environment = some address)
    (bound : address < world.cells.size) (stored : world.cells.cell address = some raw)
    (dispatched : dispatch delay world address raw = .ok chosen)
    (viewBound : raw.view < world.receiving.views.size)
    (missing : world.receiving.views.cell raw.view = none) :
    evaluate dispatch delay world = .error .missingViewSnapshot := by
  simp [evaluate, found, bound, stored, dispatched, viewBound, missing, Except.mapError, bind, Except.bind]

theorem mismatched_view (dispatch : Dispatch D ViewData Rest) (delay : NameDelay)
    (world : World Name D Nat ViewData Nat Rest) (address : Nat) (raw : Received Nat)
    (chosen : Option Nat) (view : SourceIdentityWorld.View Nat ViewData)
    (found : lookupKey delay.name world.environments delay.environment = some address)
    (bound : address < world.cells.size) (stored : world.cells.cell address = some raw)
    (dispatched : dispatch delay world address raw = .ok chosen)
    (viewBound : raw.view < world.receiving.views.size)
    (viewFound : world.receiving.views.cell raw.view = some view) (different : view.value ≠ raw.value) :
    evaluate dispatch delay world = .error .invalidView := by
  simp [evaluate, found, bound, stored, dispatched, viewBound, viewFound, different,
    Except.mapError, bind, Except.bind]

/-- The actual early dispatch_name return when the program has no dictionary
machine. The arbitrary value's existing dispatch is preserved. Other programs
retain the complete result/error readout in Native.dispatch. -/
def noDictionaries : Dispatch D ViewData Rest := fun _ _ _ raw => .ok raw.dispatch

/-- Native bind supplies lookup, initialized raw record and Value entry mode.
The parent may be any actual earlier lexical environment, not just the latest. -/
def capturedByBind (before : Event (S b D ViewData Rest Body View))
    (parent : Nat) (name : Name) (raw : Received Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields (Base b)) (handle site : Nat)
    (matching : Matches before.current.world.receiving raw) :
    CaptureAt ⟨handle, before.current.world.environments.size, name, site⟩
      (bindEvent before parent name raw node found descriptor fields) where
  address := before.current.world.cells.size
  raw := raw.asValue
  lookup := parameter_shadows before.current.world.environments parent
    before.current.world.cells.size name node.dispatch
  stored := push_current before.current.world.cells raw.asValue
  mode := rfl
  matching := matching

theorem captured_by_bind_bound (before : Event (S b D ViewData Rest Body View))
    (parent : Nat) (name : Name) (raw : Received Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields (Base b)) (handle site : Nat)
    (matching : Matches before.current.world.receiving raw) :
    (capturedByBind before parent name raw node found descriptor fields handle site matching).address <
      (bindEvent before parent name raw node found descriptor fields).current.world.cells.size :=
  Nat.lt_succ_self _

theorem bound_name_evaluate (before : Event (S b D ViewData Rest Body View))
    (parent : Nat) (name : Name) (raw : Received Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields (Base b)) (handle site : Nat)
    (matching : Matches before.current.world.receiving raw)
    (viewBound : raw.view < before.current.world.receiving.views.size) :
    evaluate noDictionaries ⟨handle, before.current.world.environments.size, name, site⟩
      (bindEvent before parent name raw node found descriptor fields).current.world =
      .ok (before.current.world.cells.size, raw.asValue.atName raw.dispatch) := by
  let capture := capturedByBind before parent name raw node found descriptor fields handle site matching
  exact initialized_evaluate noDictionaries _ _ capture.address capture.raw raw.dispatch
    capture.lookup (captured_by_bind_bound before parent name raw node found descriptor fields handle site matching)
    capture.stored rfl viewBound capture.matching

/-- A constructor application with no supplied successful Force, raw prefix,
Return form, Name lookup or cell-bound premise. The cell is bound, the Delay
code is allocated, the exact instruction mode is read, then the graph emits
its actual Return at its receipt event. No surrounding world membership is
needed for this operational theorem. -/
theorem allocated_bound_force
    (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    (input : CarrierInput (S b D ViewData Rest Body View)) (interface : b.Interface)
    (before : Event (S b D ViewData Rest Body View))
    (parent : Nat) (name : Name) (raw : Received Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields (Base b)) (handle site : Nat)
    (matching : Matches before.current.world.receiving raw)
    (viewBound : raw.view < before.current.world.receiving.views.size)
    (allocation : OriginalIdentityCarrier.Allocation
      ⟨handle, before.current.world.environments.size, name, site⟩)
    (decoded : native.handle input.carrier = some handle)
    (allocated : native.executables (bindEvent before parent name raw node found descriptor fields) = allocation.after)
    (mode : NameMode)
    (nativeMode : native.nameMode (bindEvent before parent name raw node found descriptor fields) handle = some mode)
    (lexical : mode.lexicalObserve = true) (plain : native.dispatch = noDictionaries) (n : Nat) :
    let demand := bindEvent before parent name raw node found descriptor fields
    let delay : NameDelay := ⟨handle, before.current.world.environments.size, name, site⟩
    let rawObservation := observe native input demand delay (n + 2)
    (inputs base native).force input demand rawObservation ∧
    (inputs base native).traceForm (rawObservation.atInterface interface) =
      .pureReturn ⟨descriptor, before.eta.views.value raw.value, before.eta.views.root raw.value,
        rawObservation.event⟩ := by
  dsimp only
  refine ⟨every_owned_prefix base native input _ _ (n + 2)
    (owner_from_allocation native input _ _ allocation decoded allocated mode nativeMode lexical), ?_⟩
  have computed := bound_name_evaluate before parent name raw node found descriptor fields handle site matching viewBound
  simp only [inputs, observe, RawObservation.atInterface, run, plain, computed, finish]
  simp [form, eventAt, bindEvent, OriginalParameterWorld.installValueContract,
    Received.asValue, Received.atName]

end YulangClosure.OriginalNameForceExtraction
