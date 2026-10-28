import YulangClosure.OriginalFormalShared
import YulangClosure.OriginalForcedParameter

/-!
The Value-entry Return/rebind readout at its own decoded Event.

The raw Return supplies its complete current native snapshot. In particular,
the world after forcing is not identified with the earlier receipt world.
The actual allocation determines the fresh cell and the returned Outcome;
the ordinary independent readout supplies the remaining current event fields.
This module does not assert authenticity of arbitrary raw Return packets or
the full original source/native interpretation.
-/
namespace YulangClosure.OriginalReturnWorld

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalParameterWorld OriginalParameterSemantics
open OriginalWorldReadout OriginalFormalShared OriginalForcedParameter
open NativeClosureEnvironment SourceIdentityWorld

abbrev S (b : Sorts) (D ViewData Rest Body View : Type) :=
  NS b D Nat ViewData Nat Rest Body View

/-- Independent actual Return operands. The complete post-Force snapshot is
retained, including provider, alias, residual, receiving and control data.
There is no semantic membership or post-bind equality in this record. -/
structure Packet (b : Sorts) (D ViewData Rest Body View : Type) where
  snapshot : Snapshot b D Nat ViewData Nat Rest Body
  raw : Received Nat
  parent : Nat
  node : Node Name D
  found : nodeAt snapshot.world.environments parent = some node
  history : b.History
  observation : b.Observation
  endpoints : List (Endpoint × Object (S b D ViewData Rest Body View))
  bindings : List (Name × Nat)

variable {b s : Sorts} {D ViewData Rest Body View : Type}

def liftViews (views : ViewAssignment b Nat) :
    ViewAssignment (S b D ViewData Rest Body View) Nat :=
  ⟨views.descriptor, views.interface, views.value, views.carrier, views.root⟩

/-- The Return/rebind field includes the actual allocation. Earlier receiving
or primitive receipt fields are not rewritten. -/
def Packet.outcome (packet : Packet b D ViewData Rest Body View)
    (views : ViewAssignment b Nat) (parameter : Parameter) :
    Outcome (S b D ViewData Rest Body View) :=
  let next := bindValue packet.snapshot.world packet.parent parameter.formal.name
    packet.raw packet.node packet.found
  ⟨packet.observation,
    some (.value (views.value packet.raw.value) (views.root packet.raw.value)),
    ⟨packet.history, {packet.snapshot with world := next}⟩,
    packet.endpoints,
    packet.bindings ++ [(parameter.formal.name, packet.snapshot.world.cells.size)]⟩

def returnAddress (parameter : Parameter) (outcome : Outcome s) : Option Nat :=
  (outcome.bindings.reverse.find? (fun pair => pair.1 == parameter.formal.name)).map Prod.snd

theorem packet_address (packet : Packet b D ViewData Rest Body View)
    (views : ViewAssignment b Nat) (parameter : Parameter) :
    returnAddress parameter (packet.outcome views parameter) =
      some packet.snapshot.world.cells.size := by
  simp [returnAddress, Packet.outcome]

/-- Assignment fields are interpreted at the actual Return, and only the
fresh cell receives the preselected descriptor. All other runtime kinds and
all other binders keep the original readout. -/
def valueReadout (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (parameter : Parameter) (views : ViewAssignment b Nat) (descriptor : b.Descriptor) :
    RuntimeReadout (S b D ViewData Rest Body View) View where
  eta := fun frames before binder raw =>
    match raw with
    | .returnRebind outcome =>
      if binder = returnBinder parameter then
        match returnAddress parameter outcome with
        | some address => ⟨(base.eta frames before binder raw).original,
            installValueContract views address descriptor⟩
        | none => base.eta frames before binder raw
      else base.eta frames before binder raw
    | _ => base.eta frames before binder raw
  witness := fun frames before binder raw =>
    match raw with
    | .returnRebind _ =>
      if binder = returnBinder parameter then
        ⟨(base.witness frames before binder raw).current, before.witness.shared⟩
      else base.witness frames before binder raw
    | _ => base.witness frames before binder raw
  scope := base.scope
  authority := base.authority
  incidence := base.incidence
  dictionary := base.dictionary

def fields (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (frames : List (Frame (Payload (S b D ViewData Rest Body View) View)))
    (before : Event (S b D ViewData Rest Body View)) (parameter : Parameter)
    (views : ViewAssignment b Nat) (packet : Packet b D ViewData Rest Body View) : EventFields b :=
  let raw := Runtime.returnRebind (packet.outcome views parameter)
  let binder := returnBinder parameter
  ⟨packet.history, (base.eta frames before binder raw).original,
    (base.witness frames before binder raw).current,
    base.scope frames before binder raw, base.authority frames before binder raw,
    base.incidence frames before binder raw, base.dictionary frames before binder raw⟩

/-- The pre-bind event is reconstructed from the complete actual Return
snapshot and this same Return's field readout. It is not the receipt event. -/
def beforeBind (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (frames : List (Frame (Payload (S b D ViewData Rest Body View) View)))
    (before : Event (S b D ViewData Rest Body View)) (parameter : Parameter)
    (views : ViewAssignment b Nat) (packet : Packet b D ViewData Rest Body View) :
    Event (S b D ViewData Rest Body View) :=
  let current := fields base frames before parameter views packet
  {before with
    history := packet.history
    current := packet.snapshot
    eta := ⟨current.assignment, views⟩
    witness := ⟨current.witness, before.witness.shared⟩
    scope := current.scope
    authority := current.authority
    incidence := current.incidence
    dictionary := current.dictionary}

theorem computed_return_event (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (frames : List (Frame (Payload (S b D ViewData Rest Body View) View)))
    (before : Event (S b D ViewData Rest Body View)) (parameter : Parameter)
    (views : ViewAssignment b Nat) (descriptor : b.Descriptor)
    (packet : Packet b D ViewData Rest Body View) :
    (valueReadout base parameter views descriptor).event frames before
      (returnBinder parameter) (.returnRebind (packet.outcome views parameter)) =
    bindEvent (beforeBind base frames before parameter views packet)
      packet.parent parameter.formal.name packet.raw packet.node packet.found descriptor
      (fields base frames before parameter views packet) := by
  simp only [RuntimeReadout.event, valueReadout, ite_true, packet_address]
  rfl

theorem return_keeps_scoped_strategy (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (frames : List (Frame (Payload (S b D ViewData Rest Body View) View)))
    (before : Event (S b D ViewData Rest Body View)) (parameter : Parameter)
    (views : ViewAssignment b Nat) (descriptor : b.Descriptor)
    (packet : Packet b D ViewData Rest Body View) :
    ((valueReadout base parameter views descriptor).event frames before
      (returnBinder parameter) (.returnRebind (packet.outcome views parameter))).witness.shared =
      before.witness.shared := by
  rw [computed_return_event]
  rfl

/-- No assumption equates the packet's native state to its earlier source
receipt. All changed Force fields are retained from the packet. -/
theorem return_current_native_fields
    (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (frames : List (Frame (Payload (S b D ViewData Rest Body View) View)))
    (before : Event (S b D ViewData Rest Body View)) (parameter : Parameter)
    (views : ViewAssignment b Nat) (descriptor : b.Descriptor)
    (packet : Packet b D ViewData Rest Body View) :
    let after := (valueReadout base parameter views descriptor).event frames before
      (returnBinder parameter) (.returnRebind (packet.outcome views parameter))
    after.current.residual = packet.snapshot.residual ∧
    after.current.providers = packet.snapshot.providers ∧
    after.current.aliases = packet.snapshot.aliases ∧
    after.current.world.receiving = packet.snapshot.world.receiving ∧
    after.current.world.control = packet.snapshot.world.control ∧
    after.current.world.rest = packet.snapshot.world.rest := by
  dsimp only
  rw [computed_return_event]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def decodedReturn (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View)
    (environment : Environment (Payload (S b D ViewData Rest Body View) View))
    (parameter : Parameter) (views : ViewAssignment b Nat) (descriptor : b.Descriptor)
    (packet : Packet b D ViewData Rest Body View) (occurrence : Nat) :
    Decoded (S b D ViewData Rest Body View) View :=
  returnState (valueReadout base parameter views descriptor) state environment parameter
    (packet.outcome views parameter) occurrence

theorem decoded_return_event (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View)
    (environment : Environment (Payload (S b D ViewData Rest Body View) View))
    (parameter : Parameter) (views : ViewAssignment b Nat) (descriptor : b.Descriptor)
    (packet : Packet b D ViewData Rest Body View) (occurrence : Nat) :
    (decodedReturn base state environment parameter views descriptor packet occurrence).assignment.event =
    bindEvent (beforeBind base state.fixedFrames state.assignment.event parameter views packet)
      packet.parent parameter.formal.name packet.raw packet.node packet.found descriptor
      (fields base state.fixedFrames state.assignment.event parameter views packet) :=
  computed_return_event base state.fixedFrames state.assignment.event parameter views descriptor packet

def evidence (parameter : Parameter)
    (selection : Selected (S b D ViewData Rest Body View) View parameter)
    (mode : parameter.formal.entry = .value) (views : ViewAssignment b Nat)
    (packet : Packet b D ViewData Rest Body View) (witness : b.WitnessValue) :
    Retained (S b D ViewData Rest Body View) parameter.registration :=
  nativeEvidence parameter selection mode (liftViews views) packet.snapshot.world packet.raw
    packet.observation (packet.outcome views parameter).after packet.endpoints
    (packet.outcome views parameter).bindings witness

def delivered (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View)
    (environment : Environment (Payload (S b D ViewData Rest Body View) View))
    (parameter : Parameter) (selection : Selected (S b D ViewData Rest Body View) View parameter)
    (mode : parameter.formal.entry = .value) (views : ViewAssignment b Nat)
    (packet : Packet b D ViewData Rest Body View) (witness : b.WitnessValue)
    (returnOccurrence sharedOccurrence : Nat) : Decoded (S b D ViewData Rest Body View) View :=
  let readout := valueReadout base parameter views (selection.valueDescriptor mode)
  let after := environment.extend (returnBinder parameter)
    (scopeCandidate environment returnOccurrence (.runtime (.returnRebind (packet.outcome views parameter))))
  deliverFrame readout (decodedReturn base state environment parameter views
    (selection.valueDescriptor mode) packet returnOccurrence)
    parameter (evidence parameter selection mode views packet witness) after.eventPath sharedOccurrence

theorem delivered_event (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View)
    (environment : Environment (Payload (S b D ViewData Rest Body View) View))
    (parameter : Parameter) (selection : Selected (S b D ViewData Rest Body View) View parameter)
    (mode : parameter.formal.entry = .value) (views : ViewAssignment b Nat)
    (packet : Packet b D ViewData Rest Body View) (witness : b.WitnessValue)
    (returnOccurrence sharedOccurrence : Nat) :
    (delivered base state environment parameter selection mode views packet witness
      returnOccurrence sharedOccurrence).assignment.event =
    bindEvent (beforeBind base state.fixedFrames state.assignment.event parameter views packet)
      packet.parent parameter.formal.name packet.raw packet.node packet.found
      (selection.valueDescriptor mode)
      (fields base state.fixedFrames state.assignment.event parameter views packet) :=
  decoded_return_event base state environment parameter views (selection.valueDescriptor mode) packet returnOccurrence

private theorem objects_keep_installed (state : Decoded s View)
    (entries : List (Endpoint × Object s)) :
    (entries.foldl Decoded.object state).installed = state.installed := by
  induction entries generalizing state with
  | nil => rfl
  | cons entry rest ih =>
      rw [List.foldl_cons, ih]
      rcases entry with ⟨endpoint, object⟩
      cases object <;> rfl

theorem decoded_return_installed
    (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View)
    (environment : Environment (Payload (S b D ViewData Rest Body View) View))
    (parameter : Parameter) (views : ViewAssignment b Nat) (descriptor : b.Descriptor)
    (packet : Packet b D ViewData Rest Body View) (occurrence : Nat) :
    (decodedReturn base state environment parameter views descriptor packet occurrence).installed =
      state.installed := objects_keep_installed state packet.endpoints

/-- Complete registry equality at the very Event produced by the decoder.
The pre-bind registry invariant and native finite-store representation are
inputs; the new cell and the entire post-bind equality are constructed. -/
theorem delivered_registry_at_own_event
    (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View)
    (environment : Environment (Payload (S b D ViewData Rest Body View) View))
    (parameter : Parameter) (selection : Selected (S b D ViewData Rest Body View) View parameter)
    (mode : parameter.formal.entry = .value) (views : ViewAssignment b Nat)
    (packet : Packet b D ViewData Rest Body View) (witness : b.WitnessValue)
    (returnOccurrence sharedOccurrence : Nat)
    (cells : List (Option (Received Nat))) (vector : packet.snapshot.world.cells = vectorStore cells)
    (represented : state.installed = bindingReadout (liftViews views) packet.snapshot.world.cells) :
    let post := delivered base state environment parameter selection mode views packet witness
      returnOccurrence sharedOccurrence
    post.installed = installed post.assignment.event := by
  dsimp only
  rw [delivered_event]
  apply delivered_native_bind_readout
  · exact vector
  · rw [decoded_return_installed]
    exact represented

/-- Generic world construction now concludes PhiW at the source decoder's
own current Event. This theorem does not assume that the decoded Event equals
an unrelated separately constructed event. -/
theorem delivered_phiW_at_own_event
    (operator : Inputs (S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name)
    (candidate : Family (S b D ViewData Rest Body View))
    (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View)
    (environment : Environment (Payload (S b D ViewData Rest Body View) View))
    (parameter : Parameter) (selection : Selected (S b D ViewData Rest Body View) View parameter)
    (mode : parameter.formal.entry = .value) (views : ViewAssignment b Nat)
    (packet : Packet b D ViewData Rest Body View) (witness : b.WitnessValue)
    (returnOccurrence sharedOccurrence : Nat)
    (old : PhiW (inputs operator references) candidate
      (beforeBind base state.fixedFrames state.assignment.event parameter views packet))
    (cells : List (Option (Received Nat))) (vector : packet.snapshot.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, packet.snapshot.providers provider = some closure →
      closure.savedEnvironment < packet.snapshot.world.environments.size)
    (savedAliases : ∀ reference ∈ packet.snapshot.aliases,
      reference.environment < packet.snapshot.world.environments.size)
    (coherent : operator.eventCoherent (delivered base state environment parameter selection mode views packet witness
      returnOccurrence sharedOccurrence).assignment.event)
    (guards : (operator.worldGuards (delivered base state environment parameter selection mode views packet witness
      returnOccurrence sharedOccurrence).assignment.event).Valid)
    (restrict : ∀ object : Installed (S b D ViewData Rest Body View),
      object.Valid candidate (beforeBind base state.fixedFrames state.assignment.event parameter views packet) →
      object.Valid candidate (delivered base state environment parameter selection mode views packet witness
        returnOccurrence sharedOccurrence).assignment.event)
    (returned : candidate (.value ⟨selection.valueDescriptor mode, views.value packet.raw.value,
      views.root packet.raw.value, (delivered base state environment parameter selection mode views packet witness
        returnOccurrence sharedOccurrence).assignment.event⟩)) :
    PhiW (inputs operator references) candidate
      (delivered base state environment parameter selection mode views packet witness
        returnOccurrence sharedOccurrence).assignment.event := by
  rw [delivered_event] at coherent guards restrict returned ⊢
  exact bind_phiW operator references candidate _ old cells vector savedProviders savedAliases
    packet.parent parameter.formal.name packet.raw packet.node packet.found (selection.valueDescriptor mode)
    (fields base state.fixedFrames state.assignment.event parameter views packet) coherent guards restrict returned

/-- The world and actual returned membership follow from the same complete
carrier and genuine force observation. No post-world or returned membership
is assumed. The traceForm and independent compatibility/guard obligations
remain at their original semantic owners. -/
theorem delivered_meaning_from_actual_force
    (operator : Inputs (S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name)
    (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View)
    (environment : Environment (Payload (S b D ViewData Rest Body View) View))
    (parameter : Parameter) (selection : Selected (S b D ViewData Rest Body View) View parameter)
    (mode : parameter.formal.entry = .value) (views : ViewAssignment b Nat)
    (packet : Packet b D ViewData Rest Body View) (witness : b.WitnessValue)
    (returnOccurrence sharedOccurrence : Nat)
    (carrier : CarrierRow (S b D ViewData Rest Body View))
    (whole : Meaning (inputs operator references) (.carrier carrier))
    (demandEvent : Event (S b D ViewData Rest Body View))
    (demanded : (inputs operator references).demand carrier demandEvent)
    (executed : (inputs operator references).force carrier.input demandEvent
      ⟨packet.observation, beforeBind base state.fixedFrames state.assignment.event parameter views packet⟩)
    (actualReturn : (inputs operator references).traceForm
      ((⟨packet.observation, beforeBind base state.fixedFrames state.assignment.event parameter views packet⟩ :
        RawObservation (S b D ViewData Rest Body View)).atInterface carrier.interface) =
      .pureReturn ⟨selection.valueDescriptor mode, views.value packet.raw.value, views.root packet.raw.value,
        beforeBind base state.fixedFrames state.assignment.event parameter views packet⟩)
    (cells : List (Option (Received Nat))) (vector : packet.snapshot.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, packet.snapshot.providers provider = some closure →
      closure.savedEnvironment < packet.snapshot.world.environments.size)
    (savedAliases : ∀ reference ∈ packet.snapshot.aliases,
      reference.environment < packet.snapshot.world.environments.size)
    (later : operator.compatible
      (beforeBind base state.fixedFrames state.assignment.event parameter views packet)
      (delivered base state environment parameter selection mode views packet witness
        returnOccurrence sharedOccurrence).assignment.event)
    (coherent : operator.eventCoherent (delivered base state environment parameter selection mode views packet witness
      returnOccurrence sharedOccurrence).assignment.event)
    (guards : (operator.worldGuards (delivered base state environment parameter selection mode views packet witness
      returnOccurrence sharedOccurrence).assignment.event).Valid) :
    Meaning (inputs operator references) (.world
      (delivered base state environment parameter selection mode views packet witness
        returnOccurrence sharedOccurrence).assignment.event) := by
  rw [delivered_event] at later coherent guards ⊢
  exact bind_after_force_return_meaning operator references carrier whole demandEvent demanded
    ⟨packet.observation, beforeBind base state.fixedFrames state.assignment.event parameter views packet⟩
    executed cells vector savedProviders savedAliases packet.parent parameter.formal.name packet.raw
    packet.node packet.found (selection.valueDescriptor mode)
    (fields base state.fixedFrames state.assignment.event parameter views packet)
    actualReturn later coherent guards

/-- The recursive variant unfolds the actual hole-relative carrier. It never
turns a completed Meaning result into Background for an arbitrary candidate. -/
theorem delivered_background_from_actual_force
    (operator : Inputs (S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name)
    (holes : ValueRow (S b D ViewData Rest Body View) → Prop)
    (holeFuture : ∀ row later, holes row → operator.compatible row.event later → holes (row.atEvent later))
    (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View)
    (environment : Environment (Payload (S b D ViewData Rest Body View) View))
    (parameter : Parameter) (selection : Selected (S b D ViewData Rest Body View) View parameter)
    (mode : parameter.formal.entry = .value) (views : ViewAssignment b Nat)
    (packet : Packet b D ViewData Rest Body View) (witness : b.WitnessValue)
    (returnOccurrence sharedOccurrence : Nat)
    (carrier : CarrierRow (S b D ViewData Rest Body View))
    (whole : Background (inputs operator references) holes (.carrier carrier))
    (demandEvent : Event (S b D ViewData Rest Body View))
    (demanded : (inputs operator references).demand carrier demandEvent)
    (executed : (inputs operator references).force carrier.input demandEvent
      ⟨packet.observation, beforeBind base state.fixedFrames state.assignment.event parameter views packet⟩)
    (actualReturn : (inputs operator references).traceForm
      ((⟨packet.observation, beforeBind base state.fixedFrames state.assignment.event parameter views packet⟩ :
        RawObservation (S b D ViewData Rest Body View)).atInterface carrier.interface) =
      .pureReturn ⟨selection.valueDescriptor mode, views.value packet.raw.value, views.root packet.raw.value,
        beforeBind base state.fixedFrames state.assignment.event parameter views packet⟩)
    (cells : List (Option (Received Nat))) (vector : packet.snapshot.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, packet.snapshot.providers provider = some closure →
      closure.savedEnvironment < packet.snapshot.world.environments.size)
    (savedAliases : ∀ reference ∈ packet.snapshot.aliases,
      reference.environment < packet.snapshot.world.environments.size)
    (later : operator.compatible
      (beforeBind base state.fixedFrames state.assignment.event parameter views packet)
      (delivered base state environment parameter selection mode views packet witness
        returnOccurrence sharedOccurrence).assignment.event)
    (coherent : operator.eventCoherent (delivered base state environment parameter selection mode views packet witness
      returnOccurrence sharedOccurrence).assignment.event)
    (guards : (operator.worldGuards (delivered base state environment parameter selection mode views packet witness
      returnOccurrence sharedOccurrence).assignment.event).Valid) :
    Background (inputs operator references) holes (.world
      (delivered base state environment parameter selection mode views packet witness
        returnOccurrence sharedOccurrence).assignment.event) := by
  rw [delivered_event] at later coherent guards ⊢
  exact bind_after_force_return_background operator references holes holeFuture carrier whole demandEvent demanded
    ⟨packet.observation, beforeBind base state.fixedFrames state.assignment.event parameter views packet⟩
    executed cells vector savedProviders savedAliases packet.parent parameter.formal.name packet.raw
    packet.node packet.found (selection.valueDescriptor mode)
    (fields base state.fixedFrames state.assignment.event parameter views packet)
    actualReturn later coherent guards

abbrev PairReturn (D ViewData Rest : Type) :=
  OriginalRecursivePair.Returned Nat D Nat ViewData Nat Rest

/-- The missing native fields are read from the same raw returned packet.
The packet's actual world overrides no logical or proof field. -/
structure PairData (b : Sorts) (D ViewData Rest Body View : Type) where
  views : ViewAssignment b Nat
  snapshot : PairReturn D ViewData Rest → Snapshot b D Nat ViewData Nat Rest Body
  history : PairReturn D ViewData Rest → b.History
  observation : PairReturn D ViewData Rest → b.Observation
  endpoints : PairReturn D ViewData Rest → List (Endpoint × Object (S b D ViewData Rest Body View))
  bindings : PairReturn D ViewData Rest → List (Name × Nat)

def PairData.packet (data : PairData b D ViewData Rest Body View)
    (raw : PairReturn D ViewData Rest) (parent : Nat) (node : Node Name D)
    (found : nodeAt raw.world.environments parent = some node) : Packet b D ViewData Rest Body View :=
  ⟨{data.snapshot raw with world := raw.world}, raw.value, parent, node, found,
    data.history raw, data.observation raw, data.endpoints raw, data.bindings raw⟩

/-- Total presentation for the original source consumer. The absent-parent
branch is raw data only; the source application below supplies the actual
saved-parent lookup, rather than asserting success for that branch. -/
def PairData.presentation (data : PairData b D ViewData Rest Body View)
    (parameter : Parameter) (parent : Nat) : ReturnReadout (S b D ViewData Rest Body View) D ViewData Rest where
  assignment := liftViews data.views
  observation := data.observation
  endpoints := data.endpoints
  bindings := data.bindings
  after := fun raw =>
    let snapshot := {data.snapshot raw with world := raw.world}
    match found : nodeAt raw.world.environments parent with
    | none => ⟨data.history raw, snapshot⟩
    | some node =>
      let next := bindValue raw.world parent parameter.formal.name raw.value node found
      ⟨data.history raw, {snapshot with world := next}⟩

theorem pair_outcome (data : PairData b D ViewData Rest Body View)
    (parameter : Parameter) (raw : PairReturn D ViewData Rest)
    (parent : Nat) (node : Node Name D) (found : nodeAt raw.world.environments parent = some node) :
    (data.presentation parameter parent).outcome parameter raw =
      (data.packet raw parent node found).outcome data.views parameter := by
  simp only [PairData.presentation, ReturnReadout.outcome, nativeReturned,
    OriginalSourceEvents.Returned.outcome, PairData.packet, Packet.outcome, liftViews]
  split
  next absent => simp [found] at absent
  next other present =>
    have same : other = node := Option.some.inj (present.symm.trans found)
    subst other
    rfl

theorem pair_evidence (data : PairData b D ViewData Rest Body View)
    (parameter : Parameter) (selection : Selected (S b D ViewData Rest Body View) View parameter)
    (mode : parameter.formal.entry = .value) (raw : PairReturn D ViewData Rest)
    (parent : Nat) (node : Node Name D) (found : nodeAt raw.world.environments parent = some node)
    (witness : b.WitnessValue) :
    (data.presentation parameter parent).evidence parameter selection mode raw witness =
      evidence parameter selection mode data.views (data.packet raw parent node found) witness := by
  simp only [PairData.presentation, ReturnReadout.evidence, evidence,
    PairData.packet, Packet.outcome]
  split
  next absent => simp [found] at absent
  next other present =>
    have same : other = node := Option.some.inj (present.symm.trans found)
    subst other
    rfl

/-- Application to the ACTUAL original Value-entry/Shared continuation.
The same source-selected anchor supplies the witness. The output contains the
checked original body, its actual decoded state, and that state's complete
installed map at its own Event. Genuine raw Return and old registry formation
remain independent operational inputs, not a source-safety atom. -/
theorem actual_entry_return_world
    (operator : Inputs (S b D ViewData Rest Body View))
    (base : RuntimeReadout (S b D ViewData Rest Body View) View)
    (admissions : LocalAdmissions (S b D ViewData Rest Body View) View)
    (original : Kernel (Payload (S b D ViewData Rest Body View) View))
    (execution : PairExecution D ViewData Rest)
    (parameter : Parameter) (selection : Selected (S b D ViewData Rest Body View) View parameter)
    (mode : parameter.formal.entry = .value) (data : PairData b D ViewData Rest Body View)
    (invocation : OriginalSourceEnvironment.Invocation (S b D ViewData Rest Body View) View)
    (environment : Environment (Payload (S b D ViewData Rest Body View) View))
    (openHistory : environment.replay = none)
    (entry : Judgment (OriginalFormalShared.localKernel operator
      (valueReadout base parameter data.views (selection.valueDescriptor mode)) admissions original execution
      (data.presentation parameter execution.capturedEnvironment) parameter selection mode invocation)
      environment (enteredBody parameter))
    (state : Decoded (S b D ViewData Rest Body View) View)
    (decoded : decode (valueReadout base parameter data.views (selection.valueDescriptor mode)) environment = some state)
    (active : state.activeRaw = some invocation)
    (raw : PairReturn D ViewData Rest) (actual : execution.Returns raw)
    (node : Node Name D) (found : nodeAt raw.world.environments execution.capturedEnvironment = some node)
    (cells : List (Option (Received Nat))) (vector : raw.world.cells = vectorStore cells)
    (represented : state.installed = bindingReadout (liftViews data.views) raw.world.cells)
    (occurrence : Nat) :
    let packet := data.packet raw execution.capturedEnvironment node found
    let readout := valueReadout base parameter data.views (selection.valueDescriptor mode)
    let after := environment.extend (returnBinder parameter)
      (scopeCandidate environment occurrence (.runtime (.returnRebind (packet.outcome data.views parameter))))
    ∃ witness sharedOccurrence,
      let post := delivered base state environment parameter selection mode data.views packet witness occurrence sharedOccurrence
      decode readout (after.extend (sharedBinder parameter) (after.anchorValue (sharedBinder parameter))) = some post ∧
      Judgment (OriginalFormalShared.localKernel operator readout admissions original execution
        (data.presentation parameter execution.capturedEnvironment) parameter selection mode invocation)
        (after.extend (sharedBinder parameter) (after.anchorValue (sharedBinder parameter))) (checkedBody parameter) ∧
      post.installed = installed post.assignment.event := by
  dsimp only
  have consumer := entry_actual_return_consumer operator
    (valueReadout base parameter data.views (selection.valueDescriptor mode)) admissions original execution
    (data.presentation parameter execution.capturedEnvironment) parameter selection mode invocation environment openHistory entry
  obtain ⟨witness, sharedOccurrence, deliveredDecode, body, _⟩ :=
    consumer state decoded active raw actual occurrence
  rw [pair_outcome data parameter raw execution.capturedEnvironment node found] at deliveredDecode body
  rw [pair_evidence data parameter selection mode raw execution.capturedEnvironment node found witness] at deliveredDecode
  refine ⟨witness, sharedOccurrence, deliveredDecode, body, ?_⟩
  exact delivered_registry_at_own_event base state environment parameter selection mode data.views
    (data.packet raw execution.capturedEnvironment node found) witness occurrence sharedOccurrence cells vector represented

end YulangClosure.OriginalReturnWorld
