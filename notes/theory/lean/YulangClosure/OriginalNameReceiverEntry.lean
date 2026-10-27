import YulangClosure.OriginalNameForceExtraction

/-! A concrete terminal Name packet and unchanged receiver operands.
The return decoder and Force readout have no shared field constructor in the
frozen inputs. The obstruction theorems expose that boundary; they establish
neither EntryFacts nor the original whole-language judgment. -/
namespace YulangClosure.OriginalNameReceiverEntry

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalParameterSemantics OriginalParameterWorld OriginalWorldReadout
open NativeClosureEnvironment SourceIdentityWorld
open OriginalIdentityCarrier (NameDelay CaptureAt)
open OriginalIdentityRealization (Identity Use)
open OriginalNameForceExtraction

variable {b : Sorts} {D ViewData Rest Body View : Type}

/-- All post-Force native fields come from this very observation. The raw
record is the Name-dispatched capture; terminal_force below checks that fact.
Parent lookup and endpoint/binding metadata remain raw independent readbacks. -/
def terminalPacket
    (native : Native b D ViewData Rest Body View)
    (input : CarrierInput (S b D ViewData Rest Body View))
    (demand : Event (S b D ViewData Rest Body View)) (delay : NameDelay)
    (capture : CaptureAt delay demand) (chosen : Option Nat) (n parent : Nat)
    (node : Node Name D)
    (found : nodeAt (eventAt native delay demand (n + 2)).current.world.environments parent = some node)
    (endpoints : List (Endpoint × Object (S b D ViewData Rest Body View)))
    (bindings : List (Name × Nat)) :
    OriginalReturnWorld.Packet (Base b) D ViewData Rest Body View :=
  let observation := observe native input demand delay (n + 2)
  ⟨observation.event.current, capture.raw.atName chosen, parent, node, found,
    observation.event.history, observation.observation, endpoints, bindings⟩

/-- The original CallInput and active-call incidence are copied without
projecting away provider/context/receipt/continuation/path/consumer fields. -/
def terminalUse (source : Identity)
    (native : Native b D ViewData Rest Body View)
    (readout : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View)
    (environment : Environment (Payload (S b D ViewData Rest Body View) View))
    (call : CallInput (S b D ViewData Rest Body View)) (active : state.active = some call)
    (demand : Event (S b D ViewData Rest Body View)) (delay : NameDelay)
    (capture : CaptureAt delay demand) (chosen : Option Nat) (n parent : Nat)
    (node : Node Name D)
    (found : nodeAt (eventAt native delay demand (n + 2)).current.world.environments parent = some node)
    (endpoints : List (Endpoint × Object (S b D ViewData Rest Body View)))
    (bindings : List (Name × Nat)) (nameFields : EventFields (Base b))
    (bodyDispatch : Option Nat) : Use (Base b) D ViewData Rest Body View source :=
  ⟨readout, demand.eta.views, state, environment, call, active,
    terminalPacket native ⟨call.carrier, call.carrierRoot, call.event⟩ demand delay capture chosen
      n parent node found endpoints bindings, nameFields, bodyDispatch⟩

/-- The successful native constructor emits Force and Return at its actual
post-Name event. It does not assert that a decoder independently reconstructs
that event. Every finite terminal budget is retained. -/
theorem terminal_force
    (base : Inputs (S b D ViewData Rest Body View))
    (native : Native b D ViewData Rest Body View)
    (input : CarrierInput (S b D ViewData Rest Body View)) (interface : b.Interface)
    (demand : Event (S b D ViewData Rest Body View)) (delay : NameDelay)
    (capture : CaptureAt delay demand) (chosen : Option Nat) (n : Nat)
    (registered : owner native input demand = some delay)
    (bound : capture.address < demand.current.world.cells.size)
    (dispatched : native.dispatch delay demand.current.world capture.address capture.raw = .ok chosen)
    (viewBound : capture.raw.view < demand.current.world.receiving.views.size) :
    let observation := observe native input demand delay (n + 2)
    (OriginalNameForceExtraction.inputs base native).force input demand observation ∧
    (OriginalNameForceExtraction.inputs base native).traceForm (observation.atInterface interface) =
      .pureReturn ⟨capture.descriptor, demand.eta.views.value (capture.raw.atName chosen).value,
        demand.eta.views.root (capture.raw.atName chosen).value, observation.event⟩ := by
  dsimp only
  refine ⟨every_owned_prefix base native input demand delay (n + 2) registered, ?_⟩
  have form := prefix_form base native input interface delay demand capture chosen bound dispatched viewBound (n + 2)
  simpa only [run, initialized_evaluate native.dispatch delay demand.current.world capture.address
    capture.raw chosen capture.lookup bound capture.stored dispatched viewBound capture.matching,
    finish, Phase.result, OriginalIdentityCarrier.resultForm, Received.atName, OriginalNameForceExtraction.observe] using form

/-- The complete snapshot, including providers and receiving receipts, is
copied from the designated observation, together with its exact raw tag. -/
theorem packet_fields
    (native : Native b D ViewData Rest Body View)
    (input : CarrierInput (S b D ViewData Rest Body View))
    (demand : Event (S b D ViewData Rest Body View)) (delay : NameDelay)
    (capture : CaptureAt delay demand) (chosen : Option Nat) (n parent : Nat)
    (node : Node Name D)
    (found : nodeAt (eventAt native delay demand (n + 2)).current.world.environments parent = some node)
    (endpoints : List (Endpoint × Object (S b D ViewData Rest Body View)))
    (bindings : List (Name × Nat)) :
    let packet := terminalPacket native input demand delay capture chosen n parent node found endpoints bindings
    let observation := observe native input demand delay (n + 2)
    packet.snapshot = observation.event.current ∧ packet.history = observation.event.history ∧
    packet.observation = observation.observation ∧ packet.raw = capture.raw.atName chosen ∧
    packet.endpoints = endpoints ∧ packet.bindings = bindings := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Constructor projection equations expose the exact independent owners.
In particular active-call incidence supplies none of these readback laws. -/
theorem decoder_field_owners
    (readout : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View) (source : Identity)
    (views : ViewAssignment (Base b) Nat)
    (packet : OriginalReturnWorld.Packet (Base b) D ViewData Rest Body View) :
    let before := state.assignment.event
    let reconstructed := OriginalReturnWorld.beforeBind readout state.fixedFrames before source.parameter views packet
    let raw := Runtime.returnRebind (packet.outcome views source.parameter)
    reconstructed.fiber = before.fiber ∧ reconstructed.eta0 = before.eta0 ∧
    reconstructed.eta.original = (readout.eta state.fixedFrames before (OriginalFormalShared.returnBinder source.parameter) raw).original ∧
    reconstructed.eta.views = views ∧
    reconstructed.witness.shared = before.witness.shared ∧
    reconstructed.witness.current = (readout.witness state.fixedFrames before (OriginalFormalShared.returnBinder source.parameter) raw).current ∧
    reconstructed.scope = readout.scope state.fixedFrames before (OriginalFormalShared.returnBinder source.parameter) raw ∧
    reconstructed.authority = readout.authority state.fixedFrames before (OriginalFormalShared.returnBinder source.parameter) raw ∧
    reconstructed.incidence = readout.incidence state.fixedFrames before (OriginalFormalShared.returnBinder source.parameter) raw ∧
    reconstructed.dictionary = readout.dictionary state.fixedFrames before (OriginalFormalShared.returnBinder source.parameter) raw :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A disagreeing independent scope readback suffices to prevent the desired
join, even when every native snapshot field is retained in the packet.
This is an interface obstruction, not a source-qualified counterexample. -/
theorem scope_readback_obstructs_join
    (readout : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View) (source : Identity)
    (views : ViewAssignment (Base b) Nat)
    (packet : OriginalReturnWorld.Packet (Base b) D ViewData Rest Body View)
    (observation : RawObservation (S b D ViewData Rest Body View))
    (different : readout.scope state.fixedFrames state.assignment.event
      (OriginalFormalShared.returnBinder source.parameter) (.returnRebind (packet.outcome views source.parameter)) ≠
      observation.event.scope) :
    OriginalReturnWorld.beforeBind readout state.fixedFrames state.assignment.event
      source.parameter views packet ≠ observation.event := by
  intro equal
  exact different (congrArg Event.scope equal)

/-- Even when the Force demand is chosen to be the decoder's own pre-event,
only the static fiber, eta0, views and scoped shared witness agree by their
constructors. The dynamic original assignment readback remains separate. -/
theorem same_demand_static
    (readout : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View) (source : Identity)
    (native : Native b D ViewData Rest Body View) (delay : NameDelay) (n : Nat)
    (packet : OriginalReturnWorld.Packet (Base b) D ViewData Rest Body View) :
    let demand := state.assignment.event
    let before := OriginalReturnWorld.beforeBind readout state.fixedFrames demand source.parameter demand.eta.views packet
    let terminal := eventAt native delay demand (n + 2)
    before.fiber = terminal.fiber ∧ before.eta0 = terminal.eta0 ∧
    before.eta.views = terminal.eta.views ∧ before.witness.shared = terminal.witness.shared := by
  simp [OriginalReturnWorld.beforeBind, eventAt]

/-- Exact first dynamic field owner at the terminal Force event. There is no
constructor equation connecting this assignment to RuntimeReadout.eta. -/
theorem terminal_assignment_owner
    (native : Native b D ViewData Rest Body View) (delay : NameDelay)
    (demand : Event (S b D ViewData Rest Body View)) (n : Nat) :
    (eventAt native delay demand (n + 2)).eta.original =
      ((native.fields delay demand).fields (n + 2)).assignment := by
  simp [eventAt]

/-- The first dynamic mismatch blocks the event join at the SAME demand.
The mismatch is an explicit falsifier for a proposed readback law, not a
hypothesis with which this module labels the entry obligation proved. -/
theorem assignment_readback_obstructs_join
    (readout : RuntimeReadout (S b D ViewData Rest Body View) View)
    (state : Decoded (S b D ViewData Rest Body View) View) (source : Identity)
    (native : Native b D ViewData Rest Body View) (delay : NameDelay) (n : Nat)
    (packet : OriginalReturnWorld.Packet (Base b) D ViewData Rest Body View)
    (different : (readout.eta state.fixedFrames state.assignment.event
      (OriginalFormalShared.returnBinder source.parameter)
      (.returnRebind (packet.outcome state.assignment.event.eta.views source.parameter))).original ≠
      ((native.fields delay state.assignment.event).fields (n + 2)).assignment) :
    OriginalReturnWorld.beforeBind readout state.fixedFrames state.assignment.event source.parameter
      state.assignment.event.eta.views packet ≠ eventAt native delay state.assignment.event (n + 2) := by
  intro equal
  apply different
  have projected := congrArg (fun event => event.eta.original) equal
  exact projected.trans (terminal_assignment_owner native delay state.assignment.event n)

end YulangClosure.OriginalNameReceiverEntry
