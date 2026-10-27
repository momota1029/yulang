import YulangClosure.OriginalNameForceExtraction

/-!
A same-event Return packet for the dictionary-free lexical Name constructor.
The receipt event is retained separately. Logical Return readback, independent
admission, history, guards and future compatibility remain explicit inputs.
-/
namespace YulangClosure.OriginalNameEntryCorrespondence

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalParameterWorld OriginalParameterSemantics
open OriginalFormalAdmission OriginalFormalShared OriginalSourceClosure
open OriginalSourceChecking OriginalCheckingAdmission OriginalWorldReadout
open NativeClosureEnvironment SourceIdentityWorld OriginalIdentityRealization
open OriginalIdentityCarrier (NameDelay CaptureAt EventReadout)

variable {b : Sorts} {D ViewData Rest Body View : Type}

/-- Raw constructor inputs. None of these fields assumes Force, Return, bind
success, semantic membership, or the safety of the computed observation. -/
structure Constructor
    (native : OriginalNameForceExtraction.Native b D ViewData Rest Body View)
    (input : CarrierInput (OriginalNameForceExtraction.S b D ViewData Rest Body View)) where
  before : Event (OriginalNameForceExtraction.S b D ViewData Rest Body View)
  parent : Nat
  name : Name
  raw : Received Nat
  node : Node Name D
  found : nodeAt before.current.world.environments parent = some node
  descriptor : b.Descriptor
  fields : EventFields (OriginalNameForceExtraction.Base b)
  handle : Nat
  site : Nat
  matching : Matches before.current.world.receiving raw
  viewBound : raw.view < before.current.world.receiving.views.size
  allocation : OriginalIdentityCarrier.Allocation
    ⟨handle, before.current.world.environments.size, name, site⟩
  decoded : native.handle input.carrier = some handle
  allocated : native.executables
    (bindEvent before parent name raw node found descriptor fields) = allocation.after
  mode : OriginalNameForceExtraction.NameMode
  nativeMode : native.nameMode
    (bindEvent before parent name raw node found descriptor fields) handle = some mode
  lexical : mode.lexicalObserve = true
  plain : native.dispatch = OriginalNameForceExtraction.noDictionaries

variable {native : OriginalNameForceExtraction.Native b D ViewData Rest Body View}
variable {input : CarrierInput (OriginalNameForceExtraction.S b D ViewData Rest Body View)}

def Constructor.demand (c : Constructor native input) :=
  bindEvent c.before c.parent c.name c.raw c.node c.found c.descriptor c.fields

def Constructor.delay (c : Constructor native input) : NameDelay :=
  ⟨c.handle, c.before.current.world.environments.size, c.name, c.site⟩

def Constructor.observed (c : Constructor native input) (n : Nat) :=
  OriginalNameForceExtraction.observe native input c.demand c.delay (n + 2)

def Constructor.returned (c : Constructor native input) : Received Nat :=
  c.raw.asValue.atName c.raw.dispatch

theorem force_return (base : Inputs (OriginalNameForceExtraction.S b D ViewData Rest Body View))
    (c : Constructor native input) (interface : b.Interface) (n : Nat) :
    (OriginalNameForceExtraction.inputs base native).force input c.demand (c.observed n) ∧
    (OriginalNameForceExtraction.inputs base native).traceForm ((c.observed n).atInterface interface) =
      .pureReturn ⟨c.descriptor, c.before.eta.views.value c.raw.value,
        c.before.eta.views.root c.raw.value, (c.observed n).event⟩ :=
  OriginalNameForceExtraction.allocated_bound_force base native input interface c.before
    c.parent c.name c.raw c.node c.found c.descriptor c.fields c.handle c.site
    c.matching c.viewBound c.allocation c.decoded c.allocated c.mode c.nativeMode c.lexical c.plain n

theorem receipt (c : Constructor native input) (n : Nat) :
    (c.observed n).event.current.world.receiving.receipts.cell
        c.demand.current.world.receiving.receipts.size =
      some ⟨c.demand.current.world.control.current, c.raw.view, c.site, none⟩ ∧
    (c.observed n).event.current.world.receiving.receipts.size =
      c.demand.current.world.receiving.receipts.size + 1 ∧
    (c.observed n).event.current.world.receiving.views = c.demand.current.world.receiving.views ∧
    (c.observed n).event.current.world.cells = c.demand.current.world.cells := by
  let capture := OriginalNameForceExtraction.capturedByBind c.before c.parent c.name c.raw
    c.node c.found c.descriptor c.fields c.handle c.site c.matching
  exact OriginalNameForceExtraction.return_receipt native c.delay c.demand capture c.raw.dispatch
    (OriginalNameForceExtraction.captured_by_bind_bound c.before c.parent c.name c.raw c.node
      c.found c.descriptor c.fields c.handle c.site c.matching)
    (by rw [c.plain]; rfl) c.viewBound n

/-- Every native operand is taken from the one computed post-Force event.
The callee parent lookup is checked against that event's own environment. -/
def Constructor.packet (c : Constructor native input) (n parent : Nat) (node : Node Name D)
    (found : nodeAt (c.observed n).event.current.world.environments parent = some node)
    (endpoints : List (Endpoint × Object (OriginalNameForceExtraction.S b D ViewData Rest Body View)))
    (bindings : List (Name × Nat)) :
    OriginalReturnWorld.Packet (OriginalNameForceExtraction.Base b) D ViewData Rest Body View :=
  ⟨(c.observed n).event.current, c.returned, parent, node, found,
    (c.observed n).event.history, (c.observed n).observation, endpoints, bindings⟩

def eventFields (event : Event (OriginalNameForceExtraction.S b D ViewData Rest Body View)) :
    EventFields (OriginalNameForceExtraction.Base b) :=
  ⟨event.history, event.eta.original, event.witness.current, event.scope,
    event.authority, event.incidence, event.dictionary⟩

/-- Return's logical readback is independent of the computed runtime snapshot.
In particular EventProof eta/witness adjustments are not silently erased.
The source receipt event below is never equated to the post-Force event. -/
structure ReturnAlignment
    (seed : Use (OriginalNameForceExtraction.Base b) D ViewData Rest Body View source)
    (packet : OriginalReturnWorld.Packet (OriginalNameForceExtraction.Base b) D ViewData Rest Body View)
    (event : Event (OriginalNameForceExtraction.S b D ViewData Rest Body View)) : Prop where
  fiber : seed.state.assignment.event.fiber = event.fiber
  eta0 : seed.state.assignment.event.eta0 = event.eta0
  views : seed.views = event.eta.views
  shared : seed.state.assignment.event.witness.shared = event.witness.shared
  readback : OriginalReturnWorld.fields seed.readout seed.state.fixedFrames seed.state.assignment.event
    source.parameter seed.views packet = eventFields event

def withPacket (seed : Use (OriginalNameForceExtraction.Base b) D ViewData Rest Body View source)
    (packet : OriginalReturnWorld.Packet (OriginalNameForceExtraction.Base b) D ViewData Rest Body View) :
    Use (OriginalNameForceExtraction.Base b) D ViewData Rest Body View source :=
  {seed with packet := packet}

section Join
variable (base : Inputs (OriginalNameForceExtraction.S b D ViewData Rest Body View))
variable (seed : Use (OriginalNameForceExtraction.Base b) D ViewData Rest Body View source)
variable (c : Constructor native (seed.carrier (OriginalNameForceExtraction.inputs base native)).input)
variable (n parent : Nat) (node : Node Name D)
variable (found : nodeAt (c.observed n).event.current.world.environments parent = some node)
variable (endpoints : List (Endpoint × Object (OriginalNameForceExtraction.S b D ViewData Rest Body View)))
variable (bindings : List (Name × Nat))

local notation "packet" => c.packet n parent node found endpoints bindings
local notation "use" => withPacket seed packet
local notation "operator" => OriginalNameForceExtraction.inputs base native

theorem before_is_observed (alignment : ReturnAlignment seed packet (c.observed n).event) :
    (use).before = (c.observed n).event := by
  change OriginalReturnWorld.beforeBind seed.readout seed.state.fixedFrames seed.state.assignment.event
    source.parameter seed.views packet = _
  unfold OriginalReturnWorld.beforeBind
  rw [alignment.readback]
  simp only [Constructor.packet, eventFields, alignment.views, alignment.shared,
    alignment.fiber, alignment.eta0]

/-- The actual readout theorem is applied to the same constructed Packet;
all native fields, including the post-Observe receipt, survive the bind. -/
theorem computed_bind (descriptor : b.Descriptor) :
    (OriginalReturnWorld.valueReadout seed.readout source.parameter seed.views descriptor).event
      seed.state.fixedFrames seed.state.assignment.event (returnBinder source.parameter)
      (.returnRebind ((packet).outcome seed.views source.parameter)) =
    (use).bound descriptor :=
  OriginalReturnWorld.computed_return_event seed.readout seed.state.fixedFrames
    seed.state.assignment.event source.parameter seed.views descriptor packet

/-- Operational EntryFacts fields, with one and the same observation/event.
No Force or Return equation is a hypothesis. -/
theorem executed_return (alignment : ReturnAlignment seed packet (c.observed n).event) :
    (operator).force ((use).carrier operator).input c.demand ⟨(use).packet.observation, (use).before⟩ ∧
    (operator).traceForm
      ((⟨(use).packet.observation, (use).before⟩ : RawObservation (OriginalNameForceExtraction.S b D ViewData Rest Body View)).atInterface
        ((use).carrier operator).interface) =
      .pureReturn ⟨c.descriptor, (use).views.value (use).packet.raw.value,
        (use).views.root (use).packet.raw.value, (use).before⟩ := by
  have same := before_is_observed base seed c n parent node found endpoints bindings alignment
  have computed := force_return base c ((use).carrier operator).interface n
  have rawSame : (⟨(use).packet.observation, (use).before⟩ : RawObservation (OriginalNameForceExtraction.S b D ViewData Rest Body View)) =
      c.observed n := by
    rw [same]
    rfl
  rw [rawSame]
  constructor
  · exact computed.1
  · rw [computed.2, same]
    simp only [withPacket, Constructor.packet, Constructor.returned, Received.asValue, Received.atName]
    rw [alignment.views]
    rfl

/-- The remaining fields are exactly the independent old EntryFacts fields;
matching is derived from the computed receipt rather than assumed again. -/
def entryFacts (references : Body → Nat → Option Name)
    (alignment : ReturnAlignment seed packet (c.observed n).event)
    (demanded : (operator).demand ((use).carrier operator) c.demand)
    (cells : List (Option (Received Nat)))
    (vector : (packet).snapshot.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, (packet).snapshot.providers provider = some closure →
      closure.savedEnvironment < (packet).snapshot.world.environments.size)
    (savedAliases : ∀ reference ∈ (packet).snapshot.aliases,
      reference.environment < (packet).snapshot.world.environments.size)
    (bindLater : (operator).compatible (use).before ((use).bound c.descriptor))
    (bindCoherent : (operator).eventCoherent ((use).bound c.descriptor))
    (bindGuards : ((operator).worldGuards ((use).bound c.descriptor)).Valid)
    (nameLater : (operator).compatible ((use).bound c.descriptor) ((use).named c.descriptor))
    (nameCoherent : (operator).eventCoherent ((use).named c.descriptor))
    (nameGuards : ((operator).worldGuards ((use).named c.descriptor)).Valid) :
    OriginalIdentityCarrier.EntryFacts operator references use c.descriptor := by
  have computed := executed_return base seed c n parent node found endpoints bindings alignment
  refine ⟨c.demand, demanded, computed.1, computed.2, cells, vector,
    savedProviders, savedAliases, bindLater, bindCoherent, bindGuards,
    nameLater, nameCoherent, nameGuards, ?_⟩
  change Matches (c.observed n).event.current.world.receiving c.returned
  unfold Matches
  rw [(receipt c n).2.2.1]
  exact c.matching

/-- Apply the constructed packet to the original Force/entry supplier, then
feed every same-event raw body observation to the existing body consumer.
History and NativeExtraction retain every independent demand and future. -/
theorem name_realization (references : Body → Nat → Option Name)
    (facts : OriginalIdentityCarrier.EntryFacts operator references use c.descriptor)
    (delay : NameDelay)
    (history : OriginalIdentityCarrier.History operator references ((use).carrier operator) delay)
    (nativeExtraction : OriginalIdentityCarrier.NativeExtraction operator references ((use).carrier operator) delay history)
    (consumer : ∀ raw : RawObservation (OriginalNameForceExtraction.S b D ViewData Rest Body View),
      Meaning (inputs operator references) (.trace (raw.atInterface ((use).state.interfaces ⟨source.nameSite, .finalRoot⟩))) →
      Meaning (inputs operator references) (.trace (raw.atInterface ((use).state.interfaces ⟨source.lambdaSite, .bodyConsumer⟩)))) :
    NameRealization operator references use c.descriptor := by
  let cut := facts.toForceCut delay history nativeExtraction
  obtain ⟨world, member, futures⟩ := force_supplies_name operator references use c.descriptor
    cut.whole cut.demandEvent cut.demanded cut.executed cut.actualReturn cut.cells cut.vector
    cut.savedProviders cut.savedAliases cut.bindLater cut.bindCoherent cut.bindGuards
    cut.nameLater cut.nameCoherent cut.nameGuards
  refine ⟨native_name use c.descriptor cut.matching, world, member, futures, ?_⟩
  intro observation
  dsimp only
  intro form guards fields
  apply consumer
  exact name_return_observation (inputs operator references) ((use).named c.descriptor) world
    (packet).snapshot.world.cells.size c.descriptor _ _
    (native_name_installed use c.descriptor cut.cells cut.vector) _ rfl form guards fields

/-- Parent application with the freshly constructed EntryFacts, rather than
an assumed operational packet. The body consumer is the action supplied by
value_entry_consumer_at_receipt_ports/generated_identity_from_name_delay;
its EventProof changes remain independent of the runtime event equality. -/
theorem constructed_name_realization (references : Body → Nat → Option Name)
    (alignment : ReturnAlignment seed packet (c.observed n).event)
    (demanded : (operator).demand ((use).carrier operator) c.demand)
    (cells : List (Option (Received Nat)))
    (vector : (packet).snapshot.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, (packet).snapshot.providers provider = some closure →
      closure.savedEnvironment < (packet).snapshot.world.environments.size)
    (savedAliases : ∀ reference ∈ (packet).snapshot.aliases,
      reference.environment < (packet).snapshot.world.environments.size)
    (bindLater : (operator).compatible (use).before ((use).bound c.descriptor))
    (bindCoherent : (operator).eventCoherent ((use).bound c.descriptor))
    (bindGuards : ((operator).worldGuards ((use).bound c.descriptor)).Valid)
    (nameLater : (operator).compatible ((use).bound c.descriptor) ((use).named c.descriptor))
    (nameCoherent : (operator).eventCoherent ((use).named c.descriptor))
    (nameGuards : ((operator).worldGuards ((use).named c.descriptor)).Valid)
    (delay : NameDelay)
    (history : OriginalIdentityCarrier.History operator references ((use).carrier operator) delay)
    (nativeExtraction : OriginalIdentityCarrier.NativeExtraction operator references ((use).carrier operator) delay history)
    (consumer : ∀ raw : RawObservation (OriginalNameForceExtraction.S b D ViewData Rest Body View),
      Meaning (inputs operator references) (.trace (raw.atInterface ((use).state.interfaces ⟨source.nameSite, .finalRoot⟩))) →
      Meaning (inputs operator references) (.trace (raw.atInterface ((use).state.interfaces ⟨source.lambdaSite, .bodyConsumer⟩)))) :
    NameRealization operator references use c.descriptor :=
  name_realization base seed c n parent node found endpoints bindings references
    (entryFacts base seed c n parent node found endpoints bindings references alignment demanded
      cells vector savedProviders savedAliases bindLater bindCoherent bindGuards nameLater nameCoherent nameGuards)
    delay history nativeExtraction consumer

end Join
end YulangClosure.OriginalNameEntryCorrespondence
