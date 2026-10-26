import YulangClosure.OriginalSourceClosure
import YulangClosure.OriginalReturnWorld

/-!
The actual Value-entry identity Name, at the source-selected formal contract.
This supplies the post-Force native Name/world/member join and its body-consumer
application. It does not introduce the identity closure's full Function member,
interpret opaque carrierAccepted, or establish original principality.
-/
namespace YulangClosure.OriginalIdentityRealization

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalParameterWorld OriginalParameterSemantics
open OriginalFormalAdmission OriginalFormalShared OriginalSourceClosure
open OriginalSourceChecking OriginalCheckingAdmission OriginalWorldReadout
open NativeClosureEnvironment SourceIdentityWorld

variable {b s : Sorts} {D ViewData Rest Body View : Type}

/-- Resolved original identity syntax, with arbitrary surrounding scope and
original occurrence identifiers. No global Site freshness is presumed. -/
structure Identity where
  declaration : Declaration
  ambient : List ScopeEntry
  context : Context
  lambdaSite : Site
  formalSite : Site
  patternSite : Site
  nameSite : Site
  name : Name

def Identity.parameter (source : Identity) : Parameter :=
  ⟨source.declaration, source.ambient, source.context, source.lambdaSite,
    ⟨source.formalSite, source.name, none, false⟩,
    .wild source.patternSite, .name ⟨source.nameSite, none⟩ source.name⟩

def Identity.introduction (source : Identity) (route : Route)
    (telescope : Telescope s View source.ambient) : Introduction s View :=
  ⟨source.parameter, route, telescope⟩

theorem identity_value_entry (source : Identity) : source.parameter.formal.entry = .value := rfl

theorem identity_body_resolves_formal (source : Identity) :
    lookupBinding (OriginalFormalShared.bodyContext source.parameter) source.name =
      some {name := source.name, owner := source.formalSite, kind := .formal,
            entry := some .value, singleUse := true} := by
  simp [Identity.parameter, OriginalFormalShared.bodyContext, OriginalFormalShared.formalContext,
    Source.bindingRecords, Source.nameCount, lookupBinding, Formal.entry]

/-- The Name observer's actual receipt update. All independent current
history/evidence fields are supplied at this event; the raw world is computed.
The value interpretation and original Shared strategy are retained. -/
def nameEvent (before : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (view site : Nat) (fields : EventFields b) :
    Event (OriginalReturnWorld.S b D ViewData Rest Body View) :=
  {before with
    history := fields.history
    current := {before.current with world := {before.current.world with
      receiving := before.current.world.receiving.record before.current.world.control.current view site none}}
    eta := {before.eta with original := fields.assignment}
    witness := {before.witness with current := fields.witness}
    scope := fields.scope, authority := fields.authority,
    incidence := fields.incidence, dictionary := fields.dictionary}

theorem name_event_installed (before : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (view site : Nat) (fields : EventFields b) :
    installed (nameEvent before view site fields) = installed before := rfl

theorem name_event_receipt (before : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (view site : Nat) (fields : EventFields b) :
    (nameEvent before view site fields).current.world.receiving.receipts.cell
      before.current.world.receiving.receipts.size =
        some ⟨before.current.world.control.current, view, site, none⟩ ∧
    (nameEvent before view site fields).current.world.receiving.receipts.size =
      before.current.world.receiving.receipts.size + 1 ∧
    (nameEvent before view site fields).current.world.receiving.views = before.current.world.receiving.views :=
  ⟨receipt_new _ _ _ _ _, rfl, rfl⟩

/-- Full world membership across the genuine Name receipt update. The old
world's installed certificates restrict along the independent compatibility
relation; no receipt-reflecting stutter or final-world premise is used. -/
theorem name_event_world
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name)
    (before : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (view site : Nat) (fields : EventFields b)
    (world : Meaning (inputs operator references) (.world before))
    (later : operator.compatible before (nameEvent before view site fields))
    (coherent : operator.eventCoherent (nameEvent before view site fields))
    (guards : (operator.worldGuards (nameEvent before view site fields)).Valid) :
    Meaning (inputs operator references) (.world (nameEvent before view site fields)) := by
  have old := (world_unfold (inputs operator references) before).mp world
  apply (world_unfold (inputs operator references) _).mpr
  refine ⟨coherent, guards, old.2.2.1, old.2.2.2.1, old.2.2.2.2.1, ?_⟩
  intro address object found
  exact installed_restrict (inputs operator references) object before _ later
    (old.2.2.2.2.2 address object found)

/-- Data at the actual receipt/Force cut. active is incidence with the
decoder's entire CallInput, not admission, typing, or a body certificate. -/
structure Use (b : Sorts) (D ViewData Rest Body View : Type) (source : Identity) where
  readout : RuntimeReadout (OriginalReturnWorld.S b D ViewData Rest Body View) View
  views : ViewAssignment b Nat
  state : Decoded (OriginalReturnWorld.S b D ViewData Rest Body View) View
  environment : Environment (Payload (OriginalReturnWorld.S b D ViewData Rest Body View) View)
  call : CallInput (OriginalReturnWorld.S b D ViewData Rest Body View)
  active : state.active = some call
  packet : OriginalReturnWorld.Packet b D ViewData Rest Body View
  nameFields : EventFields b
  dispatch : Option Nat

def Use.before (use : Use b D ViewData Rest Body View source) :
    Event (OriginalReturnWorld.S b D ViewData Rest Body View) :=
  OriginalReturnWorld.beforeBind use.readout use.state.fixedFrames use.state.assignment.event
    source.parameter use.views use.packet

def Use.fields (use : Use b D ViewData Rest Body View source) : EventFields b :=
  OriginalReturnWorld.fields use.readout use.state.fixedFrames use.state.assignment.event
    source.parameter use.views use.packet

def Use.bound (use : Use b D ViewData Rest Body View source) (descriptor : b.Descriptor) :
    Event (OriginalReturnWorld.S b D ViewData Rest Body View) :=
  bindEvent use.before use.packet.parent source.name use.packet.raw use.packet.node use.packet.found
    descriptor use.fields

def Use.named (use : Use b D ViewData Rest Body View source) (descriptor : b.Descriptor) :
    Event (OriginalReturnWorld.S b D ViewData Rest Body View) :=
  nameEvent (use.bound descriptor) use.packet.raw.view source.nameSite use.nameFields

def Use.carrier (use : Use b D ViewData Rest Body View source)
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View)) :
    CarrierRow (OriginalReturnWorld.S b D ViewData Rest Body View) :=
  ⟨operator.checkedInlet (use.state.assignment.descriptor ⟨source.lambdaSite, .descriptor⟩),
    use.call.carrier, use.call.carrierRoot, use.call.event⟩

def Use.returnedRow (use : Use b D ViewData Rest Body View source) (descriptor : b.Descriptor) :
    ValueRow (OriginalReturnWorld.S b D ViewData Rest Body View) :=
  ⟨descriptor, use.views.value use.packet.raw.value, use.views.root use.packet.raw.value,
    use.named descriptor⟩

theorem carrier_keeps_actual_call (use : Use b D ViewData Rest Body View source)
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View)) :
    (use.carrier operator).carrier = use.call.carrier ∧
    (use.carrier operator).root = use.call.carrierRoot ∧
    (use.carrier operator).event = use.call.event ∧ use.state.active = some use.call :=
  ⟨rfl, rfl, rfl, use.active⟩

/-- Actual native lookup/receipt, with the source Name and captured parent.
The result keeps raw value/view; dispatch is the real Name result. -/
theorem native_name (use : Use b D ViewData Rest Body View source) (descriptor : b.Descriptor)
    (matching : Matches use.packet.snapshot.world.receiving use.packet.raw) :
    observeName (use.bound descriptor).current.world
      use.packet.snapshot.world.environments.size source.name source.nameSite use.dispatch =
      some ((use.named descriptor).current.world, use.packet.raw.asValue.atName use.dispatch) := by
  exact name_success (bind_read use.packet.snapshot.world use.packet.parent source.name
    use.packet.raw use.packet.node use.packet.found) matching

theorem native_name_installed (use : Use b D ViewData Rest Body View source) (descriptor : b.Descriptor)
    (cells : List (Option (Received Nat))) (vector : use.packet.snapshot.world.cells = vectorStore cells) :
    installed (use.named descriptor) use.packet.snapshot.world.cells.size =
      some (.value descriptor (use.views.value use.packet.raw.value) (use.views.root use.packet.raw.value)) := by
  rw [Use.named, name_event_installed]
  have current := bind_installed use.before cells vector use.packet.parent source.name use.packet.raw
    use.packet.node use.packet.found descriptor use.fields
  rw [Use.bound, current]
  exact OriginalRecursivePair.extend_bindings_new _ _ _

/-- Genuine Force supplies both recursive premises of bind; the native Name
then supplies the same selected member and every compatible future member.
No world or returned-value membership is assumed separately. -/
theorem force_supplies_name
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name) (use : Use b D ViewData Rest Body View source)
    (descriptor : b.Descriptor)
    (whole : Meaning (inputs operator references) (.carrier (use.carrier operator)))
    (demandEvent : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (demanded : operator.demand (use.carrier operator) demandEvent)
    (executed : operator.force (use.carrier operator).input demandEvent ⟨use.packet.observation, use.before⟩)
    (actualReturn : operator.traceForm
      ((⟨use.packet.observation, use.before⟩ : RawObservation (OriginalReturnWorld.S b D ViewData Rest Body View)).atInterface
        (use.carrier operator).interface) =
      .pureReturn ⟨descriptor, use.views.value use.packet.raw.value, use.views.root use.packet.raw.value, use.before⟩)
    (cells : List (Option (Received Nat))) (vector : use.packet.snapshot.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, use.packet.snapshot.providers provider = some closure →
      closure.savedEnvironment < use.packet.snapshot.world.environments.size)
    (savedAliases : ∀ reference ∈ use.packet.snapshot.aliases,
      reference.environment < use.packet.snapshot.world.environments.size)
    (bindLater : operator.compatible use.before (use.bound descriptor))
    (bindCoherent : operator.eventCoherent (use.bound descriptor))
    (bindGuards : (operator.worldGuards (use.bound descriptor)).Valid)
    (nameLater : operator.compatible (use.bound descriptor) (use.named descriptor))
    (nameCoherent : operator.eventCoherent (use.named descriptor))
    (nameGuards : (operator.worldGuards (use.named descriptor)).Valid) :
    Meaning (inputs operator references) (.world (use.named descriptor)) ∧
    Meaning (inputs operator references) (.value (use.returnedRow descriptor)) ∧
    ∀ later, operator.compatible (use.named descriptor) later →
      Meaning (inputs operator references) (.value ((use.returnedRow descriptor).atEvent later)) := by
  have bound := OriginalForcedParameter.bind_after_force_return_meaning operator references
    (use.carrier operator) whole demandEvent demanded ⟨use.packet.observation, use.before⟩ executed
    cells vector savedProviders savedAliases use.packet.parent source.name use.packet.raw use.packet.node
    use.packet.found descriptor use.fields actualReturn bindLater bindCoherent bindGuards
  have named := name_event_world operator references (use.bound descriptor) use.packet.raw.view
    source.nameSite use.nameFields bound nameLater nameCoherent nameGuards
  have member := immutable_name_value (inputs operator references) (use.named descriptor) named
    use.packet.snapshot.world.cells.size descriptor _ _ (native_name_installed use descriptor cells vector)
  exact ⟨named, member, fun later lawful => value_restrict (inputs operator references) _ member later lawful⟩

/-- The retained source body has the Return's actual runtime event and the
receipt state's unchanged interface ports. Its EventProof may change logical
evidence; the Checking action quantifies over every raw observation, including
the genuine later Name event. No proof/runtime event equality is asserted. -/
theorem value_entry_consumer_at_receipt_ports (intro : Introduction s View)
    (assignment : FormalAssignment s View) (operator : Inputs s)
    (registry : GuardRegistry operator) (declarations : Declarations operator registry)
    (readout : RuntimeReadout s View) (base : LocalAdmissions s View)
    (ports : PortReadout s View) (original : Kernel (Payload s View))
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (mode : intro.parameter.formal.entry = .value) (openHistory : environment.replay = none)
    (entry : Judgment (closureKernel intro assignment operator registry declarations readout base ports original)
      environment (enteredBody intro.parameter))
    (returned : ScopedValue (Payload s View)) (outcome : Outcome s)
    (payload : returned.data = .runtime (.returnRebind outcome))
    (admitted : Admitted operator readout (closureAdmissions intro assignment base)
      environment (returnBinder intro.parameter) returned) :
    ∃ bodyState : Decoded s View,
      decode readout (retainedEnvironment (environment.extend (returnBinder intro.parameter) returned)
        intro.parameter) = some bodyState ∧
      bodyState.assignment.event = readout.event state.fixedFrames state.assignment.event
        (returnBinder intro.parameter) (.returnRebind outcome) ∧
      bodyState.interfaces = state.interfaces ∧
      formalContract bodyState intro.parameter = formalContract state intro.parameter ∧
      ∀ raw : RawObservation s,
        Meaning operator (.trace (raw.atInterface (state.interfaces ⟨intro.parameter.body.site, .finalRoot⟩))) →
        Meaning operator (.trace (raw.atInterface (state.interfaces ⟨intro.parameter.lambdaSite, .bodyConsumer⟩))) := by
  let kernel := closureKernel intro assignment operator registry declarations readout base ports original
  obtain ⟨shared, body⟩ := value_entry_shared kernel environment intro.parameter mode openHistory
    entry returned admitted
  let after := environment.extend (returnBinder intro.parameter) returned
  let afterState := (state.runtime readout (returnBinder intro.parameter) (.returnRebind outcome)).retain
    ⟨returnBinder intro.parameter, returned, environment.eventPath⟩
  have afterDecoded : decode readout after = some afterState := by
    simpa only [decodeFrame, payload] using
      decode_extend readout environment (returnBinder intro.parameter) returned state decoded
  obtain ⟨beforeShared, data, sharedDecoded, sharedPayload, _, _⟩ :=
    admitted_shared_payload operator readout (closureAdmissions intro assignment base) after intro.parameter shared
  have same : beforeShared = afterState := Option.some.inj (sharedDecoded.symm.trans afterDecoded)
  subst beforeShared
  let bodyState := (afterState.shared data).retain
    ⟨sharedBinder intro.parameter, after.anchorValue (sharedBinder intro.parameter), after.eventPath⟩
  have bodyDecoded : decode readout (retainedEnvironment after intro.parameter) = some bodyState := by
    simpa only [retainedEnvironment, bodyState, decodeFrame, sharedPayload] using
      decode_extend readout after (sharedBinder intro.parameter)
        (after.anchorValue (sharedBinder intro.parameter)) afterState afterDecoded
  have samePorts : bodyState.interfaces = state.interfaces :=
    objects_preserve_interfaces state outcome.endpoints
  have sameContract : formalContract bodyState intro.parameter = formalContract state intro.parameter :=
    runtime_preserves_contract readout state (returnBinder intro.parameter) (.returnRebind outcome) intro.parameter
  obtain ⟨_, _, _, _, _, _, _, _, action⟩ :=
    checked_body_consumer intro assignment operator registry declarations readout base ports original
      _ bodyState bodyDecoded (scopedBodyRoute intro) (scopedBodyScope intro) body
  exact ⟨bodyState, bodyDecoded, rfl, samePorts, sameContract,
    fun raw member => by simpa only [samePorts] using action raw (by simpa only [samePorts] using member)⟩

/-- Recover the entire active CallInput from the admitted raw invocation and
its actual receipt. The input is constructed, not chosen by a result witness.
The complete original checked domain is retained in the conclusion. -/
theorem receipt_recovers_call (operator : Inputs s) (readout : RuntimeReadout s View)
    (admissions : LocalAdmissions s View) (environment : Environment (Payload s View))
    (parameter : Parameter) (invocation receipt : ScopedValue (Payload s View))
    (invocationAdmitted : Admitted operator readout admissions environment (invocationBinder parameter) invocation)
    (receiptAdmitted : Admitted operator readout admissions
      (environment.extend (invocationBinder parameter) invocation) (receiptBinder parameter) receipt)
    (state : Decoded s View)
    (decoded : decode readout ((environment.extend (invocationBinder parameter) invocation).extend
      (receiptBinder parameter) receipt) = some state) :
    ∃ (before : Decoded s View) (raw : Invocation s View),
      decode readout environment = some before ∧
      invocation.data = .runtime (.invocation raw) ∧
      CheckedDomain operator (raw.challenge
        (readout.event before.fixedFrames before.assignment.event (invocationBinder parameter) (.invocation raw))
        (before.callRow (invocationBinder parameter)).descriptor before.viewMeaning) ∧
      state.active = some ((raw.challenge
        (readout.event before.fixedFrames before.assignment.event (invocationBinder parameter) (.invocation raw))
        (before.callRow (invocationBinder parameter)).descriptor before.viewMeaning).input) ∧
      state.assignment.descriptor = before.assignment.descriptor := by
  obtain ⟨parents, before, beforeDecoded, invocationValid⟩ := invocationAdmitted
  obtain ⟨raw, invocationPayload, _, _, checked⟩ := admission_recovers_challenge
    operator readout admissions environment (invocationBinder parameter) before beforeDecoded
    invocation ⟨parents, before, beforeDecoded, invocationValid⟩ rfl
  have invocationDecoded := decode_extend readout environment (invocationBinder parameter)
    invocation before beforeDecoded
  obtain ⟨_, atReceipt, atReceiptDecoded, receiptValid⟩ := receiptAdmitted
  have atReceiptEq := Option.some.inj (atReceiptDecoded.symm.trans invocationDecoded)
  subst atReceipt
  obtain ⟨runtime, receiptPayload⟩ := event_admission_is_runtime operator readout admissions _
    (receiptBinder parameter) rfl receipt.data receiptValid
  cases runtime <;> simp only [receiptPayload, DataAdmitted, receiptBinder,
    reduceCtorEq, false_and] at receiptValid
  rename_i receiptData
  have receiptDecoded := decode_extend readout (environment.extend (invocationBinder parameter) invocation)
    (receiptBinder parameter) receipt _ invocationDecoded
  have stateEq := Option.some.inj (decoded.symm.trans receiptDecoded)
  subst state
  refine ⟨before, raw, beforeDecoded, invocationPayload, checked, ?_, ?_⟩ <;>
    simp only [decodeFrame, receiptPayload, invocationPayload, Decoded.retain, Decoded.runtime] <;> rfl

/-- Independent hypotheses at one genuine Force cut. This is transparent
bookkeeping of primitive premises, not a new Call admission or a supplier of
world/value/body membership. In particular whole remains an open source
carrier obligation and is not replaced by carrierAccepted. -/
structure ForceCut
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name) (use : Use b D ViewData Rest Body View source)
    (descriptor : b.Descriptor) where
  whole : Meaning (inputs operator references) (.carrier (use.carrier operator))
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

/-- Output of the construction. All raw Return observations of the source
Name, with their original independent guards/positive fields, reach the actual
Lambda body consumer. The earlier supplier also retains every lawful future
of the same value, root and descriptor. -/
def NameRealization
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name) (use : Use b D ViewData Rest Body View source)
    (descriptor : b.Descriptor) : Prop :=
  observeName (use.bound descriptor).current.world use.packet.snapshot.world.environments.size
    source.name source.nameSite use.dispatch =
      some ((use.named descriptor).current.world, use.packet.raw.asValue.atName use.dispatch) ∧
  Meaning (inputs operator references) (.world (use.named descriptor)) ∧
  Meaning (inputs operator references) (.value (use.returnedRow descriptor)) ∧
  (∀ later, operator.compatible (use.named descriptor) later →
    Meaning (inputs operator references) (.value ((use.returnedRow descriptor).atEvent later))) ∧
  ∀ observation : b.Observation,
    let raw : RawObservation (OriginalReturnWorld.S b D ViewData Rest Body View) := ⟨observation, use.named descriptor⟩
    let trace := raw.atInterface (use.state.interfaces ⟨source.nameSite, .finalRoot⟩)
    operator.traceForm trace = .pureReturn (use.returnedRow descriptor) →
    (operator.observationGuards trace).Valid →
    (operator.observationFields trace).Holds (Meaning (inputs operator references)) →
    Meaning (inputs operator references)
      (.trace (raw.atInterface (use.state.interfaces ⟨source.lambdaSite, .bodyConsumer⟩)))

private theorem name_realization_of_consumer
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name) (use : Use b D ViewData Rest Body View source)
    (descriptor : b.Descriptor) (cut : ForceCut operator references use descriptor)
    (consumer : ∀ raw : RawObservation (OriginalReturnWorld.S b D ViewData Rest Body View),
      Meaning (inputs operator references) (.trace (raw.atInterface (use.state.interfaces ⟨source.nameSite, .finalRoot⟩))) →
      Meaning (inputs operator references) (.trace (raw.atInterface (use.state.interfaces ⟨source.lambdaSite, .bodyConsumer⟩)))) :
    NameRealization operator references use descriptor := by
  obtain ⟨world, member, futures⟩ := force_supplies_name operator references use descriptor
    cut.whole cut.demandEvent cut.demanded cut.executed cut.actualReturn cut.cells cut.vector
    cut.savedProviders cut.savedAliases cut.bindLater cut.bindCoherent cut.bindGuards
    cut.nameLater cut.nameCoherent cut.nameGuards
  refine ⟨native_name use descriptor cut.matching, world, member, futures, ?_⟩
  intro observation
  dsimp only
  intro form guards fields
  apply consumer
  exact name_return_observation (inputs operator references) (use.named descriptor) world
    use.packet.snapshot.world.cells.size descriptor _ _ (native_name_installed use descriptor cut.cells cut.vector)
    _ rfl form guards fields

/-- Raw provenance of the active input. It is constructed from actual
invocation/receipt admissions; none of its fields assert Call safety. -/
structure CallAtReceipt (operator : Inputs s) (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (parameter : Parameter)
    (invocation : ScopedValue (Payload s View)) (state : Decoded s View) where
  before : Decoded s View
  raw : Invocation s View
  decoded : decode readout environment = some before
  payload : invocation.data = .runtime (.invocation raw)
  checked : CheckedDomain operator (raw.challenge
    (readout.event before.fixedFrames before.assignment.event (invocationBinder parameter) (.invocation raw))
    (before.callRow (invocationBinder parameter)).descriptor before.viewMeaning)
  active : state.active = some ((raw.challenge
    (readout.event before.fixedFrames before.assignment.event (invocationBinder parameter) (.invocation raw))
    (before.callRow (invocationBinder parameter)).descriptor before.viewMeaning).input)
  descriptors : state.assignment.descriptor = before.assignment.descriptor

def CallAtReceipt.input {operator : Inputs s} {readout : RuntimeReadout s View}
    {environment : Environment (Payload s View)} {parameter : Parameter}
    {invocation : ScopedValue (Payload s View)} {state : Decoded s View}
    (origin : CallAtReceipt operator readout environment parameter invocation state) : CallInput s :=
  (origin.raw.challenge
    (readout.event origin.before.fixedFrames origin.before.assignment.event (invocationBinder parameter) (.invocation origin.raw))
    (origin.before.callRow (invocationBinder parameter)).descriptor origin.before.viewMeaning).input

def Identity.formalDescriptor (source : Identity) (route : Route)
    (telescope : Telescope (OriginalReturnWorld.S b D ViewData Rest Body View) View source.ambient)
    (assignment : FormalAssignment (OriginalReturnWorld.S b D ViewData Rest Body View) View) : b.Descriptor :=
  ((source.introduction route telescope).selection assignment).valueDescriptor rfl

/-- The real original Build fixes its formal descriptor over the complete
prior telescope before every admitted invocation. At each actual receipt it
constructs the complete CallInput, decodes the same native Return, and derives
the Name result plus its body-consumer application from primitive Force data.
No entry/body judgment, full Call certificate, post-world/value membership,
proof/runtime event equation, or descriptor chosen per invocation is an input.
The remaining carrier/Force/independent-field obligations are fully exposed. -/
theorem generated_identity_name_realization
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
        ForceCut operator references use descriptor →
        ∃ bodyState,
          decode readout (retainedEnvironment (received.extend (returnBinder source.parameter) returned)
            source.parameter) = some bodyState ∧
          bodyState.assignment.event = use.bound descriptor ∧
          formalContract bodyState source.parameter = (intro.selection assignment).contract ∧
          NameRealization operator references use descriptor := by
  let intro := source.introduction route telescope
  let descriptor := source.formalDescriptor route telescope assignment
  let readout := OriginalReturnWorld.valueReadout baseReadout source.parameter views descriptor
  let kernel := closureKernel intro assignment (inputs operator references) registry declarations readout base ports original
  have localSolves : Satisfies
      (OriginalFormalAdmission.localKernel intro assignment (inputs operator references) readout (proofAdmissions base) kernel)
      (priorEnvironment intro prior)
      (Build intro.parameter.context (.lambda ⟨intro.parameter.lambdaSite, annotation⟩
        intro.parameter.formal intro.parameter.pattern intro.parameter.body)) := solves
  obtain ⟨description, view, _, _, _, descriptionAdmitted, viewAdmitted, every⟩ :=
    actual_build_from_whole_telescope intro assignment (inputs operator references) readout (proofAdmissions base)
      kernel prior annotation localSolves
  refine ⟨description, view, descriptionAdmitted, viewAdmitted, ?_⟩
  intro invocation invocationAdmitted
  obtain ⟨receipt, state, receiptAdmitted, decoded, selected, entry⟩ := every invocation invocationAdmitted
  obtain ⟨before, raw, beforeDecoded, payload, checked, active, descriptors⟩ :=
    receipt_recovers_call (inputs operator references) readout (closureAdmissions intro assignment base)
      _ source.parameter invocation receipt invocationAdmitted receiptAdmitted state decoded
  let origin : CallAtReceipt (inputs operator references) readout _ source.parameter invocation state :=
    ⟨before, raw, beforeDecoded, payload, checked, active, descriptors⟩
  refine ⟨receipt, state, receiptAdmitted, decoded, selected, origin, ?_⟩
  intro packet nameFields dispatch occurrence
  dsimp only
  intro returnedAdmitted cut
  have openHistory : (receivedEnvironment (priorEnvironment intro prior) source.parameter
      description view invocation receipt).replay = none :=
    invocation_receipt_open _ source.parameter invocation receipt
  obtain ⟨bodyState, bodyDecoded, bodyEvent, bodyPorts, bodyContract, action⟩ :=
    value_entry_consumer_at_receipt_ports intro assignment (inputs operator references) registry declarations
      readout base ports original _ state decoded rfl openHistory entry _ (packet.outcome views source.parameter)
      rfl returnedAdmitted
  refine ⟨bodyState, bodyDecoded, ?_, bodyContract.trans selected, ?_⟩
  · exact bodyEvent.trans (OriginalReturnWorld.computed_return_event baseReadout state.fixedFrames
      state.assignment.event source.parameter views descriptor packet)
  · exact name_realization_of_consumer operator references _ descriptor cut action

/-- The Force carrier uses the inlet of the very descriptor at original
invocation admission. Its raw carrier, root and event are exactly that complete
challenge's operands; no convenient admitted carrier is substituted. -/
theorem receipt_origin_carrier
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (readout baseReadout : RuntimeReadout (OriginalReturnWorld.S b D ViewData Rest Body View) View)
    (environment received : Environment (Payload (OriginalReturnWorld.S b D ViewData Rest Body View) View))
    (source : Identity) (invocation : ScopedValue (Payload (OriginalReturnWorld.S b D ViewData Rest Body View) View))
    (state : Decoded (OriginalReturnWorld.S b D ViewData Rest Body View) View)
    (origin : CallAtReceipt operator readout environment source.parameter invocation state)
    (views : ViewAssignment b Nat) (packet : OriginalReturnWorld.Packet b D ViewData Rest Body View)
    (fields : EventFields b) (dispatch : Option Nat) :
    let use : Use b D ViewData Rest Body View source :=
      ⟨baseReadout, views, state, received, origin.input, origin.active, packet, fields, dispatch⟩
    use.carrier operator =
      (origin.raw.challenge
        (readout.event origin.before.fixedFrames origin.before.assignment.event (invocationBinder source.parameter)
          (.invocation origin.raw))
        (origin.before.callRow (invocationBinder source.parameter)).descriptor origin.before.viewMeaning).carrierRow
        (operator.checkedInlet (origin.before.callRow (invocationBinder source.parameter)).descriptor) := by
  dsimp only [Use.carrier]
  rw [origin.descriptors]
  rfl

/-- Every lawful future and every actual provider of the returned formal
value use the original complete Call domain and all raw observations. This is
elimination of the Name's derived member, not introduction of the identity
closure's own Function membership. -/
theorem realized_name_future_function
    (operator : Inputs (OriginalReturnWorld.S b D ViewData Rest Body View))
    (references : Body → Nat → Option Name) (use : Use b D ViewData Rest Body View source)
    (descriptor : b.Descriptor) (realized : NameRealization operator references use descriptor)
    (form : operator.valueForm descriptor = .function)
    (later : Event (OriginalReturnWorld.S b D ViewData Rest Body View))
    (compatible : operator.compatible (use.named descriptor) later)
    (provider : b.Provider)
    (actual : operator.actual (use.views.value use.packet.raw.value) (use.views.root use.packet.raw.value) provider)
    (challenge : Challenge ((use.returnedRow descriptor).atEvent later))
    (admitted : CheckedDomain (inputs operator references) challenge) :
    ActualAdm (inputs operator references) provider challenge ∧
      ∀ observation, operator.execute provider challenge.input observation →
        ObservationMem (inputs operator references) (Meaning (inputs operator references)) challenge observation :=
  function_challenge (inputs operator references) ((use.returnedRow descriptor).atEvent later) form
    (realized.2.2.2.1 later compatible) provider actual challenge admitted

end YulangClosure.OriginalIdentityRealization
