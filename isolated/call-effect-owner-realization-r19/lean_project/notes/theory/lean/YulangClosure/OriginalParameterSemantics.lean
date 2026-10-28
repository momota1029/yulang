import YulangClosure.OriginalParameterWorld

/-!
Concrete missing-native world fields, with source telescope replay kept
separate from raw identity. No pre-existing Inputs or semantic sort is
identified with this new presentation by definition.
-/
namespace YulangClosure.OriginalParameterSemantics

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalParameterWorld OriginalWorldReadout
open OriginalRecursivePair NativeClosureEnvironment SourceIdentityWorld
variable {View : Type}

/-! The full typed prior telescope is an actual replayed input, not a
first-invocation search or a list of successful histories. All frame metadata
is retained; no fabricated empty parent path is supplied by this constructor. -/
inductive Telescope (s : Sorts) (View : Type) : List ScopeEntry → Type where
  | nil : Telescope s View []
  | cons (head : ScopeEntry) (tail : List ScopeEntry)
      (frame : Frame (Payload s View)) (binder : frame.binder = head.binder)
      (kind : frame.value.data.atKind head.binder.kind)
      (rest : Telescope s View tail) : Telescope s View (head :: tail)

def Telescope.frames : Telescope s View scope → List (Frame (Payload s View))
  | .nil => []
  | .cons _ _ frame _ _ rest => frame :: rest.frames

def Telescope.values : (telescope : Telescope s View scope) → ScopeValues s View scope
  | .nil => ()
  | .cons _ _ frame _ kind rest => (⟨frame.value.data, kind⟩, rest.values)

def replayTelescope (readout : RuntimeReadout s View) (state : Decoded s View)
    (telescope : Telescope s View scope) : Decoded s View :=
  telescope.frames.foldl (decodeFrame readout) state

theorem telescope_keeps_binders (telescope : Telescope s View scope) :
    telescope.frames.map Frame.binder = scope.map ScopeEntry.binder := by
  induction telescope with
  | nil => rfl
  | cons head tail frame binder kind rest ih =>
      simp only [Telescope.frames, List.map_cons, binder, ih]

theorem telescope_keeps_payloads (head : ScopeEntry) (tail : List ScopeEntry)
    (frame : Frame (Payload s View)) (binder : frame.binder = head.binder)
    (kind : frame.value.data.atKind head.binder.kind) (rest : Telescope s View tail) :
    (Telescope.cons head tail frame binder kind rest).values.1.val = frame.value.data ∧
    (Telescope.cons head tail frame binder kind rest).frames.head? = some frame := ⟨rfl, rfl⟩

/-- Root-Lambda declaration from its actual complete replayed telescope. -/
def declareValueFormal (readout : RuntimeReadout s View) (initial : Decoded s View)
    (assignment : FormalAssignment s View) (parameter : Parameter) (route : Route)
    (telescope : Telescope s View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.value) : Decoded s View :=
  let before := replayTelescope readout initial telescope
  before.logical
    ⟨[(⟨parameter.formal.site, .descriptor⟩,
      (select assignment parameter route telescope.values).valueDescriptor mode)], [],
      before.viewMeaning, before.assignment.event.eta, before.assignment.event.witness⟩

theorem selected_at_original_formal (readout : RuntimeReadout s View) (initial : Decoded s View)
    (assignment : FormalAssignment s View) (parameter : Parameter) (route : Route)
    (telescope : Telescope s View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.value) :
    (declareValueFormal readout initial assignment parameter route telescope mode).assignment.descriptor
      ⟨parameter.formal.site, .descriptor⟩ =
      (select assignment parameter route telescope.values).valueDescriptor mode := by
  simp [declareValueFormal, Decoded.logical, put]

theorem declaration_uses_entire_prior (readout : RuntimeReadout s View) (initial : Decoded s View)
    (assignment : FormalAssignment s View) (parameter : Parameter) (route : Route)
    (telescope : Telescope s View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.value) :
    telescope.frames.map Frame.binder = parameter.ambient.map ScopeEntry.binder ∧
    (declareValueFormal readout initial assignment parameter route telescope mode).installed =
      (replayTelescope readout initial telescope).installed :=
  ⟨telescope_keeps_binders _, rfl⟩

/-- The actual original Lambda has this Description binder before its
invocation. No Site freshness or annotation-shape inference is used. -/
theorem source_formal_description_binder (parameter : Parameter) :
    (match sourceRules parameter.context parameter.source with
      | .existsE binder _ => some binder
      | _ => none) = some (⟨parameter.formal.site, .description, 0⟩ : Binder) := by
  cases parameter
  simp only [Parameter.source, sourceRules]
  rfl

def formalDescriptionFrame (readout : RuntimeReadout s View) (initial : Decoded s View)
    (assignment : FormalAssignment s View) (parameter : Parameter) (route : Route)
    (telescope : Telescope s View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.value)
    (actual : ActualEvent (Payload s View)) (entryPath : List (EventStep (Payload s View))) :
    Frame (Payload s View) :=
  let before := replayTelescope readout initial telescope
  ⟨⟨parameter.formal.site, .description, 0⟩,
    ⟨.logical .description
      ⟨[(⟨parameter.formal.site, .descriptor⟩,
        (select assignment parameter route telescope.values).valueDescriptor mode)], [],
        before.viewMeaning, before.assignment.event.eta, before.assignment.event.witness⟩,
      actual⟩, entryPath⟩

theorem decode_formal_description (readout : RuntimeReadout s View) (initial : Decoded s View)
    (assignment : FormalAssignment s View) (parameter : Parameter) (route : Route)
    (telescope : Telescope s View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.value)
    (actual : ActualEvent (Payload s View)) (entryPath : List (EventStep (Payload s View))) :
    decodeFrame readout (replayTelescope readout initial telescope)
      (formalDescriptionFrame readout initial assignment parameter route telescope mode actual entryPath) =
      declareValueFormal readout initial assignment parameter route telescope mode := rfl

theorem description_keeps_actual_metadata (readout : RuntimeReadout s View) (initial : Decoded s View)
    (assignment : FormalAssignment s View) (parameter : Parameter) (route : Route)
    (telescope : Telescope s View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.value)
    (actual : ActualEvent (Payload s View)) (entryPath : List (EventStep (Payload s View))) :
    (formalDescriptionFrame readout initial assignment parameter route telescope mode actual entryPath).value.event = actual ∧
    (formalDescriptionFrame readout initial assignment parameter route telescope mode actual entryPath).entryPath = entryPath :=
  ⟨rfl, rfl⟩

/-! Scoped Shared strategy arguments include every typed predecessor. They
remain separate from the complete raw key and from description proof uses. -/
structure SharedPosition (s : Sorts) (View : Type) where
  introduction : OriginalSourceEvents.Owner
  prior : ScopeValues s View introduction.telescope
  key : SharedKey s View

structure SharedReference (s : Sorts) (View : Type) where
  target : SharedPosition s View
  useRoute : Route

abbrev ScopedShared (s : Sorts) (View : Type) := SharedPosition s View → s.WitnessValue

def retainedPosition (parameter : Parameter) (selection : Selected s View parameter)
    (prior : ScopeValues s View parameter.registration.retainedOwner.telescope)
    (actual : RawKey s View) : SharedPosition s View :=
  ⟨parameter.registration.retainedOwner, prior, parameterSharedKey parameter selection actual⟩

theorem scoped_shared_keeps_owner (parameter : Parameter) (selection : Selected s View parameter)
    (prior : ScopeValues s View parameter.registration.retainedOwner.telescope)
    (actual : RawKey s View) :
    (retainedPosition parameter selection prior actual).introduction =
      parameter.registration.retainedOwner ∧
    (retainedPosition parameter selection prior actual).key.actual = actual := ⟨rfl, rfl⟩

theorem different_proof_uses_share (assignment : ScopedShared s View)
    (position : SharedPosition s View) (first second : Route) :
    assignment (SharedReference.mk position first).target =
      assignment (SharedReference.mk position second).target := rfl

/-- The typed predecessor tuple is not erased from a Shared position even
when its raw key is the same. This is independent of EventProof use routes. -/
theorem shared_position_keeps_typed_prior (owner : OriginalSourceEvents.Owner)
    (first second : ScopeValues s View owner.telescope) (different : first ≠ second)
    (key : SharedKey s View) :
    (⟨owner, first, key⟩ : SharedPosition s View) ≠ ⟨owner, second, key⟩ := by
  intro same
  cases same
  exact different rfl

/-! Raw native snapshots retain every cell, provider, alias registration,
receiving/control/rest field and opaque remaining current field. Invalid raw
records remain representable; no decoding or membership test admits them. -/
structure AliasReference where
  declaration : Declaration
  introduction : Route
  environment : Nat
  original : Name
  aliasName : Name

structure Snapshot (b : Sorts) (D V ViewData SiteData Rest Body : Type) where
  residual : b.Configuration
  world : World Name D V ViewData SiteData Rest
  providers : b.Provider → Option (Closure Body)
  aliases : List AliasReference

structure NativeAssignment (b : Sorts) (V : Type) where
  original : b.Assignment
  views : ViewAssignment b V

structure NativeWitness (b : Sorts) (View : Type) where
  current : b.JointWitness
  shared : ScopedShared b View

/-- This defines genuinely missing native sorts, not an isomorphism from an
arbitrary previously fixed Configuration/Assignment universe. -/
abbrev nativeSorts (b : Sorts) (D V ViewData SiteData Rest Body View : Type) : Sorts :=
  {b with
    Configuration := Snapshot b D V ViewData SiteData Rest Body
    Assignment := NativeAssignment b V
    JointWitness := NativeWitness b View
    WitnessPosition := SharedReference b View}

abbrev NS (b : Sorts) (D V ViewData SiteData Rest Body View : Type) :=
  nativeSorts b D V ViewData SiteData Rest Body View

structure Presentation (b : Sorts) (D V ViewData SiteData Rest Body View : Type) where
  fiber : Fiber (NS b D V ViewData SiteData Rest Body View)
  initial : NativeAssignment b V
  assignment : NativeAssignment b V
  history : b.History
  snapshot : Snapshot b D V ViewData SiteData Rest Body
  witnesses : NativeWitness b View
  scope : b.Scope
  authority : b.Authority
  incidence : b.Incidence
  dictionary : b.Dictionary

def pack (data : Presentation b D V ViewData SiteData Rest Body View) :
    Event (NS b D V ViewData SiteData Rest Body View) :=
  ⟨data.fiber, data.initial, data.assignment, data.history, data.snapshot,
    data.witnesses, data.scope, data.authority, data.incidence, data.dictionary⟩

def unpack (event : Event (NS b D V ViewData SiteData Rest Body View)) :
    Presentation b D V ViewData SiteData Rest Body View :=
  ⟨event.fiber, event.eta0, event.eta, event.history, event.current,
    event.witness, event.scope, event.authority, event.incidence, event.dictionary⟩

theorem unpack_pack (data : Presentation b D V ViewData SiteData Rest Body View) :
    unpack (pack data) = data := by cases data; rfl

theorem pack_unpack (event : Event (NS b D V ViewData SiteData Rest Body View)) :
    pack (unpack event) = event := by cases event; rfl

def viewAssignment (data : NativeAssignment b V) :
    ViewAssignment (NS b D V ViewData SiteData Rest Body View) V :=
  ⟨data.views.descriptor, data.views.interface, data.views.value, data.views.carrier, data.views.root⟩

def installed (event : Event (NS b D V ViewData SiteData Rest Body View)) :
    Nat → Option (Installed (NS b D V ViewData SiteData Rest Body View)) :=
  bindingReadout (viewAssignment event.eta) event.current.world.cells

def aliasAt (event : Event (NS b D V ViewData SiteData Rest Body View)) (first second : Nat) : Prop :=
  ∃ reference ∈ event.current.aliases,
    lookupKey reference.original event.current.world.environments reference.environment = some first ∧
    lookupKey reference.aliasName event.current.world.environments reference.environment = some second

def captureAt (references : Body → Nat → Option Name)
    (event : Event (NS b D V ViewData SiteData Rest Body View))
    (provider : b.Provider) (name : Nat) : Option Nat :=
  (event.current.providers provider).bind fun closure =>
    captureAddress event.current.world.environments closure references name

/-- One missing-native Inputs is fixed before any Force. Every nonworld
field, independent domain and raw transition is inherited unchanged. Captures
and aliases are raw lookups, including guard-failing dangling records. -/
def inputs (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name) : Inputs (NS b D V ViewData SiteData Rest Body View) :=
  {base with
    installedCount := fun event => event.current.world.cells.size
    installed := installed
    alias := aliasAt
    capture := captureAt references
    captureValue := fun event provider name => (captureAt references event provider name).bind (installed event)
    sharedPosition := fun _ first second => first.target = second.target
    witnessAt := fun event position => event.witness.shared position.target}

theorem every_native_some (event : Event (NS b D V ViewData SiteData Rest Body View))
    (index : Nat) (raw : Received V) (found : event.current.world.cells.cell index = some raw) :
    installed event index = some ((viewAssignment event.eta).received index raw) :=
  every_cell_readout _ _ _ _ found

theorem native_inputs_keep_domains (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name) {row : ValueRow (NS b D V ViewData SiteData Rest Body View)}
    (challenge : Challenge row) :
    CheckedDomain (inputs base references) challenge ↔ CheckedDomain base challenge := Iff.rfl

theorem native_inputs_keep_force (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (carrier : CarrierInput (NS b D V ViewData SiteData Rest Body View))
    (atEvent : Event (NS b D V ViewData SiteData Rest Body View))
    (observation : RawObservation (NS b D V ViewData SiteData Rest Body View)) :
    (inputs base references).force carrier atEvent observation ↔ base.force carrier atEvent observation := Iff.rfl

theorem native_inputs_keep_trace (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (row : TraceRow (NS b D V ViewData SiteData Rest Body View)) :
    (inputs base references).traceForm row = base.traceForm row ∧
    (inputs base references).observationFields row = base.observationFields row := ⟨rfl, rfl⟩

/-- A malformed raw capture remains visible as a dangling capture. The
constructor never removes it to make CapturesAgree or admission easier. -/
theorem dangling_capture_not_erased
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (event : Event (NS b D V ViewData SiteData Rest Body View))
    (provider : b.Provider) (name address : Nat) (closure : Closure Body)
    (registered : event.current.providers provider = some closure)
    (resolved : captureAddress event.current.world.environments closure references name = some address)
    (missing : event.current.world.cells.cell address = none) :
    (inputs base references).capture event provider name = some address ∧
    (inputs base references).captureValue event provider name = none := by
  have captured : captureAt references event provider name = some address := by
    simp only [captureAt, registered, Option.bind_some, resolved]
  refine ⟨captured, ?_⟩
  change (captureAt references event provider name).bind (installed event) = none
  rw [captured]
  simp only [Option.bind_some, installed, bindingReadout, missing, Option.map_none]

/-- Initial decoder representation is constructed, not supplied as a whole
installed-map equation. This is a new native root, not a reset of an existing
source Environment. All unrelated source projections remain explicit data. -/
def initialRoot (event : Event (NS b D V ViewData SiteData Rest Body View))
    (source : SourceAssignment (NS b D V ViewData SiteData Rest Body View))
    (interfaces : Endpoint → b.Interface) (carriers : Endpoint → b.Carrier)
    (views : View → b.Interface) (owners : List CallOwner) :
    Root (NS b D V ViewData SiteData Rest Body View) View :=
  ⟨{source with event}, interfaces, carriers, views, installed event, owners⟩

theorem initial_decoded_readout (event : Event (NS b D V ViewData SiteData Rest Body View))
    (source : SourceAssignment (NS b D V ViewData SiteData Rest Body View))
    (interfaces : Endpoint → b.Interface) (carriers : Endpoint → b.Carrier)
    (views : View → b.Interface) (owners : List CallOwner) :
    (initialRoot event source interfaces carriers views owners).decoded.installed = installed event ∧
    (initialRoot event source interfaces carriers views owners).decoded.assignment.event = event := ⟨rfl, rfl⟩

structure EventFields (b : Sorts) where
  history : b.History
  assignment : b.Assignment
  witness : b.JointWitness
  scope : b.Scope
  authority : b.Authority
  incidence : b.Incidence
  dictionary : b.Dictionary

/-- Actual bind changes the current native world and the fresh cell's derived
contract. The scoped Shared strategy is fixed; new typed positions may have
new values, while all older positions retain theirs. Current EventFields can
change independently of that strategy. -/
def bindEvent (before : Event (NS b D V ViewData SiteData Rest Body View))
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b) :
    Event (NS b D V ViewData SiteData Rest Body View) :=
  {before with
    history := fields.history
    current := {before.current with world := bindValue before.current.world parent formal raw node found}
    eta := ⟨fields.assignment,
      installValueContract before.eta.views before.current.world.cells.size descriptor⟩
    witness := ⟨fields.witness, before.witness.shared⟩
    scope := fields.scope, authority := fields.authority,
    incidence := fields.incidence, dictionary := fields.dictionary}

theorem bind_keeps_static_fiber (before : Event (NS b D V ViewData SiteData Rest Body View))
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b) :
    (bindEvent before parent formal raw node found descriptor fields).fiber = before.fiber ∧
    (bindEvent before parent formal raw node found descriptor fields).eta0 = before.eta0 := ⟨rfl, rfl⟩

theorem bind_current_fields (before : Event (NS b D V ViewData SiteData Rest Body View))
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b) :
    (bindEvent before parent formal raw node found descriptor fields).witness.current = fields.witness ∧
    (bindEvent before parent formal raw node found descriptor fields).eta.original = fields.assignment := ⟨rfl, rfl⟩

theorem bind_uses_current_history (before : Event (NS b D V ViewData SiteData Rest Body View))
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b) :
    (bindEvent before parent formal raw node found descriptor fields).history = fields.history ∧
    (bindEvent before parent formal raw node found descriptor fields).current.residual = before.current.residual :=
  ⟨rfl, rfl⟩

theorem bind_existing_shared (before : Event (NS b D V ViewData SiteData Rest Body View))
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b) (position : SharedPosition b View) :
    (bindEvent before parent formal raw node found descriptor fields).witness.shared position =
      before.witness.shared position := rfl

theorem bind_installed (before : Event (NS b D V ViewData SiteData Rest Body View))
    (cells : List (Option (Received V))) (vector : before.current.world.cells = vectorStore cells)
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b) :
    installed (bindEvent before parent formal raw node found descriptor fields) =
      extendBindings (installed before) before.current.world.cells.size
        (.value descriptor (before.eta.views.value raw.value) (before.eta.views.root raw.value)) := by
  change bindingReadout
    (installValueContract (viewAssignment before.eta) before.current.world.cells.size descriptor)
    (bindValue before.current.world parent formal raw node found).cells = _
  rw [parameter_bind_readout]
  have empty : before.current.world.cells.cell before.current.world.cells.size = none := by
    rw [vector]
    exact vector_cell_beyond cells cells.length (Nat.le_refl _)
  rw [fresh_contract_before_readout (viewAssignment before.eta) before.current.world.cells
    before.current.world.cells.size empty descriptor]
  simp only [installValueContract, ite_true]
  rfl

theorem bind_old_installed (before : Event (NS b D V ViewData SiteData Rest Body View))
    (cells : List (Option (Received V))) (vector : before.current.world.cells = vectorStore cells)
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b)
    (index : Nat) (object : Installed (NS b D V ViewData SiteData Rest Body View))
    (present : installed before index = some object) :
    installed (bindEvent before parent formal raw node found descriptor fields) index = some object := by
  rw [bind_installed before cells vector parent formal raw node found descriptor fields]
  apply extend_bindings_old _ present
  unfold installed bindingReadout
  rw [vector]
  rw [show (vectorStore cells).cell (vectorStore cells).size = none from
    vector_cell_beyond cells cells.length (Nat.le_refl _)]
  rfl

theorem bind_capture_address (references : Body → Nat → Option Name)
    (before : Event (NS b D V ViewData SiteData Rest Body View))
    (saved : ∀ provider closure, before.current.providers provider = some closure →
      closure.savedEnvironment < before.current.world.environments.size)
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b) (provider : b.Provider) (name : Nat) :
    captureAt references (bindEvent before parent formal raw node found descriptor fields) provider name =
      captureAt references before provider name := by
  unfold captureAt
  change (before.current.providers provider).bind _ = _
  cases present : before.current.providers provider with
  | none => rfl
  | some closure =>
      exact capture_address_parameter_bind before.current.world closure
        (saved provider closure present) references name parent formal raw node found

theorem bind_aliases (before : Event (NS b D V ViewData SiteData Rest Body View))
    (saved : ∀ reference ∈ before.current.aliases,
      reference.environment < before.current.world.environments.size)
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b) (first second : Nat) :
    aliasAt (bindEvent before parent formal raw node found descriptor fields) first second ↔
      aliasAt before first second := by
  unfold aliasAt
  change (∃ reference ∈ before.current.aliases, _ ∧ _) ↔ _
  apply exists_congr
  intro reference
  apply and_congr_right
  intro registered
  simp only [bindEvent, bindValue, extendNode, lookupKey]
  rw [lookup_old _ _ _ _ _ _ (saved reference registered),
    lookup_old _ _ _ _ _ _ (saved reference registered)]

/-- Full PhiW for the computed constructor. The prior world clause and
actual returned field are recursive premises; no post-world or registry
commutation equation is a premise. Old values/carriers are transported at
their actual unchanged descriptors by the given candidate restriction action. -/
theorem bind_phiW
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (candidate : Family (NS b D V ViewData SiteData Rest Body View))
    (before : Event (NS b D V ViewData SiteData Rest Body View))
    (old : PhiW (inputs base references) candidate before)
    (cells : List (Option (Received V))) (vector : before.current.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, before.current.providers provider = some closure →
      closure.savedEnvironment < before.current.world.environments.size)
    (savedAliases : ∀ reference ∈ before.current.aliases,
      reference.environment < before.current.world.environments.size)
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b)
    (coherent : base.eventCoherent (bindEvent before parent formal raw node found descriptor fields))
    (guards : (base.worldGuards (bindEvent before parent formal raw node found descriptor fields)).Valid)
    (restrict : ∀ object : Installed (NS b D V ViewData SiteData Rest Body View), object.Valid candidate before →
      object.Valid candidate (bindEvent before parent formal raw node found descriptor fields))
    (returned : candidate (.value ⟨descriptor, before.eta.views.value raw.value,
      before.eta.views.root raw.value, bindEvent before parent formal raw node found descriptor fields⟩)) :
    PhiW (inputs base references) candidate (bindEvent before parent formal raw node found descriptor fields) := by
  let after := bindEvent before parent formal raw node found descriptor fields
  refine ⟨coherent, guards, ?_, ?_, ?_, ?_⟩
  · intro first second same
    have previous : aliasAt before first second :=
      (bind_aliases before savedAliases parent formal raw node found descriptor fields first second).mp same
    obtain ⟨object, firstFound, secondFound⟩ := old.2.2.1 first second previous
    exact ⟨object,
      bind_old_installed before cells vector parent formal raw node found descriptor fields first object firstFound,
      bind_old_installed before cells vector parent formal raw node found descriptor fields second object secondFound⟩
  · intro provider name address captured
    change captureAt references after provider name = some address at captured
    have previous : captureAt references before provider name = some address := by
      rw [← bind_capture_address references before savedProviders parent formal raw node found descriptor fields provider name]
      exact captured
    obtain ⟨bounded, object, present, _⟩ := old.2.2.2.1 provider name address previous
    have current := bind_old_installed before cells vector parent formal raw node found descriptor fields
      address object present
    refine ⟨Nat.lt_succ_of_lt bounded, object, current, ?_⟩
    change (captureAt references after provider name).bind (installed after) = some object
    rw [captured]
    exact current
  · intro first second same
    exact congrArg after.witness.shared same
  · intro index object present
    change installed after index = some object at present
    dsimp only [after] at present
    rw [bind_installed before cells vector parent formal raw node found descriptor fields] at present
    unfold extendBindings at present
    split at present
    · cases Option.some.inj present
      exact returned
    · exact restrict object (old.2.2.2.2.2 index object present)

/-- Complete captured-value readout under the changed address assignment,
using the old world's actual capture equation and the real bind readout. -/
theorem bind_capture_value
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (before : Event (NS b D V ViewData SiteData Rest Body View))
    (captures : CapturesAgree (inputs base references) before)
    (cells : List (Option (Received V))) (vector : before.current.world.cells = vectorStore cells)
    (saved : ∀ provider closure, before.current.providers provider = some closure →
      closure.savedEnvironment < before.current.world.environments.size)
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b) (provider : b.Provider) (name : Nat) :
    (inputs base references).captureValue (bindEvent before parent formal raw node found descriptor fields)
      provider name = (inputs base references).captureValue before provider name := by
  change (captureAt references _ provider name).bind (installed _) =
    (captureAt references before provider name).bind (installed before)
  rw [bind_capture_address references before saved parent formal raw node found descriptor fields]
  cases present : captureAt references before provider name with
  | none => rfl
  | some address =>
      obtain ⟨_, object, cell, _⟩ := captures provider name address present
      change installed before address = some object at cell
      simp only [Option.bind_some]
      rw [cell]
      exact bind_old_installed before cells vector parent formal raw node found descriptor fields address object cell

/-! Original shared-reference aliases retain one existing native address.
This constructor does not infer monomorphic sharing from equal raw values. -/
theorem native_alias_same_cell (world : World Name D V ViewData SiteData Rest)
    (parent : Nat) (original aliasName : Name) (address : Nat) (dispatch : D)
    (resolved : lookupKey original world.environments parent = some address) :
    let arena := world.environments.append parent (some (aliasName, address)) dispatch
    lookupKey original arena world.environments.size = some address ∧
      lookupKey aliasName arena world.environments.size = some address := by
  dsimp only
  refine ⟨?_, parameter_shadows _ _ _ _ _⟩
  by_cases same : aliasName = original
  · subst aliasName
    exact parameter_shadows _ _ _ _ _
  · simpa only [lookupKey, lookup_new, decide_eq_false same, Bool.false_eq_true,
      ite_false] using resolved

def nativeAliasData (assignment : ViewAssignment s V) (cells : List (Option (Received V)))
    (address : Nat) (raw : Received V) (present : (vectorStore cells).cell address = some raw) :
    AliasData (bindingReadout assignment (vectorStore cells)) cells.length :=
  ⟨address, address, vector_some_bound cells address raw present,
    vector_some_bound cells address raw present, assignment.received address raw,
    every_cell_readout _ _ _ _ present, every_cell_readout _ _ _ _ present⟩

theorem native_alias_reads_same_contract (assignment : ViewAssignment s V)
    (cells : List (Option (Received V))) (address : Nat) (raw : Received V)
    (present : (vectorStore cells).cell address = some raw) :
    (nativeAliasData assignment cells address raw present).left = address ∧
    (nativeAliasData assignment cells address raw present).right = address ∧
    (nativeAliasData assignment cells address raw present).object = assignment.received address raw :=
  ⟨rfl, rfl, rfl⟩

/-- Completed Meaning has its own genuine hereditary action. This does not
reuse a completed check as an action on declared-hole membership. -/
theorem meaning_installed_restrict (operator : Inputs s) (object : Installed s)
    (before after : Event s) (member : object.Valid (Meaning operator) before)
    (later : operator.compatible before after) : object.Valid (Meaning operator) after := by
  cases object with
  | value descriptor value root =>
      have opened := greatest_unfold (Phi operator) (phi_monotone operator)
        (.value ⟨descriptor, value, root, before⟩) member
      exact opened.2 after later
  | carrier interface carrier root =>
      have opened := greatest_unfold (Phi operator) (phi_monotone operator)
        (.carrier ⟨interface, carrier, root, before⟩) member
      exact opened.2.2.2.2.2 after later

theorem bind_meaning_world
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (before : Event (NS b D V ViewData SiteData Rest Body View))
    (old : Meaning (inputs base references) (.world before))
    (cells : List (Option (Received V))) (vector : before.current.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, before.current.providers provider = some closure →
      closure.savedEnvironment < before.current.world.environments.size)
    (savedAliases : ∀ reference ∈ before.current.aliases,
      reference.environment < before.current.world.environments.size)
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b)
    (later : base.compatible before (bindEvent before parent formal raw node found descriptor fields))
    (coherent : base.eventCoherent (bindEvent before parent formal raw node found descriptor fields))
    (guards : (base.worldGuards (bindEvent before parent formal raw node found descriptor fields)).Valid)
    (returned : Meaning (inputs base references) (.value ⟨descriptor, before.eta.views.value raw.value,
      before.eta.views.root raw.value, before⟩)) :
    Meaning (inputs base references) (.world (bindEvent before parent formal raw node found descriptor fields)) := by
  let operator := inputs base references
  have oldClause := greatest_unfold (Phi operator) (phi_monotone operator) (.world before) old
  apply greatest_fold (Phi operator) (phi_monotone operator)
  apply bind_phiW base references (Meaning operator) before oldClause cells vector
    savedProviders savedAliases parent formal raw node found descriptor fields coherent guards
  · intro object member
    exact meaning_installed_restrict operator object before _ member later
  · exact meaning_installed_restrict operator
      (.value descriptor (before.eta.views.value raw.value) (before.eta.views.root raw.value))
      before _ returned later

/-- The analogous exact B_H constructor uses B_H's own hereditary action.
Its returned-field premise is not supplied by completed Checking.sound. -/
theorem bind_background_world
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (holes : ValueRow (NS b D V ViewData SiteData Rest Body View) → Prop)
    (holeFuture : ∀ row later, holes row → base.compatible row.event later → holes (row.atEvent later))
    (before : Event (NS b D V ViewData SiteData Rest Body View))
    (old : Background (inputs base references) holes (.world before))
    (cells : List (Option (Received V))) (vector : before.current.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, before.current.providers provider = some closure →
      closure.savedEnvironment < before.current.world.environments.size)
    (savedAliases : ∀ reference ∈ before.current.aliases,
      reference.environment < before.current.world.environments.size)
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b)
    (later : base.compatible before (bindEvent before parent formal raw node found descriptor fields))
    (coherent : base.eventCoherent (bindEvent before parent formal raw node found descriptor fields))
    (guards : (base.worldGuards (bindEvent before parent formal raw node found descriptor fields)).Valid)
    (returned : Background (inputs base references) holes (.value ⟨descriptor, before.eta.views.value raw.value,
      before.eta.views.root raw.value, before⟩)) :
    Background (inputs base references) holes
      (.world (bindEvent before parent formal raw node found descriptor fields)) := by
  let operator := inputs base references
  have opened := greatest_unfold (RelativePhi operator holes) (relative_monotone operator holes)
    (.world before) old
  rcases opened with oldClause | impossible
  · apply greatest_fold (RelativePhi operator holes) (relative_monotone operator holes)
    apply Or.inl
    apply bind_phiW base references (Background operator holes) before oldClause cells vector
      savedProviders savedAliases parent formal raw node found descriptor fields coherent guards
    · intro object member
      exact background_installed_restrict operator holes holeFuture object before _ member later
    · exact background_installed_restrict operator holes holeFuture
        (.value descriptor (before.eta.views.value raw.value) (before.eta.views.root raw.value))
        before _ returned later
  · cases impossible

/-- The formal source consumer has no free descriptor slot: the target is
read from the actual declaration constructed over the complete prior frames.
Its recursive premises are the old world and this actual returned field.
The source's Force-to-that-field incidence remains a separate obligation. -/
theorem source_formal_phiW
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (candidate : Family (NS b D V ViewData SiteData Rest Body View))
    (readout : RuntimeReadout (NS b D V ViewData SiteData Rest Body View) View)
    (initial : Decoded (NS b D V ViewData SiteData Rest Body View) View)
    (assignment : FormalAssignment (NS b D V ViewData SiteData Rest Body View) View)
    (parameter : Parameter) (route : Route)
    (telescope : Telescope (NS b D V ViewData SiteData Rest Body View) View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.value)
    (old : PhiW (inputs base references) candidate
      (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event)
    (cells : List (Option (Received V)))
    (vector : (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event.current.world.cells =
      vectorStore cells)
    (savedProviders : ∀ provider closure,
      (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event.current.providers provider =
        some closure → closure.savedEnvironment <
          (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event.current.world.environments.size)
    (savedAliases : ∀ reference ∈
      (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event.current.aliases,
      reference.environment <
        (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event.current.world.environments.size)
    (parent : Nat) (raw : Received V) (node : Node Name D)
    (found : nodeAt (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event.current.world.environments
      parent = some node) (fields : EventFields b)
    (coherent : base.eventCoherent (bindEvent
      (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event
      parent parameter.formal.name raw node found
      ((select assignment parameter route telescope.values).valueDescriptor mode) fields))
    (guards : (base.worldGuards (bindEvent
      (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event
      parent parameter.formal.name raw node found
      ((select assignment parameter route telescope.values).valueDescriptor mode) fields)).Valid)
    (restrict : ∀ object : Installed (NS b D V ViewData SiteData Rest Body View),
      object.Valid candidate (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event →
      object.Valid candidate (bindEvent
        (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event
        parent parameter.formal.name raw node found
        ((select assignment parameter route telescope.values).valueDescriptor mode) fields))
    (returned : candidate (.value ⟨(select assignment parameter route telescope.values).valueDescriptor mode,
      (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event.eta.views.value raw.value,
      (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event.eta.views.root raw.value,
      bindEvent (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event
        parent parameter.formal.name raw node found
        ((select assignment parameter route telescope.values).valueDescriptor mode) fields⟩)) :
    (declareValueFormal readout initial assignment parameter route telescope mode).assignment.descriptor
      ⟨parameter.formal.site, .descriptor⟩ = (select assignment parameter route telescope.values).valueDescriptor mode ∧
    telescope.frames.map Frame.binder = parameter.ambient.map ScopeEntry.binder ∧
    PhiW (inputs base references) candidate (bindEvent
      (declareValueFormal readout initial assignment parameter route telescope mode).assignment.event
      parent parameter.formal.name raw node found
      ((select assignment parameter route telescope.values).valueDescriptor mode) fields) :=
  ⟨selected_at_original_formal readout initial assignment parameter route telescope mode,
   telescope_keeps_binders telescope,
   bind_phiW base references candidate _ old cells vector savedProviders savedAliases
     parent parameter.formal.name raw node found _ fields coherent guards restrict returned⟩

/-! Nonvacuous data distinctions for the computed presentation. -/
theorem changed_current_keeps_old_shared
    (before : Event (NS b D V ViewData SiteData Rest Body View))
    (parent : Nat) (formal : Name) (raw : Received V) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (descriptor : b.Descriptor) (fields : EventFields b)
    (different : fields.witness ≠ before.witness.current) (position : SharedPosition b View) :
    (bindEvent before parent formal raw node found descriptor fields).witness.current ≠ before.witness.current ∧
    (bindEvent before parent formal raw node found descriptor fields).witness.shared position =
      before.witness.shared position := ⟨different, rfl⟩

theorem same_native_cells_different_scoped_values
    (event : Event (NS b D V ViewData SiteData Rest Body View))
    (first second : ScopedShared b View) (position : SharedPosition b View)
    (different : first position ≠ second position) :
    ({event with witness := ⟨event.witness.current, first⟩}).current =
      ({event with witness := ⟨event.witness.current, second⟩}).current ∧
    ({event with witness := ⟨event.witness.current, first⟩}).witness.shared position ≠
      ({event with witness := ⟨event.witness.current, second⟩}).witness.shared position := ⟨rfl, different⟩

theorem same_view_distinct_cell_meanings (assignment : NativeAssignment b Nat)
    (different : assignment.views.descriptor 0 OriginalWorldReadout.Discriminator.first.view ≠
      assignment.views.descriptor 1 OriginalWorldReadout.Discriminator.first.view) :
    bindingReadout (viewAssignment (D := D) (ViewData := ViewData) (SiteData := SiteData)
      (Rest := Rest) (Body := Body) (View := View) assignment)
      (vectorStore [some OriginalWorldReadout.Discriminator.first, some OriginalWorldReadout.Discriminator.first]) 0 ≠
    bindingReadout (viewAssignment (D := D) (ViewData := ViewData) (SiteData := SiteData)
      (Rest := Rest) (Body := Body) (View := View) assignment)
      (vectorStore [some OriginalWorldReadout.Discriminator.first, some OriginalWorldReadout.Discriminator.first]) 1 :=
  OriginalWorldReadout.Discriminator.same_view_separate_cell_contracts _ different

theorem pending_has_no_returned_constructor (pending : Outcome s) (noResult : pending.result = none)
    (returned : Returned s) : pending ≠ returned.outcome := by
  intro same
  have result := congrArg Outcome.result same
  rw [noResult] at result
  cases result

end YulangClosure.OriginalParameterSemantics
