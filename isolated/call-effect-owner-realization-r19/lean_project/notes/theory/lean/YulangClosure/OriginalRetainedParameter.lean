import YulangClosure.OriginalParameterSemantics

/-! The actual post-receipt Computation bind stores the carrier without
executing it. Source/native entry and scoped-presentation boundaries remain
explicit; this module does not change the existing Value bind. -/
namespace YulangClosure.OriginalRetainedParameter

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalParameterWorld OriginalWorldReadout OriginalRecursivePair
open OriginalParameterSemantics NativeClosureEnvironment SourceIdentityWorld
variable {View : Type}

/-- Exact record stored after actual receiving.enter/receipt. -/
def packet (delay : V) (selectedView : Nat) : Received V :=
  ⟨delay, .computation, selectedView, none⟩

/-- The native plain bind does not execute or convert this carrier. -/
def bindRetained (world : World K D V ViewData SiteData Rest)
    (parent : Nat) (formal : K) (delay : V) (selectedView : Nat)
    (node : Node K D) (found : nodeAt world.environments parent = some node) :
    World K D V ViewData SiteData Rest :=
  {world with
    cells := world.cells.push (packet delay selectedView)
    environments := extendNode world.environments parent formal world.cells.size node found}

theorem stored_carrier_record (world : World K D V ViewData SiteData Rest)
    (parent : Nat) (formal : K) (delay : V) (selectedView : Nat)
    (node : Node K D) (found : nodeAt world.environments parent = some node) :
    (bindRetained world parent formal delay selectedView node found).cells.cell world.cells.size =
      some ⟨delay, .computation, selectedView, none⟩ := push_current _ _

theorem retained_preserves_native_fields (world : World K D V ViewData SiteData Rest)
    (parent : Nat) (formal : K) (delay : V) (selectedView : Nat)
    (node : Node K D) (found : nodeAt world.environments parent = some node) :
    (bindRetained world parent formal delay selectedView node found).receiving = world.receiving ∧
    (bindRetained world parent formal delay selectedView node found).control = world.control ∧
    (bindRetained world parent formal delay selectedView node found).rest = world.rest ∧
    (nodeAt (bindRetained world parent formal delay selectedView node found).environments world.environments.size).map
      Node.dispatch = some node.dispatch := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simp [bindRetained, extendNode, nodeAt]

theorem retained_native_vector (world : World K D V ViewData SiteData Rest)
    (cells : List (Option (Received V))) (vector : world.cells = vectorStore cells)
    (parent : Nat) (formal : K) (delay : V) (selectedView : Nat)
    (node : Node K D) (found : nodeAt world.environments parent = some node) :
    (bindRetained world parent formal delay selectedView node found).cells =
      vectorStore (cells ++ [some (packet delay selectedView)]) := by
  change world.cells.push _ = _
  rw [vector, vector_store_push]

theorem retained_all_old_cells (world : World K D V ViewData SiteData Rest)
    (cells : List (Option (Received V))) (vector : world.cells = vectorStore cells)
    (parent : Nat) (formal : K) (delay : V) (selectedView : Nat)
    (node : Node K D) (found : nodeAt world.environments parent = some node)
    (index : Nat) (previous : Received V) (present : world.cells.cell index = some previous) :
    (bindRetained world parent formal delay selectedView node found).cells.cell index = some previous := by
  have bounded : index < world.cells.size := by
    rw [vector] at present ⊢
    exact vector_some_bound cells index previous present
  change (world.cells.push _).cell index = _
  rw [push_old _ _ _ bounded]
  exact present

theorem retained_formal_lookup [DecidableEq K] (world : World K D V ViewData SiteData Rest)
    (parent : Nat) (formal : K) (delay : V) (selectedView : Nat)
    (node : Node K D) (found : nodeAt world.environments parent = some node) :
    lookupKey formal (bindRetained world parent formal delay selectedView node found).environments
      world.environments.size = some world.cells.size := parameter_shadows _ _ _ _ _

theorem retained_address_invariant (world : World K D V ViewData SiteData Rest)
    (within : AddressesWithin world.environments world.cells.size)
    (parent : Nat) (formal : K) (delay : V) (selectedView : Nat)
    (node : Node K D) (found : nodeAt world.environments parent = some node) :
    AddressesWithin (bindRetained world parent formal delay selectedView node found).environments
      (bindRetained world parent formal delay selectedView node found).cells.size :=
  addresses_parameter_bind world within parent formal (packet delay selectedView) node found

def installInterface (assignment : ViewAssignment s V) (address : Nat) (interface : s.Interface) :
    ViewAssignment s V :=
  {assignment with interface := fun index view =>
    if index = address then interface else assignment.interface index view}

theorem fresh_interface_keeps_old_readout (assignment : ViewAssignment s V)
    (store : Store (Received V)) (address : Nat) (empty : store.cell address = none)
    (interface : s.Interface) :
    bindingReadout (installInterface assignment address interface) store = bindingReadout assignment store := by
  funext index
  by_cases same : index = address
  · subst index
    simp only [bindingReadout, empty, Option.map_none]
  · cases present : store.cell index with
    | none => simp only [bindingReadout, present, Option.map_none]
    | some raw =>
        cases role : raw.interface <;>
          simp [bindingReadout, present, ViewAssignment.received, installInterface, role, same]

theorem retained_bind_readout (assignment : ViewAssignment s V)
    (world : World K D V ViewData SiteData Rest)
    (cells : List (Option (Received V))) (vector : world.cells = vectorStore cells)
    (parent : Nat) (formal : K) (delay : V) (selectedView : Nat)
    (node : Node K D) (found : nodeAt world.environments parent = some node)
    (interface : s.Interface) :
    bindingReadout (installInterface assignment world.cells.size interface)
      (bindRetained world parent formal delay selectedView node found).cells =
      extendBindings (bindingReadout assignment world.cells) world.cells.size
        (.carrier interface (assignment.carrier delay) (assignment.root delay)) := by
  change bindingReadout _ (world.cells.push _) = _
  rw [push_binding_readout]
  have empty : world.cells.cell world.cells.size = none := by
    rw [vector]
    exact vector_cell_beyond cells cells.length (Nat.le_refl _)
  rw [fresh_interface_keeps_old_readout assignment world.cells world.cells.size empty interface]
  simp only [ViewAssignment.received, packet, installInterface, ite_true]

theorem retained_capture_address [DecidableEq K]
    (world : World K D V ViewData SiteData Rest) (closure : Closure Body)
    (saved : closure.savedEnvironment < world.environments.size)
    (references : Body → Nat → Option K) (name : Nat)
    (parent : Nat) (formal : K) (delay : V) (selectedView : Nat)
    (node : Node K D) (found : nodeAt world.environments parent = some node) :
    captureAddress (bindRetained world parent formal delay selectedView node found).environments
      closure references name = captureAddress world.environments closure references name :=
  capture_address_parameter_bind world closure saved references name parent formal (packet delay selectedView) node found

theorem retained_capture_readout [DecidableEq K]
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (cells : List (Option (Received V))) (vector : world.cells = vectorStore cells)
    (within : AddressesWithin world.environments world.cells.size)
    (closure : Closure Body) (saved : closure.savedEnvironment < world.environments.size)
    (references : Body → Nat → Option K) (name : Nat)
    (parent : Nat) (formal : K) (delay : V) (selectedView : Nat)
    (node : Node K D) (found : nodeAt world.environments parent = some node)
    (interface : s.Interface) :
    captureReadout (installInterface assignment world.cells.size interface)
      (bindRetained world parent formal delay selectedView node found) closure references name =
      captureReadout assignment world closure references name := by
  unfold captureReadout
  rw [retained_capture_address world closure saved references name parent formal delay selectedView node found]
  cases resolved : captureAddress world.environments closure references name with
  | none => rfl
  | some address =>
      simp only [Option.bind_some]
      rw [retained_bind_readout assignment world cells vector parent formal delay selectedView node found interface]
      have bounded := capture_address_bound world.environments world.cells.size within closure references name address resolved
      simp only [extendBindings, ite_eq_right (Nat.ne_of_lt bounded)]

def selectedInterface (selection : Selected s View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation) : s.Interface := by
  simpa only [Contract, mode] using selection.contract

def formalInterfacePoint (parameter : Parameter) : Endpoint := ⟨parameter.formal.site, .descriptor⟩

def declareInterface (readout : RuntimeReadout s View) (initial : Decoded s View)
    (assignment : FormalAssignment s View) (parameter : Parameter) (route : Route)
    (telescope : Telescope s View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation) : Decoded s View :=
  let before := replayTelescope readout initial telescope
  before.logical ⟨[], [(formalInterfacePoint parameter,
    selectedInterface (select assignment parameter route telescope.values) mode)],
    before.viewMeaning, before.assignment.event.eta, before.assignment.event.witness⟩

theorem selected_at_original_interface (readout : RuntimeReadout s View) (initial : Decoded s View)
    (assignment : FormalAssignment s View) (parameter : Parameter) (route : Route)
    (telescope : Telescope s View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation) :
    (declareInterface readout initial assignment parameter route telescope mode).interfaces
      (parameter.coordinate route).endpoint = selectedInterface (select assignment parameter route telescope.values) mode := by
  simp [declareInterface, Decoded.logical, put, formalInterfacePoint, Parameter.coordinate]

def carrierEvidence (parameter : Parameter) (selection : Selected s View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation)
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (delay : V) (witness : s.WitnessValue) : Retained s parameter.registration :=
  retainedCarrier parameter.registration mode (assignment.carrier delay) (assignment.root delay)
    (selectedInterface selection mode) world.cells.size witness

theorem carrier_evidence_is_actual (parameter : Parameter) (selection : Selected s View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation)
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (delay : V) (witness : s.WitnessValue) :
    (carrierEvidence parameter selection mode assignment world delay witness).address = world.cells.size ∧
    (carrierEvidence parameter selection mode assignment world delay witness).data.installed =
      .carrier (selectedInterface selection mode) (assignment.carrier delay) (assignment.root delay) :=
  ⟨rfl, carrier_evidence_object parameter.registration mode _ _ _ _ _⟩

theorem retained_delivery_readout (readout : RuntimeReadout s View) (state : Decoded s View)
    (parameter : Parameter) (selection : Selected s View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation)
    (assignment : ViewAssignment s V) (world : World Name D V ViewData SiteData Rest)
    (cells : List (Option (Received V))) (vector : world.cells = vectorStore cells)
    (represented : state.installed = bindingReadout assignment world.cells)
    (parent : Nat) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt world.environments parent = some node) (witness : s.WitnessValue)
    (parents : List (EventStep (Payload s View))) (occurrence : Nat) :
    let evidence := carrierEvidence parameter selection mode assignment world delay witness
    let delivered := deliverFrame readout state parameter evidence parents occurrence
    delivered.installed = bindingReadout
      (installInterface assignment world.cells.size (selectedInterface selection mode))
      (bindRetained world parent parameter.formal.name delay selectedView node found).cells ∧
    delivered.assignment.binding parameter.formal.name = some world.cells.size ∧
    delivered.fixedFrames = state.fixedFrames ++ [evidence.frame parameter.registration parents occurrence] := by
  dsimp only
  refine ⟨?_, delivered_formal_binding _ _ _ _ _ _, rfl⟩
  rw [delivered_installed_map]
  rw [retained_bind_readout assignment world cells vector parent parameter.formal.name delay selectedView node found]
  rw [(carrier_evidence_is_actual parameter selection mode assignment world delay witness).2]
  change extendBindings state.installed world.cells.size _ = _
  rw [represented]

theorem retained_scope_has_no_return (parameter : Parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation) :
    parameter.registration.retainedOwner.telescope = parameter.registration.telescope ∧
    (entryDelivery parameter.registration).physical = parameter.registration.route ++ [0] :=
  ⟨computation_retained_below_receipt parameter.registration mode,
    retained_delivery_position parameter.registration mode⟩


/-! Fixed missing-native Inputs, with an actual retained bind snapshot. -/
def retainEvent (before : Event (NS b D V ViewData SiteData Rest Body View))
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b) :
    Event (NS b D V ViewData SiteData Rest Body View) :=
  {before with
    history := fields.history
    current := {before.current with world := bindRetained before.current.world parent formal delay selectedView node found}
    eta := ⟨fields.assignment,
      installInterface before.eta.views before.current.world.cells.size interface⟩
    witness := ⟨fields.witness, before.witness.shared⟩
    scope := fields.scope, authority := fields.authority,
    incidence := fields.incidence, dictionary := fields.dictionary}

theorem retain_keeps_static_fiber (before : Event (NS b D V ViewData SiteData Rest Body View))
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b) :
    (retainEvent before parent formal delay selectedView node found interface fields).fiber = before.fiber ∧
    (retainEvent before parent formal delay selectedView node found interface fields).eta0 = before.eta0 := ⟨rfl, rfl⟩

theorem retain_current_fields (before : Event (NS b D V ViewData SiteData Rest Body View))
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b) :
    (retainEvent before parent formal delay selectedView node found interface fields).witness.current = fields.witness ∧
    (retainEvent before parent formal delay selectedView node found interface fields).eta.original = fields.assignment := ⟨rfl, rfl⟩

theorem retain_uses_current_history (before : Event (NS b D V ViewData SiteData Rest Body View))
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b) :
    (retainEvent before parent formal delay selectedView node found interface fields).history = fields.history ∧
    (retainEvent before parent formal delay selectedView node found interface fields).current.residual = before.current.residual :=
  ⟨rfl, rfl⟩

theorem retain_existing_shared (before : Event (NS b D V ViewData SiteData Rest Body View))
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b) (position : SharedPosition b View) :
    (retainEvent before parent formal delay selectedView node found interface fields).witness.shared position =
      before.witness.shared position := rfl

theorem retain_installed (before : Event (NS b D V ViewData SiteData Rest Body View))
    (cells : List (Option (Received V))) (vector : before.current.world.cells = vectorStore cells)
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b) :
    installed (retainEvent before parent formal delay selectedView node found interface fields) =
      extendBindings (installed before) before.current.world.cells.size
        (.carrier interface (before.eta.views.carrier delay) (before.eta.views.root delay)) := by
  change bindingReadout (installInterface (viewAssignment before.eta) before.current.world.cells.size interface)
    (bindRetained before.current.world parent formal delay selectedView node found).cells = _
  exact retained_bind_readout (viewAssignment before.eta) before.current.world cells vector
    parent formal delay selectedView node found interface

theorem retain_old_installed (before : Event (NS b D V ViewData SiteData Rest Body View))
    (cells : List (Option (Received V))) (vector : before.current.world.cells = vectorStore cells)
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b)
    (index : Nat) (object : Installed (NS b D V ViewData SiteData Rest Body View))
    (present : installed before index = some object) :
    installed (retainEvent before parent formal delay selectedView node found interface fields) index = some object := by
  rw [retain_installed before cells vector parent formal delay selectedView node found interface fields]
  apply extend_bindings_old _ present
  unfold installed bindingReadout
  rw [vector]
  rw [show (vectorStore cells).cell (vectorStore cells).size = none from
    vector_cell_beyond cells cells.length (Nat.le_refl _)]
  rfl

theorem retain_capture_address (references : Body → Nat → Option Name)
    (before : Event (NS b D V ViewData SiteData Rest Body View))
    (saved : ∀ provider closure, before.current.providers provider = some closure →
      closure.savedEnvironment < before.current.world.environments.size)
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b) (provider : b.Provider) (name : Nat) :
    captureAt references (retainEvent before parent formal delay selectedView node found interface fields) provider name =
      captureAt references before provider name := by
  unfold captureAt
  change (before.current.providers provider).bind _ = _
  cases present : before.current.providers provider with
  | none => rfl
  | some closure =>
      exact retained_capture_address before.current.world closure
        (saved provider closure present) references name parent formal delay selectedView node found

theorem retain_aliases (before : Event (NS b D V ViewData SiteData Rest Body View))
    (saved : ∀ reference ∈ before.current.aliases,
      reference.environment < before.current.world.environments.size)
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b) (first second : Nat) :
    aliasAt (retainEvent before parent formal delay selectedView node found interface fields) first second ↔
      aliasAt before first second := by
  unfold aliasAt
  change (∃ reference ∈ before.current.aliases, _ ∧ _) ↔ _
  apply exists_congr
  intro reference
  apply and_congr_right
  intro registered
  simp only [retainEvent, bindRetained, extendNode, lookupKey]
  rw [lookup_old _ _ _ _ _ _ (saved reference registered),
    lookup_old _ _ _ _ _ _ (saved reference registered)]

/-- Full PhiW for the computed constructor. The prior world clause and
actual retained carrier are recursive premises; no post-world or registry
commutation equation is a premise. Old values/carriers are transported at
their actual unchanged descriptors by the given candidate restriction action. -/
theorem retain_phiW
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
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b)
    (coherent : base.eventCoherent (retainEvent before parent formal delay selectedView node found interface fields))
    (guards : (base.worldGuards (retainEvent before parent formal delay selectedView node found interface fields)).Valid)
    (restrict : ∀ object : Installed (NS b D V ViewData SiteData Rest Body View), object.Valid candidate before →
      object.Valid candidate (retainEvent before parent formal delay selectedView node found interface fields))
    (retained : candidate (.carrier ⟨interface, before.eta.views.carrier delay,
      before.eta.views.root delay, retainEvent before parent formal delay selectedView node found interface fields⟩)) :
    PhiW (inputs base references) candidate (retainEvent before parent formal delay selectedView node found interface fields) := by
  let after := retainEvent before parent formal delay selectedView node found interface fields
  refine ⟨coherent, guards, ?_, ?_, ?_, ?_⟩
  · intro first second same
    have previous : aliasAt before first second :=
      (retain_aliases before savedAliases parent formal delay selectedView node found interface fields first second).mp same
    obtain ⟨object, firstFound, secondFound⟩ := old.2.2.1 first second previous
    exact ⟨object,
      retain_old_installed before cells vector parent formal delay selectedView node found interface fields first object firstFound,
      retain_old_installed before cells vector parent formal delay selectedView node found interface fields second object secondFound⟩
  · intro provider name address captured
    change captureAt references after provider name = some address at captured
    have previous : captureAt references before provider name = some address := by
      rw [← retain_capture_address references before savedProviders parent formal delay selectedView node found interface fields provider name]
      exact captured
    obtain ⟨bounded, object, present, _⟩ := old.2.2.2.1 provider name address previous
    have current := retain_old_installed before cells vector parent formal delay selectedView node found interface fields
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
    rw [retain_installed before cells vector parent formal delay selectedView node found interface fields] at present
    unfold extendBindings at present
    split at present
    · cases Option.some.inj present
      exact retained
    · exact restrict object (old.2.2.2.2.2 index object present)


/-- The whole carrier certificate already includes this current world's
meaning. No execution, Force or Return is needed to obtain it. -/
theorem carrier_meaning_current_world (operator : Inputs s) (row : CarrierRow s)
    (certificate : Meaning operator (.carrier row)) : Meaning operator (.world row.event) := by
  have clause := greatest_unfold (Phi operator) (phi_monotone operator) (.carrier row) certificate
  exact clause.2.2.1

theorem carrier_background_current_world (operator : Inputs s) (holes : ValueRow s → Prop)
    (row : CarrierRow s) (certificate : Background operator holes (.carrier row)) :
    Background operator holes (.world row.event) := by
  have clause := greatest_unfold (RelativePhi operator holes) (relative_monotone operator holes)
    (.carrier row) certificate
  rcases clause with actual | impossible
  · exact actual.2.2.1
  · cases impossible

/-- The semantic consumer needs the actual unchanged carrier at the chosen
formal Interface. It derives the prior world and the fresh carrier field
from that single certificate, rather than assuming either post-bind fact. -/
theorem retained_meaning_world
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (before : Event (NS b D V ViewData SiteData Rest Body View))
    (cells : List (Option (Received V))) (vector : before.current.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, before.current.providers provider = some closure →
      closure.savedEnvironment < before.current.world.environments.size)
    (savedAliases : ∀ reference ∈ before.current.aliases,
      reference.environment < before.current.world.environments.size)
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b)
    (later : base.compatible before (retainEvent before parent formal delay selectedView node found interface fields))
    (coherent : base.eventCoherent (retainEvent before parent formal delay selectedView node found interface fields))
    (guards : (base.worldGuards (retainEvent before parent formal delay selectedView node found interface fields)).Valid)
    (carrier : Meaning (inputs base references) (.carrier ⟨interface, before.eta.views.carrier delay,
      before.eta.views.root delay, before⟩)) :
    Meaning (inputs base references)
      (.world (retainEvent before parent formal delay selectedView node found interface fields)) := by
  let operator := inputs base references
  have old := carrier_meaning_current_world operator _ carrier
  have oldClause := greatest_unfold (Phi operator) (phi_monotone operator) (.world before) old
  apply greatest_fold (Phi operator) (phi_monotone operator)
  apply retain_phiW base references (Meaning operator) before oldClause cells vector
    savedProviders savedAliases parent formal delay selectedView node found interface fields coherent guards
  · intro object member
    exact meaning_installed_restrict operator object before _ member later
  · exact meaning_installed_restrict operator
      (.carrier interface (before.eta.views.carrier delay) (before.eta.views.root delay))
      before _ carrier later

/-- B_H uses its own hereditary action. Carrier rows cannot be discharged by
a Value hole, and no completed checking theorem is used as a B_H inclusion. -/
theorem retained_background_world
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (holes : ValueRow (NS b D V ViewData SiteData Rest Body View) → Prop)
    (holeFuture : ∀ row later, holes row → base.compatible row.event later → holes (row.atEvent later))
    (before : Event (NS b D V ViewData SiteData Rest Body View))
    (cells : List (Option (Received V))) (vector : before.current.world.cells = vectorStore cells)
    (savedProviders : ∀ provider closure, before.current.providers provider = some closure →
      closure.savedEnvironment < before.current.world.environments.size)
    (savedAliases : ∀ reference ∈ before.current.aliases,
      reference.environment < before.current.world.environments.size)
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b)
    (later : base.compatible before (retainEvent before parent formal delay selectedView node found interface fields))
    (coherent : base.eventCoherent (retainEvent before parent formal delay selectedView node found interface fields))
    (guards : (base.worldGuards (retainEvent before parent formal delay selectedView node found interface fields)).Valid)
    (carrier : Background (inputs base references) holes (.carrier ⟨interface, before.eta.views.carrier delay,
      before.eta.views.root delay, before⟩)) :
    Background (inputs base references) holes
      (.world (retainEvent before parent formal delay selectedView node found interface fields)) := by
  let operator := inputs base references
  have old := carrier_background_current_world operator holes _ carrier
  have opened := greatest_unfold (RelativePhi operator holes) (relative_monotone operator holes)
    (.world before) old
  rcases opened with oldClause | impossible
  · apply greatest_fold (RelativePhi operator holes) (relative_monotone operator holes)
    apply Or.inl
    apply retain_phiW base references (Background operator holes) before oldClause cells vector
      savedProviders savedAliases parent formal delay selectedView node found interface fields coherent guards
    · intro object member
      exact background_installed_restrict operator holes holeFuture object before _ member later
    · exact background_installed_restrict operator holes holeFuture
        (.carrier interface (before.eta.views.carrier delay) (before.eta.views.root delay))
        before _ carrier later
  · cases impossible


/-! The actual formal Description frame reads the Interface namespace at
its original endpoint. This does not equate that endpoint to an opaque
actual-call inlet or prove the runtime receiving.enter correspondence. -/
def interfaceDescriptionFrame (readout : RuntimeReadout s View) (initial : Decoded s View)
    (assignment : FormalAssignment s View) (parameter : Parameter) (route : Route)
    (telescope : Telescope s View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation)
    (actual : ActualEvent (Payload s View)) (entryPath : List (EventStep (Payload s View))) :
    Frame (Payload s View) :=
  let before := replayTelescope readout initial telescope
  ⟨⟨parameter.formal.site, .description, 0⟩,
    ⟨.logical .description
      ⟨[], [(formalInterfacePoint parameter,
        selectedInterface (select assignment parameter route telescope.values) mode)],
        before.viewMeaning, before.assignment.event.eta, before.assignment.event.witness⟩,
      actual⟩, entryPath⟩

theorem decode_interface_description (readout : RuntimeReadout s View) (initial : Decoded s View)
    (assignment : FormalAssignment s View) (parameter : Parameter) (route : Route)
    (telescope : Telescope s View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation)
    (actual : ActualEvent (Payload s View)) (entryPath : List (EventStep (Payload s View))) :
    decodeFrame readout (replayTelescope readout initial telescope)
      (interfaceDescriptionFrame readout initial assignment parameter route telescope mode actual entryPath) =
      declareInterface readout initial assignment parameter route telescope mode ∧
    (interfaceDescriptionFrame readout initial assignment parameter route telescope mode actual entryPath).value.event = actual ∧
    (interfaceDescriptionFrame readout initial assignment parameter route telescope mode actual entryPath).entryPath = entryPath :=
  ⟨rfl, rfl, rfl⟩

/-- Complete native operands are retained in addition to the complete
original raw receipt key. Neither chosen Interface nor EventProof is a raw
field. Retaining delay prevents a noninjective carrier interpretation from
collapsing two native inputs. -/
structure NativeReceiptKey (s : Sorts) (V : Type) where
  original : RawKey s Nat
  delay : V
  parent : Nat
  selectedView : Nat

def nativeReceiptKey (parameter : Parameter) (route : Route) (receipt : ReceiptData s Nat)
    (delay : V) (parent : Nat) (parents : List (RawStep s Nat)) (occurrence : Nat) : NativeReceiptKey s V :=
  ⟨⟨parents, ⟨parameter.declaration, route ++ [0, 0, 0, 0],
      ⟨parameter.formal.site, .receipt, 0⟩, occurrence, .direct (.receipt receipt)⟩⟩,
    delay, parent, receipt.view⟩

theorem native_receipt_keeps_all_operands (parameter : Parameter) (route : Route)
    (receipt : ReceiptData s Nat) (delay : V) (parent : Nat)
    (parents : List (RawStep s Nat)) (occurrence : Nat) :
    (nativeReceiptKey parameter route receipt delay parent parents occurrence).original.parents = parents ∧
    (nativeReceiptKey parameter route receipt delay parent parents occurrence).original.current.action =
      .direct (.receipt receipt) ∧
    (nativeReceiptKey parameter route receipt delay parent parents occurrence).delay = delay ∧
    (nativeReceiptKey parameter route receipt delay parent parents occurrence).parent = parent ∧
    (nativeReceiptKey parameter route receipt delay parent parents occurrence).selectedView = receipt.view :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem receipt_owner_is_source_generated (parameter : Parameter) :
    ((sourceOwners parameter.context parameter.source).drop 1).head? =
      some (owner [0, 0, 0, 0]
        [⟨[], ⟨parameter.formal.site, .description, 0⟩⟩,
         ⟨[0], ⟨parameter.lambdaSite, .viewLogic, 0⟩⟩,
         ⟨[0, 0, 0], ⟨parameter.lambdaSite, .invocation, 0⟩⟩]
        ⟨parameter.formal.site, .receipt, 0⟩ .actualEvent) :=
  source_lambda_receipt parameter.context parameter.lambdaSite parameter.formal parameter.pattern parameter.body

/-- A retained strategy argument keeps the full typed local Lambda prefix,
the complete raw receipt and native bind operands. This is a local root-Lambda
supplier; no fabricated global outer-telescope correspondence is asserted. -/
structure CarrierPosition (s : Sorts) (V : Type) where
  parameter : Parameter
  selection : Selected s Nat parameter
  source : SharedPosition s Nat
  native : NativeReceiptKey s V

def carrierPosition (parameter : Parameter) (selection : Selected s Nat parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation)
    (description view : Logical s Nat) (invocation : Invocation s Nat) (receipt : ReceiptData s Nat)
    (delay : V) (parent : Nat) (parents : List (RawStep s Nat)) (occurrence : Nat) : CarrierPosition s V :=
  let native := nativeReceiptKey parameter selection.outerRoute receipt delay parent parents occurrence
  ⟨parameter, selection, retainedPosition parameter selection
    (carrierPrefix parameter.registration mode
      (lambdaPrefix parameter.context parameter.lambdaSite parameter.formal parameter.pattern parameter.body
        description view invocation receipt)) native.original, native⟩

theorem carrier_position_keeps_entire_formal_scope
    (parameter : Parameter) (selection : Selected s Nat parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation)
    (description view : Logical s Nat) (invocation : Invocation s Nat) (receipt : ReceiptData s Nat)
    (delay : V) (parent : Nat) (parents : List (RawStep s Nat)) (occurrence : Nat) :
    (carrierPosition parameter selection mode description view invocation receipt delay parent parents occurrence).parameter =
      parameter ∧
    (carrierPosition parameter selection mode description view invocation receipt delay parent parents occurrence).selection.prior =
      selection.prior ∧
    (carrierPosition parameter selection mode description view invocation receipt delay parent parents occurrence).selection.contract =
      selection.contract := ⟨rfl, rfl, rfl⟩

abbrev CarrierAssignment (s : Sorts) (V : Type) := CarrierPosition s V → s.WitnessValue

def scopedCarrierEvidence (shared : CarrierAssignment s V) (parameter : Parameter)
    (selection : Selected s Nat parameter) (mode : parameter.formal.entry = OriginalSource.Entry.computation)
    (description view : Logical s Nat) (invocation : Invocation s Nat) (receipt : ReceiptData s Nat)
    (assignment : ViewAssignment s V) (world : World Name D V ViewData SiteData Rest)
    (delay : V) (parent : Nat) (parents : List (RawStep s Nat)) (occurrence : Nat) :
    Retained s parameter.registration :=
  carrierEvidence parameter selection mode assignment world delay
    (shared (carrierPosition parameter selection mode description view invocation receipt delay parent parents occurrence))

/-- One source-selected contract, one source-scoped Shared application, one
actual cell allocation, and one decoder delivery. The representation of the
previous decoder is an induction invariant, not an output commutation law. -/
theorem source_scoped_retained_delivery
    (formalAssignment : FormalAssignment s Nat) (shared : CarrierAssignment s V)
    (parameter : Parameter) (route : Route) (prior : ScopeValues s Nat parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation)
    (description view : Logical s Nat) (invocation : Invocation s Nat) (receipt : ReceiptData s Nat)
    (readout : RuntimeReadout s Nat) (state : Decoded s Nat)
    (assignment : ViewAssignment s V) (world : World Name D V ViewData SiteData Rest)
    (cells : List (Option (Received V))) (vector : world.cells = vectorStore cells)
    (represented : state.installed = bindingReadout assignment world.cells)
    (parent : Nat) (delay : V) (node : Node Name D) (found : nodeAt world.environments parent = some node)
    (parents : List (RawStep s Nat)) (rawOccurrence sharedOccurrence : Nat) :
    let selection := select formalAssignment parameter route prior
    let actual := nativeReceiptKey parameter route receipt delay parent parents rawOccurrence
    let evidence := scopedCarrierEvidence shared parameter selection mode description view invocation receipt
      assignment world delay parent parents rawOccurrence
    let delivered := deliverFrame readout state parameter evidence actual.original.erasedPath sharedOccurrence
    parameter.generate.deliveries = [entryDelivery parameter.registration] ∧
    delivered.installed = bindingReadout
      (installInterface assignment world.cells.size (selectedInterface selection mode))
      (bindRetained world parent parameter.formal.name delay receipt.view node found).cells ∧
    delivered.assignment.binding parameter.formal.name = some world.cells.size ∧
    delivered.fixedFrames = state.fixedFrames ++
      [evidence.frame parameter.registration actual.original.erasedPath sharedOccurrence] := by
  dsimp only
  refine ⟨generated_parameter_delivery parameter, ?_⟩
  exact retained_delivery_readout readout state parameter _ mode assignment world cells vector represented
    parent delay receipt.view node found _ _ sharedOccurrence

/-- Original invocation-to-native carrier readback is an explicit local data
boundary. When that genuine equality is supplied, the computed Shared is
exactly the invocation's carrier/root at the preselected formal Interface. -/
theorem invocation_readback_retained_object
    (parameter : Parameter) (selection : Selected s View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation)
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (delay : V) (invocation : Invocation s View) (witness : s.WitnessValue)
    (carrierReadback : assignment.carrier delay = invocation.carrier)
    (rootReadback : assignment.root delay = invocation.carrierRoot) :
    (carrierEvidence parameter selection mode assignment world delay witness).data.installed =
      .carrier (selectedInterface selection mode) invocation.carrier invocation.carrierRoot := by
  rw [(carrier_evidence_is_actual parameter selection mode assignment world delay witness).2,
    carrierReadback, rootReadback]

/-- The selected Interface exists before the receipt. It is not selected by
the carrier, native cell, receipt view, or its future observations. -/
theorem selected_interface_before_receipt (assignment : FormalAssignment s View)
    (parameter : Parameter) (route : Route) (prior : ScopeValues s View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation)
    (_first _second : ReceiptData s View) :
    selectedInterface (select assignment parameter route prior) mode =
      selectedInterface ⟨route, prior, assignment parameter route prior⟩ mode := rfl

/-- This direct native projection includes actual receipt insertion after any
receiving.enter view construction, then exactly the plain retained bind.
The RootComp view-allocation and SourceSite/HIR-id projection remain separate. -/
def afterReceipt (world : World Name D V ViewData Site Rest) (activation : Nat)
    (selectedView : Nat) (parameter : Parameter) : World Name D V ViewData Site Rest :=
  {world with
    receiving := world.receiving.record (.invocation activation)
      selectedView parameter.lambdaSite (some parameter.formal.name)}

theorem actual_receipt_then_plain_bind
    (world : World Name D V ViewData Site Rest) (activation : Nat)
    (parameter : Parameter) (parent : Nat) (delay : V) (selectedView : Nat)
    (node : Node Name D) (found : nodeAt world.environments parent = some node) :
    let received := afterReceipt world activation selectedView parameter
    let bound := bindRetained received parent parameter.formal.name delay selectedView node found
    bound.receiving.receipts.cell world.receiving.receipts.size =
      some ⟨.invocation activation, selectedView, parameter.lambdaSite, some parameter.formal.name⟩ ∧
    bound.receiving.index (.invocation activation, selectedView, some parameter.formal.name) =
      some world.receiving.receipts.size ∧
    bound.cells.cell world.cells.size = some (packet delay selectedView) ∧
    bound.control = world.control ∧ bound.rest = world.rest := by
  dsimp only
  exact ⟨receipt_new _ _ _ _ _, receipt_index _ _ _ _ _, push_current _ _, rfl, rfl⟩

/-! Concrete discriminators. No semantic membership is inferred merely from
these raw operational data or from equality of native view tokens. -/
namespace Discriminator
open OriginalWorldReadout.Discriminator

def retained : World Nat Nat Nat Unit Nat Nat :=
  bindRetained world 1 7 20 2 ⟨some 0, some (7, 0), 11⟩ (by rfl)

theorem nonlatest_capture_and_retained_shadow :
    closure.savedEnvironment < world.environments.size - 1 ∧
    captureAddress retained.environments closure references 0 = some 0 ∧
    lookupKey (7 : Nat) retained.environments world.environments.size = some 2 ∧
    retained.cells.cell 0 = some first ∧ retained.cells.cell 2 = some ⟨20, .computation, 2, none⟩ :=
  ⟨by decide, rfl, rfl, rfl, rfl⟩

theorem selected_parent_and_receiving :
    (nodeAt retained.environments world.environments.size).map Node.dispatch = some 11 ∧
    retained.receiving = world.receiving ∧ retained.rest = 47 := ⟨rfl, rfl, rfl⟩

theorem retained_is_not_value_entry :
    retained.cells.cell 2 ≠ (bindValue world 1 7 (packet 20 2)
      ⟨some 0, some (7, 0), 11⟩ (by rfl)).cells.cell 2 := by
  intro same
  have records := Option.some.inj same
  have roles := congrArg Received.interface records
  cases roles

theorem captured_contract_survives_new_interface (assignment : ViewAssignment s Nat) (interface : s.Interface) :
    captureReadout (installInterface assignment 2 interface) retained closure references 0 =
      some (assignment.received 0 first) := rfl

theorem same_view_separate_carrier_contracts (assignment : ViewAssignment s Nat)
    (different : assignment.interface 0 2 ≠ assignment.interface 1 2) :
    bindingReadout assignment (vectorStore [some (packet 20 2), some (packet 20 2)]) 0 ≠
      bindingReadout assignment (vectorStore [some (packet 20 2), some (packet 20 2)]) 1 := by
  intro same
  exact different (Installed.carrier.inj (Option.some.inj same)).1

end Discriminator

theorem retained_changed_current_keeps_old_shared
    (before : Event (NS b D V ViewData SiteData Rest Body View))
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b)
    (different : fields.witness ≠ before.witness.current) (position : SharedPosition b View) :
    (retainEvent before parent formal delay selectedView node found interface fields).witness.current ≠ before.witness.current ∧
    (retainEvent before parent formal delay selectedView node found interface fields).witness.shared position =
      before.witness.shared position := ⟨different, rfl⟩

theorem native_delays_not_erased (parameter : Parameter) (route : Route)
    (receipt : ReceiptData s Nat) (first second : V) (different : first ≠ second)
    (parent : Nat) (parents : List (RawStep s Nat)) (occurrence : Nat) :
    nativeReceiptKey parameter route receipt first parent parents occurrence ≠
      nativeReceiptKey parameter route receipt second parent parents occurrence := by
  intro same
  exact different (congrArg NativeReceiptKey.delay same)


/-- Application at the constructed original formal Description endpoint.
The only semantic entry premise is the whole carrier at that fixed formal
Interface. Authentic actual-call inlet/receipt readback is not inferred by
identifying names of two different ports. -/
theorem source_formal_retained_meaning
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (readout : RuntimeReadout (NS b D V ViewData SiteData Rest Body View) View)
    (initial : Decoded (NS b D V ViewData SiteData Rest Body View) View)
    (assignment : FormalAssignment (NS b D V ViewData SiteData Rest Body View) View)
    (parameter : Parameter) (route : Route)
    (telescope : Telescope (NS b D V ViewData SiteData Rest Body View) View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation) :
    let declaration := declareInterface readout initial assignment parameter route telescope mode
    let before := declaration.assignment.event
    let interface := selectedInterface (select assignment parameter route telescope.values) mode
    ∀ (cells : List (Option (Received V))) (_vector : before.current.world.cells = vectorStore cells)
      (_savedProviders : ∀ provider closure, before.current.providers provider = some closure →
        closure.savedEnvironment < before.current.world.environments.size)
      (_savedAliases : ∀ reference ∈ before.current.aliases,
        reference.environment < before.current.world.environments.size)
      (parent : Nat) (delay : V) (selectedView : Nat) (node : Node Name D)
      (found : nodeAt before.current.world.environments parent = some node) (fields : EventFields b),
      base.compatible before (retainEvent before parent parameter.formal.name delay selectedView node found interface fields) →
      base.eventCoherent (retainEvent before parent parameter.formal.name delay selectedView node found interface fields) →
      (base.worldGuards (retainEvent before parent parameter.formal.name delay selectedView node found interface fields)).Valid →
      Meaning (inputs base references) (.carrier ⟨declaration.interfaces (parameter.coordinate route).endpoint,
        before.eta.views.carrier delay, before.eta.views.root delay, before⟩) →
      declaration.interfaces (parameter.coordinate route).endpoint = interface ∧
      telescope.frames.map Frame.binder = parameter.ambient.map ScopeEntry.binder ∧
      Meaning (inputs base references)
        (.world (retainEvent before parent parameter.formal.name delay selectedView node found interface fields)) := by
  dsimp only
  intro cells vector savedProviders savedAliases parent delay selectedView node found fields later coherent guards carrier
  have chosen := selected_at_original_interface readout initial assignment parameter route telescope mode
  rw [chosen] at carrier
  exact ⟨chosen, telescope_keeps_binders telescope,
    retained_meaning_world base references _ cells vector savedProviders savedAliases
      parent parameter.formal.name delay selectedView node found _ fields later coherent guards carrier⟩

/-- The decoder and fixed native Inputs consume exactly the same carrier
entry and address. The source decoder's Shared action alone keeps its Event
unchanged; this theorem states that boundary rather than re-rooting it. -/
theorem retained_decoder_matches_native_inputs
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (readout : RuntimeReadout (NS b D V ViewData SiteData Rest Body View) View)
    (state : Decoded (NS b D V ViewData SiteData Rest Body View) View)
    (parameter : Parameter) (selection : Selected (NS b D V ViewData SiteData Rest Body View) View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.computation)
    (cells : List (Option (Received V))) (vector : state.assignment.event.current.world.cells = vectorStore cells)
    (represented : state.installed = (inputs base references).installed state.assignment.event)
    (parent : Nat) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt state.assignment.event.current.world.environments parent = some node)
    (fields : EventFields b) (witness : b.WitnessValue)
    (parents : List (EventStep (Payload (NS b D V ViewData SiteData Rest Body View) View))) (occurrence : Nat) :
    let before := state.assignment.event
    let evidence := carrierEvidence parameter selection mode (viewAssignment before.eta) before.current.world delay witness
    let delivered := deliverFrame readout state parameter evidence parents occurrence
    delivered.installed = (inputs base references).installed
      (retainEvent before parent parameter.formal.name delay selectedView node found (selectedInterface (s := NS b D V ViewData SiteData Rest Body View) selection mode) fields) ∧
    delivered.assignment.event = before ∧
    delivered.assignment.binding parameter.formal.name = some before.current.world.cells.size := by
  dsimp only
  have complete := retained_delivery_readout readout state parameter selection mode
    (viewAssignment state.assignment.event.eta) state.assignment.event.current.world cells vector represented
    parent delay selectedView node found witness parents occurrence
  exact ⟨complete.1, rfl, complete.2.1⟩

theorem retain_capture_value
    (base : Inputs (NS b D V ViewData SiteData Rest Body View))
    (references : Body → Nat → Option Name)
    (before : Event (NS b D V ViewData SiteData Rest Body View))
    (within : AddressesWithin before.current.world.environments before.current.world.cells.size)
    (cells : List (Option (Received V))) (vector : before.current.world.cells = vectorStore cells)
    (saved : ∀ provider closure, before.current.providers provider = some closure →
      closure.savedEnvironment < before.current.world.environments.size)
    (parent : Nat) (formal : Name) (delay : V) (selectedView : Nat) (node : Node Name D)
    (found : nodeAt before.current.world.environments parent = some node)
    (interface : b.Interface) (fields : EventFields b) (provider : b.Provider) (name : Nat) :
    (inputs base references).captureValue (retainEvent before parent formal delay selectedView node found interface fields)
      provider name = (inputs base references).captureValue before provider name := by
  change ((before.current.providers provider).bind _).bind _ =
    ((before.current.providers provider).bind _).bind _
  cases present : before.current.providers provider with
  | none => rfl
  | some closure =>
      exact retained_capture_readout (viewAssignment before.eta) before.current.world cells vector within
        closure (saved provider closure present) references name parent formal delay selectedView node found interface


/-- Different checked Interfaces do not create different native binds or
receipts. They do give different decorated carrier rows at the same cell. -/
theorem one_native_bind_two_interfaces
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (parent : Nat) (formal : K) (delay : V) (selectedView : Nat) (node : Node K D)
    (found : nodeAt world.environments parent = some node)
    (first second : s.Interface) (different : first ≠ second) :
    bindingReadout (installInterface assignment world.cells.size first)
      (bindRetained world parent formal delay selectedView node found).cells world.cells.size ≠
    bindingReadout (installInterface assignment world.cells.size second)
      (bindRetained world parent formal delay selectedView node found).cells world.cells.size := by
  intro same
  simp only [bindingReadout, stored_carrier_record, Option.map_some,
    ViewAssignment.received, installInterface, ite_true] at same
  have records := Option.some.inj same
  exact different (Installed.carrier.inj records).1

theorem receipt_parents_not_erased (parameter : Parameter) (route : Route)
    (receipt : ReceiptData s Nat) (delay : V) (parent : Nat)
    (first second : List (RawStep s Nat)) (different : first ≠ second) (occurrence : Nat) :
    nativeReceiptKey parameter route receipt delay parent first occurrence ≠
      nativeReceiptKey parameter route receipt delay parent second occurrence := by
  intro same
  exact different (congrArg (fun key => key.original.parents) same)

/-- Proof-use sidecars do not become raw ownership keys. Preceding typed
scope fields remain in CarrierPosition and may genuinely affect Shared. -/
structure DescribedCarrier (s : Sorts) (V Proof : Type) where
  actual : CarrierPosition s V
  proof : Proof

def describedCarrierWitness (assignment : CarrierAssignment s V)
    (description : DescribedCarrier s V Proof) : s.WitnessValue := assignment description.actual

theorem two_proof_uses_same_retained (assignment : CarrierAssignment s V)
    (actual : CarrierPosition s V) (first second : Proof) :
    describedCarrierWitness assignment ⟨actual, first⟩ =
      describedCarrierWitness assignment ⟨actual, second⟩ := rfl

end YulangClosure.OriginalRetainedParameter
