import YulangClosure.OriginalWorldReadout
import YulangClosure.OriginalSourceEvents
import YulangClosure.OriginalCheckingAdmission

/-!
Owned parameter contracts and actual formal Shared delivery.

SG §3.3 fixes the ordinary formal descriptor before invocation. The original
source builder now emits the formal Shared delivery. Parameter.generate
retains that exact source tree and records its existing physical occurrence.
The older additive transformer remains a separate helper and is not applied
by Parameter.generate. Raw history and typed assignments remain separate.
-/
namespace YulangClosure.OriginalParameterWorld

open OriginalSource OriginalSourceInterpretation OriginalSourceEnvironment
open OriginalSourceEvents OriginalWorldReadout OriginalRecursivePair

/-- An original declaration and its source introduction, not a globally
fresh Site or a checked description. -/
structure Coordinate where
  declaration : Declaration
  introduction : Route
  endpoint : Endpoint
  deriving DecidableEq, Repr

/-- The exact raw Lambda/formal constructor. Its source is computed rather
than supplied as a successful typing derivation. -/
structure Parameter where
  declaration : Declaration
  ambient : List ScopeEntry
  context : Context
  lambdaSite : Site
  formal : Formal
  pattern : Source .pattern
  body : Source .expression

def Parameter.source (parameter : Parameter) : Source .expression :=
  .lambda ⟨parameter.lambdaSite, none⟩ parameter.formal parameter.pattern parameter.body

def Parameter.registration (parameter : Parameter) : EntryRegistration :=
  lambdaEntry parameter.context parameter.lambdaSite parameter.formal parameter.pattern parameter.body

/-- The Parameter description is the first source binder, above invocation.
The externally supplied outerRoute is the actual containing declaration route. -/
def Parameter.coordinate (parameter : Parameter) (outerRoute : Route) : Coordinate :=
  ⟨parameter.declaration, outerRoute, ⟨parameter.formal.site, .descriptor⟩⟩

def Parameter.typeScope (parameter : Parameter) : List ScopeEntry := parameter.ambient

/-- A contract assignment reads only the original pre-invocation telescope.
No actual invocation, returned value, cell, or result proof is an argument. -/
def Contract (s : Sorts) : Entry → Type
  | .value => s.Descriptor
  | .computation => s.Interface

abbrev FormalAssignment (s : Sorts) (View : Type) :=
  (parameter : Parameter) → Route → ScopeValues s View parameter.typeScope →
    Contract s parameter.formal.entry

structure Selected (s : Sorts) (View : Type) (parameter : Parameter) where
  outerRoute : Route
  prior : ScopeValues s View parameter.typeScope
  contract : Contract s parameter.formal.entry

def select (assignment : FormalAssignment s View) (parameter : Parameter)
    (outerRoute : Route) (prior : ScopeValues s View parameter.typeScope) : Selected s View parameter :=
  ⟨outerRoute, prior, assignment parameter outerRoute prior⟩

theorem selected_before_invocation (assignment : FormalAssignment s View) (parameter : Parameter)
    (outerRoute : Route) (prior : ScopeValues s View parameter.typeScope)
    (_first _second : Invocation s View) :
    (select assignment parameter outerRoute prior).contract = assignment parameter outerRoute prior := rfl

theorem formal_annotation_and_entry (parameter : Parameter) :
    parameter.registration.role.annotation = parameter.formal.annotation ∧
    parameter.registration.entry = parameter.formal.entry := ⟨rfl, rfl⟩

theorem parameter_registered (parameter : Parameter) :
    (sourceEntries parameter.context parameter.source).head? = some parameter.registration :=
  source_lambda_entry parameter.context parameter.lambdaSite parameter.formal parameter.pattern parameter.body

/-- The inherited source telescope remains an explicit input of the original
Parameter introduction. It is not replaced by an empty pre-call scope. -/
theorem original_type_scope_kept (parameter : Parameter) :
    parameter.typeScope = parameter.ambient := rfl

theorem repeated_sites_separate_coordinates (parameter : Parameter) (first second : Route)
    (different : first ≠ second) : parameter.coordinate first ≠ parameter.coordinate second := by
  intro same
  exact different (congrArg Coordinate.introduction same)

theorem distinct_declarations_separate_coordinates (parameter : Parameter) (other : Declaration)
    (different : parameter.declaration ≠ other) (outerRoute : Route) :
    parameter.coordinate outerRoute ≠ ({parameter with declaration := other}).coordinate outerRoute := by
  intro same
  exact different (congrArg Coordinate.declaration same)

/-- The original retained owner is virtual metadata at tag 2. Its generated
physical position is separately computed, never identified with that tag. -/
def deliveryPosition (entry : EntryRegistration) : Route :=
  entry.route ++ match entry.entry with
    | .value => [0, 0]
    | .computation => [0]

structure Delivery where
  original : Owner
  physical : Route
  deriving DecidableEq, Repr

def entryDelivery (entry : EntryRegistration) : Delivery :=
  ⟨entry.retainedOwner, deliveryPosition entry⟩

theorem value_delivery_position (entry : EntryRegistration) (mode : entry.entry = .value) :
    (entryDelivery entry).physical = entry.route ++ [0, 0] := by
  simp only [entryDelivery, deliveryPosition, mode]

theorem retained_delivery_position (entry : EntryRegistration) (mode : entry.entry = .computation) :
    (entryDelivery entry).physical = entry.route ++ [0] := by
  simp only [entryDelivery, deliveryPosition, mode]

theorem delivery_owner_not_physical (entry : EntryRegistration) :
    (entryDelivery entry).original.route ≠ (entryDelivery entry).physical := by
  simp only [entryDelivery, EntryRegistration.retainedOwner, owner, deliveryPosition]
  cases entry.entry <;> simp

/-- Annotating stores the original whole program and original root route.
Generation traverses THIS tree; it never re-walks its inserted output. -/
structure Annotated where
  root : Route
  original : RuleTree

def Annotated.positions (program : Annotated) : List Route :=
  treeRoutes program.root program.original

structure Generated where
  tree : RuleTree
  deliveries : List Delivery

mutual
/-- Insert exactly at the selected ORIGINAL node, recording both owner and
physical delivery position. Other source rules and branches are preserved. -/
def generateAt (route : Route) (delivery : Delivery) (tree : RuleTree) : Generated :=
  if route = delivery.physical then
    ⟨.sharedE delivery.original.binder tree, [delivery]⟩
  else match tree with
  | .rule rule site context premises children =>
      let result := generateForest (route ++ [0]) delivery children
      ⟨.rule rule site context premises result.1, result.2⟩
  | .existsE binder body =>
      let result := generateAt (route ++ [0]) delivery body
      ⟨.existsE binder result.tree, result.deliveries⟩
  | .forallE binder body =>
      let result := generateAt (route ++ [0]) delivery body
      ⟨.forallE binder result.tree, result.deliveries⟩
  | .initializerE site body =>
      let result := generateAt (route ++ [0]) delivery body
      ⟨.initializerE site result.tree, result.deliveries⟩
  | .executionE binder body =>
      let result := generateAt (route ++ [0]) delivery body
      ⟨.executionE binder result.tree, result.deliveries⟩
  | .sharedE binder body =>
      let result := generateAt (route ++ [0]) delivery body
      ⟨.sharedE binder result.tree, result.deliveries⟩
  | .publishGroup bindings body =>
      let result := generateAt (route ++ [0]) delivery body
      ⟨.publishGroup bindings result.tree, result.deliveries⟩
  | .atPublication binding body =>
      let result := generateAt (route ++ [0]) delivery body
      ⟨.atPublication binding result.tree, result.deliveries⟩
  | .aliasPublication original aliasName body =>
      let result := generateAt (route ++ [0]) delivery body
      ⟨.aliasPublication original aliasName result.tree, result.deliveries⟩
  | .choice site left right =>
      let first := generateAt (route ++ [0]) delivery left
      let second := generateAt (route ++ [3]) delivery right
      ⟨.choice site first.tree second.tree, first.deliveries ++ second.deliveries⟩

def generateForest (route : Route) (delivery : Delivery) : RuleForest → RuleForest × List Delivery
  | .nil => ⟨.nil, []⟩
  | .cons head tail =>
      let first := generateAt route delivery head
      let second := generateForest (route ++ [1]) delivery tail
      ⟨.cons first.tree second.1, first.deliveries ++ second.2⟩
end

def Annotated.generate (program : Annotated) (delivery : Delivery) : Generated :=
  generateAt program.root delivery program.original

def Parameter.annotated (parameter : Parameter) : Annotated :=
  ⟨[], sourceRules parameter.context parameter.source⟩

/-- The original source builder now emits formal Shared itself. This
consumer retains that exact tree; it never applies the additive transformer. -/
def Parameter.generate (parameter : Parameter) : Generated :=
  ⟨sourceRules parameter.context parameter.source, [entryDelivery parameter.registration]⟩

theorem generated_parameter_is_original (parameter : Parameter) :
    parameter.generate.tree = sourceRules parameter.context parameter.source := rfl

/-- Existing delivery occurrence in the actual source tree, not metadata
for a separately transformed program. -/
theorem generated_parameter_existing_owner (parameter : Parameter) :
    ((sourceOwners parameter.context parameter.source).drop
      (match parameter.formal.entry with | .value => 3 | .computation => 2)).head? =
      some parameter.registration.physicalRetainedOwner := by
  cases mode : parameter.formal.entry
  · exact source_lambda_value_shared parameter.context parameter.lambdaSite parameter.formal
      parameter.pattern parameter.body mode
  · exact source_lambda_computation_shared parameter.context parameter.lambdaSite parameter.formal
      parameter.pattern parameter.body mode

theorem generated_parameter_delivery_matches_owner (parameter : Parameter) :
    (entryDelivery parameter.registration).physical = parameter.registration.physicalRetainedOwner.route ∧
    (entryDelivery parameter.registration).original.binder = parameter.registration.physicalRetainedOwner.binder ∧
    (entryDelivery parameter.registration).original.telescope = parameter.registration.physicalRetainedOwner.telescope :=
  ⟨rfl, rfl, rfl⟩

theorem insertion_uses_original_node (route : Route) (delivery : Delivery) (tree : RuleTree)
    (same : route = delivery.physical) :
    generateAt route delivery tree = ⟨.sharedE delivery.original.binder tree, [delivery]⟩ := by
  cases tree <;> simp [generateAt, same]

/-- Actual original Lambda generation supplies exactly one formal delivery.
Body/pattern source trees remain arbitrary and are not executed by generation. -/
theorem generated_parameter_delivery (parameter : Parameter) :
    parameter.generate.deliveries = [entryDelivery parameter.registration] := rfl

/-- Full independent history-record keys are used directly. The old Runtime
projection remains an execution projection and cannot select assignments. -/
abbrev CompleteKey (s : Sorts) (View : Type) := RecordKey s View

structure DecoratedKey (s : Sorts) (View Proof : Type) where
  key : CompleteKey s View
  joint : Joint s
  description : Proof

def DecoratedKey.raw (packet : DecoratedKey s View Proof) : CompleteKey s View := packet.key

theorem description_not_in_raw_key (key : CompleteKey s View) (first second : Joint s)
    (left right : Proof) :
    (DecoratedKey.mk key first left).raw = (DecoratedKey.mk key second right).raw := rfl

theorem complete_key_keeps_operands (introduction : Owner) (origin : Declaration)
    (parents : List (HistoryStep s View)) (occurrence : Nat) (raw : RawRecord s View) :
    (recordKey introduction origin parents occurrence raw).step.raw = raw ∧
    (recordKey introduction origin parents occurrence raw).parents = parents ∧
    (recordKey introduction origin parents occurrence raw).step.origin = origin ∧
    (recordKey introduction origin parents occurrence raw).step.route = introduction.route ∧
    (recordKey introduction origin parents occurrence raw).step.occurrence = occurrence :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem erased_operation_collision_preserved (introduction : Owner) (origin : Declaration)
    (parents : List (HistoryStep s View)) (occurrence : Nat)
    (invocation : Invocation s View) (others : s.Context) (request : s.Observation)
    (handle continuation : s.Continuation) (suffix : s.Context) (response : ResponseData s View) :
    let first := RawRecord.response invocation others request 0 handle continuation suffix response
    let second := RawRecord.response invocation others request 1 handle continuation suffix response
    first.runtime = second.runtime ∧
      recordKey introduction origin parents occurrence first ≠
        recordKey introduction origin parents occurrence second := by
  dsimp only
  refine ⟨rfl, ?_⟩
  intro same
  have raw := congrArg (fun key : RecordKey s View => key.step.raw) same
  cases raw


open NativeClosureEnvironment SourceIdentityWorld
variable {View : Type}

/-- Reinterpretation at a freshly allocated address, using the ALREADY
selected formal contract. Every other address/view retains its prior data. -/
def installValueContract (assignment : ViewAssignment s V) (address : Nat)
    (descriptor : s.Descriptor) : ViewAssignment s V :=
  {assignment with descriptor := fun index view =>
    if index = address then descriptor else assignment.descriptor index view}

theorem fresh_contract_before_readout (assignment : ViewAssignment s V)
    (store : Store (Received V)) (address : Nat) (empty : store.cell address = none)
    (descriptor : s.Descriptor) :
    bindingReadout (installValueContract assignment address descriptor) store =
      bindingReadout assignment store := by
  funext index
  by_cases same : index = address
  · subst index
    simp only [bindingReadout, empty, Option.map_none]
  · cases found : store.cell index with
    | none => simp only [bindingReadout, found, Option.map_none]
    | some raw =>
        cases role : raw.interface <;>
          simp [bindingReadout, found, ViewAssignment.received, installValueContract, role, same]

/-- Actual Return/cell constructor; descriptor selection is an earlier input,
while the new address is computed from the native allocator. -/
def nativeReturned (assignment : ViewAssignment s V) (raw : Received V)
    (observation : s.Observation) (after : Current s)
    (endpoints : List (Endpoint × Object s)) (bindings : List (Name × Nat)) : Returned s :=
  ⟨observation, assignment.value raw.value, assignment.root raw.value, after, endpoints, bindings⟩

def Selected.valueDescriptor (selection : Selected s View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.value) : s.Descriptor := by
  simpa only [Contract, mode] using selection.contract

def nativeEvidence (parameter : Parameter) (selection : Selected s View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.value)
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (raw : Received V) (observation : s.Observation) (after : Current s)
    (endpoints : List (Endpoint × Object s)) (bindings : List (Name × Nat))
    (witness : s.WitnessValue) : Retained s parameter.registration :=
  returnedEvidence parameter.registration mode
    (nativeReturned assignment raw observation after endpoints bindings)
    (selection.valueDescriptor mode) world.cells.size witness

theorem native_evidence_address (parameter : Parameter) (selection : Selected s View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.value)
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (raw : Received V) (observation : s.Observation) (after : Current s)
    (endpoints : List (Endpoint × Object s)) (bindings : List (Name × Nat))
    (witness : s.WitnessValue) :
    (nativeEvidence parameter selection mode assignment world raw observation after endpoints bindings witness).address =
      world.cells.size := rfl

/-- Exact installed object: both actual raw projections are preserved, and
its description is the same pre-invocation formal selection. -/
theorem native_evidence_object (parameter : Parameter) (selection : Selected s View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.value)
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (raw : Received V) (observation : s.Observation) (after : Current s)
    (endpoints : List (Endpoint × Object s)) (bindings : List (Name × Nat))
    (witness : s.WitnessValue) :
    (nativeEvidence parameter selection mode assignment world raw observation after endpoints bindings witness).data.installed =
      .value (selection.valueDescriptor mode) (assignment.value raw.value) (assignment.root raw.value) :=
  returned_evidence_object parameter.registration mode _ _ _ _

/-- Decode the SAME generated retained payload. No second Shared value is
selected for another logical description or for this consumer theorem. -/
def deliverFrame (readout : RuntimeReadout s View) (state : Decoded s View)
    (parameter : Parameter) (evidence : Retained s parameter.registration)
    (parents : List (EventStep (Payload s View))) (occurrence : Nat) : Decoded s View :=
  decodeFrame readout state (evidence.frame parameter.registration parents occurrence)

theorem delivered_actual_cell (readout : RuntimeReadout s View) (state : Decoded s View)
    (parameter : Parameter) (selection : Selected s View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.value)
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (raw : Received V) (observation : s.Observation) (after : Current s)
    (endpoints : List (Endpoint × Object s)) (bindings : List (Name × Nat))
    (witness : s.WitnessValue) (parents : List (EventStep (Payload s View))) (occurrence : Nat) :
    let evidence := nativeEvidence parameter selection mode assignment world raw observation after endpoints bindings witness
    (deliverFrame readout state parameter evidence parents occurrence).installed world.cells.size =
      some (.value (selection.valueDescriptor mode) (assignment.value raw.value) (assignment.root raw.value)) := by
  dsimp only
  change (state.shared _).installed _ = _
  have installed := retained_installs_actual_object parameter.registration
    (nativeEvidence parameter selection mode assignment world raw observation after endpoints bindings witness) state
  simpa only [native_evidence_address, native_evidence_object] using installed

theorem delivered_formal_binding (readout : RuntimeReadout s View) (state : Decoded s View)
    (parameter : Parameter) (evidence : Retained s parameter.registration)
    (parents : List (EventStep (Payload s View))) (occurrence : Nat) :
    (deliverFrame readout state parameter evidence parents occurrence).assignment.binding parameter.formal.name =
      some evidence.address := by
  change (state.shared _).assignment.binding _ = _
  exact lambda_retained_binds_formal parameter.context parameter.lambdaSite parameter.formal
    parameter.pattern parameter.body evidence state

theorem delivered_every_other_cell (readout : RuntimeReadout s View) (state : Decoded s View)
    (parameter : Parameter) (evidence : Retained s parameter.registration)
    (parents : List (EventStep (Payload s View))) (occurrence index : Nat)
    (different : index ≠ evidence.address) :
    (deliverFrame readout state parameter evidence parents occurrence).installed index = state.installed index := by
  change (state.shared _).installed index = _
  exact retained_preserves_other parameter.registration evidence state index different

theorem delivered_keeps_entire_prefix (readout : RuntimeReadout s View) (state : Decoded s View)
    (parameter : Parameter) (evidence : Retained s parameter.registration)
    (parents : List (EventStep (Payload s View))) (occurrence : Nat) :
    (deliverFrame readout state parameter evidence parents occurrence).fixedFrames =
      state.fixedFrames ++ [evidence.frame parameter.registration parents occurrence] := rfl


/-- The decoder's complete installed map is the one-cell extension, not just
its projection at the new address. -/
theorem delivered_installed_map (readout : RuntimeReadout s View) (state : Decoded s View)
    (parameter : Parameter) (evidence : Retained s parameter.registration)
    (parents : List (EventStep (Payload s View))) (occurrence : Nat) :
    (deliverFrame readout state parameter evidence parents occurrence).installed =
      extendBindings state.installed evidence.address evidence.data.installed := rfl

/-- Exact native/decoder agreement. The premise is the previous representation
invariant; the post-bind equation is derived from the actual constructor. -/
theorem delivered_native_bind_readout (readout : RuntimeReadout s View) (state : Decoded s View)
    (parameter : Parameter) (selection : Selected s View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.value)
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (cells : List (Option (Received V))) (actualCells : world.cells = vectorStore cells)
    (represented : state.installed = bindingReadout assignment world.cells)
    (parent : Nat) (formalKey : K) (raw : Received V) (node : Node K D)
    (found : nodeAt world.environments parent = some node)
    (observation : s.Observation) (after : Current s)
    (endpoints : List (Endpoint × Object s)) (bindings : List (Name × Nat))
    (witness : s.WitnessValue) (parents : List (EventStep (Payload s View))) (occurrence : Nat) :
    let evidence := nativeEvidence parameter selection mode assignment world raw observation after endpoints bindings witness
    let postAssignment := installValueContract assignment world.cells.size (selection.valueDescriptor mode)
    (deliverFrame readout state parameter evidence parents occurrence).installed =
      bindingReadout postAssignment (bindValue world parent formalKey raw node found).cells := by
  dsimp only
  rw [delivered_installed_map, native_evidence_object]
  change extendBindings state.installed world.cells.size _ = _
  rw [parameter_bind_readout]
  have empty : world.cells.cell world.cells.size = none := by
    rw [actualCells]
    exact vector_cell_beyond cells cells.length (Nat.le_refl _)
  rw [fresh_contract_before_readout assignment world.cells world.cells.size empty, represented]
  simp [installValueContract]

/-- Every prior Some survives, without changing the original all-Some
quantifier into a bounded semantic predicate. -/
theorem delivered_preserves_all_old (readout : RuntimeReadout s View) (state : Decoded s View)
    (parameter : Parameter) (selection : Selected s View parameter)
    (mode : parameter.formal.entry = OriginalSource.Entry.value)
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (cells : List (Option (Received V))) (actualCells : world.cells = vectorStore cells)
    (represented : state.installed = bindingReadout assignment world.cells)
    (raw : Received V) (observation : s.Observation) (after : Current s)
    (endpoints : List (Endpoint × Object s)) (bindings : List (Name × Nat))
    (witness : s.WitnessValue) (parents : List (EventStep (Payload s View))) (occurrence : Nat)
    (index : Nat) (object : Installed s) (present : state.installed index = some object) :
    let evidence := nativeEvidence parameter selection mode assignment world raw observation after endpoints bindings witness
    (deliverFrame readout state parameter evidence parents occurrence).installed index = some object := by
  dsimp only
  rw [delivered_installed_map, native_evidence_object, native_evidence_address]
  apply extend_bindings_old _ present
  rw [represented, actualCells]
  simp only [bindingReadout, vectorStore]
  rw [vector_cell_beyond cells cells.length (Nat.le_refl _)]
  rfl

/-- Actual environment extension consumes the payload in place. There is no
new root or replacement of the existing frame/entry/publication prefix. -/
theorem deliver_existing_environment (readout : RuntimeReadout s View)
    (environment : Environment (Payload s View)) (state : Decoded s View)
    (decoded : decode readout environment = some state)
    (parameter : Parameter) (evidence : Retained s parameter.registration) (occurrence : Nat) :
    decode readout (environment.extend parameter.registration.retainedOwner.binder
      (scopeCandidate environment occurrence (.shared (evidence.shared parameter.registration)))) =
      some (deliverFrame readout state parameter evidence environment.eventPath occurrence) := by
  exact decode_extend readout environment parameter.registration.retainedOwner.binder _ state decoded

/-- Full raw action carrier. Independent records are never replaced by their
non-injective execution projection when constructing a key. -/
inductive RawAction (s : Sorts) (View : Type) where
  | direct (runtime : Runtime s View)
  | independent (record : RawRecord s View)

def RawAction.execution : RawAction s View → Runtime s View
  | .direct runtime => runtime
  | .independent record => record.runtime

structure RawStep (s : Sorts) (View : Type) where
  declaration : Declaration
  introduction : Route
  binder : Binder
  occurrence : Nat
  action : RawAction s View

structure RawKey (s : Sorts) (View : Type) where
  parents : List (RawStep s View)
  current : RawStep s View

def RawStep.erase (step : RawStep s View) : EventStep (Payload s View) :=
  ⟨step.binder.site, step.binder.kind, step.occurrence, .runtime step.action.execution⟩

def RawKey.erasedPath (key : RawKey s View) : List (EventStep (Payload s View)) :=
  key.parents.map RawStep.erase ++ [key.current.erase]

theorem full_key_retained_before_erasure (key : RawKey s View) :
    (key, key.erasedPath).1 = key := rfl

structure SharedKey (s : Sorts) (View : Type) where
  declaration : Declaration
  introduction : Route
  actual : RawKey s View

abbrev SharedAssignment (s : Sorts) (View : Type) := SharedKey s View → s.WitnessValue

def parameterSharedKey (parameter : Parameter) (selection : Selected s View parameter)
    (actual : RawKey s View) : SharedKey s View :=
  ⟨parameter.declaration, selection.outerRoute ++ parameter.registration.retainedOwner.route, actual⟩

/-- The actual Return key is computed from the same returned object used by
Shared delivery. All independent raw suffix fields and parents are retained. -/
def nativeReturnKey (parameter : Parameter) (selection : Selected s View parameter)
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (raw : Received V) (observation : s.Observation) (after : Current s)
    (endpoints : List (Endpoint × Object s)) (bindings : List (Name × Nat))
    (parents : List (RawStep s View)) (occurrence : Nat) : RawKey s View :=
  ⟨parents, ⟨parameter.declaration, selection.outerRoute ++ parameter.registration.route ++ [0],
    ⟨parameter.formal.site, .returnRebind, 0⟩, occurrence,
    .direct (.returnRebind (nativeReturned assignment raw observation after endpoints
      (bindings ++ [(parameter.formal.name, world.cells.size)])).outcome)⟩⟩

/-- One original strategy is applied at the exact owner and actual complete
history. Neither a description frame nor a membership proof is a key field. -/
def ownedNativeEvidence (shared : SharedAssignment s View) (parameter : Parameter)
    (selection : Selected s View parameter) (mode : parameter.formal.entry = OriginalSource.Entry.value)
    (assignment : ViewAssignment s V) (world : World K D V ViewData SiteData Rest)
    (raw : Received V) (observation : s.Observation) (after : Current s)
    (endpoints : List (Endpoint × Object s)) (bindings : List (Name × Nat))
    (parents : List (RawStep s View)) (occurrence : Nat) : Retained s parameter.registration :=
  nativeEvidence parameter selection mode assignment world raw observation after endpoints bindings
    (shared (parameterSharedKey parameter selection
      (nativeReturnKey parameter selection assignment world raw observation after endpoints bindings parents occurrence)))

structure DescribedActual (s : Sorts) (View Proof : Type) where
  actual : RawKey s View
  proof : Proof

def describedShared (assignment : SharedAssignment s View) (parameter : Parameter)
    (selection : Selected s View parameter) (description : DescribedActual s View Proof) : s.WitnessValue :=
  assignment (parameterSharedKey parameter selection description.actual)

theorem same_actual_shared_across_descriptions (assignment : SharedAssignment s View)
    (parameter : Parameter) (selection : Selected s View parameter) (actual : RawKey s View)
    (first second : Proof) :
    describedShared assignment parameter selection ⟨actual, first⟩ =
      describedShared assignment parameter selection ⟨actual, second⟩ := rfl


/-- First complete producer-to-decoder checkpoint. It selects the contract
from the original pre-invocation assignment, computes the real allocation
address, uses one owned Shared strategy application, and consumes exactly
that payload in the original decoder. No post-bind readout law is an input.
The delivery metadata now refers to the actual original builder. The direct
Build/anchor consumer is supplied separately by OriginalFormalShared. -/
theorem source_assigned_native_delivery
    (formalAssignment : FormalAssignment s View) (sharedAssignment : SharedAssignment s View)
    (parameter : Parameter) (outerRoute : Route)
    (prior : ScopeValues s View parameter.typeScope)
    (mode : parameter.formal.entry = OriginalSource.Entry.value)
    (readout : RuntimeReadout s View) (state : Decoded s View)
    (assignment : ViewAssignment s V) (world : World Name D V ViewData SiteData Rest)
    (cells : List (Option (Received V))) (actualCells : world.cells = vectorStore cells)
    (represented : state.installed = bindingReadout assignment world.cells)
    (parent : Nat) (raw : Received V) (node : Node Name D)
    (found : nodeAt world.environments parent = some node)
    (observation : s.Observation) (after : Current s)
    (endpoints : List (Endpoint × Object s)) (bindings : List (Name × Nat))
    (rawParents : List (RawStep s View)) (rawOccurrence occurrence : Nat) :
    let selection := select formalAssignment parameter outerRoute prior
    let evidence := ownedNativeEvidence sharedAssignment parameter selection mode assignment world raw
      observation after endpoints bindings rawParents rawOccurrence
    let actual := nativeReturnKey parameter selection assignment world raw observation after endpoints bindings
      rawParents rawOccurrence
    let delivered := deliverFrame readout state parameter evidence actual.erasedPath occurrence
    parameter.generate.deliveries = [entryDelivery parameter.registration] ∧
    delivered.installed = bindingReadout
      (installValueContract assignment world.cells.size (selection.valueDescriptor mode))
      (bindValue world parent parameter.formal.name raw node found).cells ∧
    delivered.assignment.binding parameter.formal.name = some world.cells.size ∧
    (∀ index object, state.installed index = some object → delivered.installed index = some object) := by
  dsimp only
  refine ⟨generated_parameter_delivery parameter, ?_, ?_, ?_⟩
  · exact delivered_native_bind_readout readout state parameter _ mode assignment world cells actualCells
      represented parent parameter.formal.name raw node found observation after endpoints bindings _ _ occurrence
  · exact delivered_formal_binding readout state parameter _ _ occurrence
  · intro index object present
    exact delivered_preserves_all_old readout state parameter _ mode assignment world cells actualCells
      represented raw observation after endpoints bindings _ _ occurrence index object present


/-- The source-formal specialization uses exactly this Parameter's resolved
name. It also proves lookup/shadowing for that same native key. -/
theorem source_formal_native_lookup (parameter : Parameter)
    (world : World Name D V ViewData SiteData Rest) (parent : Nat)
    (raw : Received V) (node : Node Name D)
    (found : nodeAt world.environments parent = some node) :
    lookupKey parameter.formal.name
      (bindValue world parent parameter.formal.name raw node found).environments
      world.environments.size = some world.cells.size :=
  parameter_formal_shadows world parent parameter.formal.name raw node found

/-- An old nonlatest closure retains its original saved lookup even when the
new source formal shadows the same resolved name in the current environment. -/
theorem source_formal_saved_capture (parameter : Parameter)
    (world : World Name D V ViewData SiteData Rest) (parent : Nat)
    (raw : Received V) (node : Node Name D) (found : nodeAt world.environments parent = some node)
    (closure : Closure Body) (saved : closure.savedEnvironment < world.environments.size)
    (references : Body → Nat → Option Name) (name : Nat) :
    captureAddress (bindValue world parent parameter.formal.name raw node found).environments
      closure references name = captureAddress world.environments closure references name :=
  capture_address_parameter_bind world closure saved references name parent parameter.formal.name raw node found

end YulangClosure.OriginalParameterWorld
