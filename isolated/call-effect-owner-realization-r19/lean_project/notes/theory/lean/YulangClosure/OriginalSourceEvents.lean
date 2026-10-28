import YulangClosure.OriginalSourceEnvironment
import YulangClosure.SourceSignatureConstruction

/-!
Source-owned event declarations and typed packets, separate from raw identity.
Authority: SG §3.3/§5.2 and Call semantic input realization §§2–4. The actual
source builder supplies owner occurrences; no complete registry, source
judgment, semantic membership or event-readback law is an input.

This constructor packet does not identify its history data grammar with
every independently admitted original context. Primitive interpretations and
semantic admission remain independent inputs. The source builder now emits
formal Shared; its distinct virtual and physical coordinates are related below.
Complete semantic/native delivery remains a separate local application.
-/
namespace YulangClosure.OriginalSourceEvents

open OriginalSource OriginalSourceEnvironment OriginalSourceInterpretation

abbrev Route := List Nat

/-- A source constructor position, not an assertion that sites are unique. -/
structure ScopeEntry where
  route : Route
  binder : Binder
  deriving DecidableEq, Repr

inductive Lifetime where
  | actualEvent | retainedShared | descriptionProof
  deriving DecidableEq, Repr

structure Owner where
  route : Route
  binder : Binder
  telescope : List ScopeEntry
  lifetime : Lifetime
  deriving DecidableEq, Repr

def owner (route : Route) (scope : List ScopeEntry) (binder : Binder)
    (lifetime : Lifetime) : Owner := ⟨route, binder, scope, lifetime⟩

def extendScope (scope : List ScopeEntry) (route : Route) (binder : Binder) : List ScopeEntry :=
  scope ++ [⟨route, binder⟩]

def binderOwner (route : Route) (scope : List ScopeEntry) (binder : Binder) : List Owner :=
  if binder.isEvent then [owner route scope binder .actualEvent]
  else if binder.kind == .shared then [owner route scope binder .retainedShared]
  else if binder.kind == .eventProof then [owner route scope binder .descriptionProof]
  else []

mutual
/-- Exhaustive structural walk of the existing original rule program. Distinct descent/left (0), sibling (1), and right-choice (3) tags
preserve occurrences even when raw sites coincide; tag 2 is retained evidence. -/
def owners (route : Route) (scope : List ScopeEntry) : RuleTree → List Owner
  | .rule _ _ _ _ children => forestOwners (route ++ [0]) scope children
  | .existsE binder body | .forallE binder body | .executionE binder body | .sharedE binder body =>
      binderOwner route scope binder ++ owners (route ++ [0]) (extendScope scope route binder) body
  | .initializerE _ body | .publishGroup _ body | .atPublication _ body | .aliasPublication _ _ body =>
      owners (route ++ [0]) scope body
  | .choice _ left right => owners (route ++ [0]) scope left ++ owners (route ++ [3]) scope right

def forestOwners (route : Route) (scope : List ScopeEntry) : RuleForest → List Owner
  | .nil => []
  | .cons head tail => owners route scope head ++ forestOwners (route ++ [1]) scope tail
end

def sourceOwners (context : Context) (source : Source category) : List Owner :=
  owners [] [] (sourceRules context source)

theorem runtime_owner_constructed (route : Route) (scope : List ScopeEntry)
    (binder : Binder) (actual : binder.isEvent = true) :
    binderOwner route scope binder = [owner route scope binder .actualEvent] := by
  simp only [binderOwner, actual, ↓reduceIte]

theorem proof_owner_separate (route : Route) (scope : List ScopeEntry) (site : Site) :
    binderOwner route scope ⟨site, .eventProof, 0⟩ =
      [owner route scope ⟨site, .eventProof, 0⟩ .descriptionProof] := rfl

/-- This record is emitted by the actual parameterEntry node. The complete
original role atom/context and receipt operand list remain attached. -/
structure EntryRegistration where
  route : Route
  telescope : List ScopeEntry
  site : Site
  context : Context
  role : Atom
  receipt : Atom
  entry : Entry
  deriving DecidableEq, Repr

def atomOfKind (kind : AtomKind) (premises : List Premise) : Option Atom :=
  premises.findSome? fun premise => match premise with
    | .atom data => if data.kind == kind then some data else none
    | _ => none

def entryAt (route : Route) (scope : List ScopeEntry) (rule : Rule)
    (site : Site) (context : Context) (premises : List Premise) : Option EntryRegistration := do
  if rule != .parameterEntry then none else do
    let role ← atomOfKind .sourceFormalRole premises
    let receipt ← atomOfKind .receiptFormation premises
    let entry ← role.entry
    pure ⟨route, scope, site, context, role, receipt, entry⟩

mutual
def entries (route : Route) (scope : List ScopeEntry) : RuleTree → List EntryRegistration
  | .rule rule site context premises children =>
      (entryAt route scope rule site context premises).toList ++ forestEntries (route ++ [0]) scope children
  | .existsE binder body | .forallE binder body | .executionE binder body | .sharedE binder body =>
      entries (route ++ [0]) (extendScope scope route binder) body
  | .initializerE _ body | .publishGroup _ body | .atPublication _ body | .aliasPublication _ _ body =>
      entries (route ++ [0]) scope body
  | .choice _ left right => entries (route ++ [0]) scope left ++ entries (route ++ [3]) scope right

def forestEntries (route : Route) (scope : List ScopeEntry) : RuleForest → List EntryRegistration
  | .nil => []
  | .cons head tail => entries route scope head ++ forestEntries (route ++ [1]) scope tail
end

def sourceEntries (context : Context) (source : Source category) : List EntryRegistration :=
  entries [] [] (sourceRules context source)

def formalContext (context : Context) (formal : Formal) (body : Source .expression) : Context :=
  {name := formal.name, owner := formal.site, kind := .formal, annotation := formal.annotation,
    entry := some formal.entry, singleUse := body.nameCount formal.name == 1} :: context

def lambdaScope (site : Site) (formal : Formal) : List ScopeEntry :=
  [⟨[], ⟨formal.site, .description, 0⟩⟩,
   ⟨[0], ⟨site, .viewLogic, 0⟩⟩,
   ⟨[0, 0, 0], ⟨site, .invocation, 0⟩⟩,
   ⟨[0, 0, 0, 0], ⟨formal.site, .receipt, 0⟩⟩]

def lambdaEntry (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) : EntryRegistration :=
  let inner := formalContext context formal body
  ⟨[0, 0, 0, 0, 0], lambdaScope site formal, formal.site, inner,
    {(atom .sourceFormalRole formal.site inner) with
      annotation := formal.annotation, entry := some formal.entry},
    atom .receiptFormation formal.site inner [site, pattern.site, body.site], formal.entry⟩

/-- An actual raw Lambda supplies the parameter registration. The body and
pattern are arbitrary original sources, not supplied local rule packages. -/
theorem source_lambda_entry (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    (sourceEntries context (.lambda ⟨site, none⟩ formal pattern body)).head? =
      some (lambdaEntry context site formal pattern body) := by
  cases mode : formal.entry <;>
    simp only [sourceEntries, sourceRules, lambdaEntry, lambdaScope, formalContext, mode]
  all_goals rfl

def lambdaInvocationOwner (site : Site) (formal : Formal) : Owner :=
  owner [0, 0, 0]
    [⟨[], ⟨formal.site, .description, 0⟩⟩, ⟨[0], ⟨site, .viewLogic, 0⟩⟩]
    ⟨site, .invocation, 0⟩ .actualEvent

theorem source_lambda_invocation (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    (sourceOwners context (.lambda ⟨site, none⟩ formal pattern body)).head? =
      some (lambdaInvocationOwner site formal) := by
  simp only [sourceOwners, sourceRules]
  rfl

theorem source_lambda_receipt (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    ((sourceOwners context (.lambda ⟨site, none⟩ formal pattern body)).drop 1).head? =
      some (owner [0, 0, 0, 0]
        [⟨[], ⟨formal.site, .description, 0⟩⟩, ⟨[0], ⟨site, .viewLogic, 0⟩⟩,
          ⟨[0, 0, 0], ⟨site, .invocation, 0⟩⟩]
        ⟨formal.site, .receipt, 0⟩ .actualEvent) := by
  simp only [sourceOwners, sourceRules]
  rfl

/-- New retained evidence belongs after the actual receipt and, for Value
entry, after the actual Return/rebind. The reserved route names original
retained ownership; physicalRetainedOwner records its emitted position. -/
def EntryRegistration.retainedOwner (entry : EntryRegistration) : Owner :=
  let scope := match entry.entry with
    | .value => extendScope entry.telescope (entry.route ++ [0]) ⟨entry.site, .returnRebind, 0⟩
    | .computation => entry.telescope
  owner (entry.route ++ [2]) scope ⟨entry.site, .shared, 0⟩ .retainedShared

/-- The emitted Shared node has a physical tree coordinate distinct from
its reserved original retained-field coordinate. Its binder and dependencies
are exactly the original retained owner's. -/
def EntryRegistration.physicalRetainedOwner (entry : EntryRegistration) : Owner :=
  {entry.retainedOwner with route := entry.route ++ match entry.entry with
    | .value => [0, 0]
    | .computation => [0]}

theorem physical_retained_keeps_owner (entry : EntryRegistration) :
    entry.physicalRetainedOwner.binder = entry.retainedOwner.binder ∧
    entry.physicalRetainedOwner.telescope = entry.retainedOwner.telescope ∧
    entry.physicalRetainedOwner.lifetime = entry.retainedOwner.lifetime := ⟨rfl, rfl, rfl⟩

theorem source_lambda_value_shared (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) (mode : formal.entry = .value) :
    ((sourceOwners context (.lambda ⟨site, none⟩ formal pattern body)).drop 3).head? =
      some (lambdaEntry context site formal pattern body).physicalRetainedOwner := by
  simp only [sourceOwners, sourceRules, mode, lambdaEntry, lambdaScope, formalContext,
    EntryRegistration.physicalRetainedOwner, EntryRegistration.retainedOwner]
  rfl

theorem source_lambda_computation_shared (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) (mode : formal.entry = .computation) :
    ((sourceOwners context (.lambda ⟨site, none⟩ formal pattern body)).drop 2).head? =
      some (lambdaEntry context site formal pattern body).physicalRetainedOwner := by
  simp only [sourceOwners, sourceRules, mode, lambdaEntry, lambdaScope, formalContext,
    EntryRegistration.physicalRetainedOwner, EntryRegistration.retainedOwner]
  rfl

theorem value_retained_below_return (entry : EntryRegistration) (mode : entry.entry = .value) :
    entry.retainedOwner.telescope = entry.telescope ++
      [⟨entry.route ++ [0], ⟨entry.site, .returnRebind, 0⟩⟩] := by
  simp only [EntryRegistration.retainedOwner, mode, extendScope, owner]

theorem computation_retained_below_receipt (entry : EntryRegistration)
    (mode : entry.entry = .computation) :
    entry.retainedOwner.telescope = entry.telescope := by
  simp only [EntryRegistration.retainedOwner, mode, owner]

theorem retained_keeps_old_scope (entry : EntryRegistration) (older : ScopeEntry)
    (present : older ∈ entry.telescope) : older ∈ entry.retainedOwner.telescope := by
  cases mode : entry.entry
  · rw [value_retained_below_return entry mode]
    exact List.mem_append_left _ present
  · rw [computation_retained_below_receipt entry mode]
    exact present

theorem lambda_retained_receipt (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    (⟨[0, 0, 0, 0], ⟨formal.site, .receipt, 0⟩⟩ : ScopeEntry) ∈
      (lambdaEntry context site formal pattern body).retainedOwner.telescope := by
  apply retained_keeps_old_scope
  simp [lambdaEntry, lambdaScope]

theorem lambda_registration_formal (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) :
    ((lambdaEntry context site formal pattern body).context.head?).map Binding.name = some formal.name ∧
    (lambdaEntry context site formal pattern body).receipt.operands = [site, pattern.site, body.site] :=
  ⟨rfl, rfl⟩

inductive Field where
  | assignment | currentWitness | scope | authority | incidence | dictionary | retainedWitness
  | retainedNames | retainedObjects
  deriving DecidableEq, Repr

def Field.slot : Field → Nat
  | .assignment => 0 | .currentWitness => 1 | .scope => 2 | .authority => 3
  | .incidence => 4 | .dictionary => 5 | .retainedWitness => 6
  | .retainedNames => 7 | .retainedObjects => 8

def Field.Sort (s : Sorts) : Field → Type
  | .assignment => s.Assignment | .currentWitness => s.JointWitness
  | .scope => s.Scope | .authority => s.Authority | .incidence => s.Incidence
  | .dictionary => s.Dictionary | .retainedWitness => s.WitnessValue
  | .retainedNames => List (Name × Nat) | .retainedObjects => List (Nat × Installed s)

/-- Original event coordinates and retained evidence are data under their
source telescope. `event.witness` here is the source runtime-field assignment;
it is not asserted equal to the whole witness after a description/EventProof
frame. Description proof interpretation is kept separately below. There is
no membership or admission proof in this record. -/
structure Joint (s : Sorts) where
  event : Event s
  retainedWitness : s.WitnessValue
  retainedNames : List (Name × Nat)
  retainedObjects : List (Nat × Installed s)

def Field.read (field : Field) (joint : Joint s) : field.Sort s :=
  match field with
  | .assignment => joint.event.eta | .currentWitness => joint.event.witness
  | .scope => joint.event.scope | .authority => joint.event.authority
  | .incidence => joint.event.incidence | .dictionary => joint.event.dictionary
  | .retainedWitness => joint.retainedWitness
  | .retainedNames => joint.retainedNames | .retainedObjects => joint.retainedObjects

def Owner.fields (introduction : Owner) : List Field :=
  match introduction.lifetime with
  | .actualEvent => [.assignment, .currentWitness, .scope, .authority, .incidence, .dictionary]
  | .retainedShared => [.retainedNames, .retainedObjects, .retainedWitness]
  | .descriptionProof => []

/-- The original catalogue machinery keeps each output projection on the
SAME complete joint tuple. These are output fields, including inherited
coordinates, not a declaration that every transition creates a fresh eta or
proof binder. Equality is raw field projection, never typing. -/
def catalogue (s : Sorts) (introduction : Owner) : SourceSignatureConstruction.Catalogue (Joint s) where
  Port := {field : Field // field ∈ introduction.fields}
  Packet := fun joint field => {value : field.val.Sort s // value = field.val.read joint}
  scope := introduction.telescope.map ScopeEntry.binder ++ [introduction.binder]
  sharedSlot := fun field => field.val.slot

def declaredField (introduction : Owner) (joint : Joint s)
    (field : (catalogue s introduction).Port) : (catalogue s introduction).Packet joint field :=
  ⟨field.val.read joint, rfl⟩

theorem catalogue_keeps_telescope (introduction : Owner) :
    (catalogue s introduction).scope =
      introduction.telescope.map ScopeEntry.binder ++ [introduction.binder] := rfl

theorem declared_field_same_joint (introduction : Owner) (joint : Joint s)
    (field : (catalogue s introduction).Port) :
    (declaredField introduction joint field).val = field.val.read joint := rfl

/-- Raw event identity keeps source route, actual parent path, occurrence and
all independent raw operands. Typed fields and description frames are absent. -/
structure ActualKey (s : Sorts) (View : Type) where
  origin : Declaration
  route : Route
  binder : Binder
  parents : List (EventStep (Runtime s View))
  occurrence : Nat
  raw : Runtime s View

def actualKey (introduction : Owner) (origin : Declaration)
    (parents : List (EventStep (Runtime s View))) (occurrence : Nat) (raw : Runtime s View) :
    ActualKey s View := ⟨origin, introduction.route, introduction.binder, parents, occurrence, raw⟩

/-- One assignment has one value at each original actual key. This is scoped
assignment DATA, not a registry of admitted events or a witness of safety. -/
abbrev Assignment (s : Sorts) (View : Type) := ActualKey s View → Joint s

structure Packet (s : Sorts) (View : Type) where
  introduction : Owner
  key : ActualKey s View
  joint : Joint s

def instantiate (assignment : Assignment s View) (introduction : Owner)
    (origin : Declaration) (parents : List (EventStep (Runtime s View)))
    (occurrence : Nat) (raw : Runtime s View) : Packet s View :=
  let key := actualKey introduction origin parents occurrence raw
  ⟨introduction, key, assignment key⟩

def Packet.erase (packet : Packet s View) : Runtime s View := packet.key.raw

theorem instantiated_raw (assignment : Assignment s View) (introduction : Owner)
    (origin : Declaration) (parents : List (EventStep (Runtime s View)))
    (occurrence : Nat) (raw : Runtime s View) :
    (instantiate assignment introduction origin parents occurrence raw).erase = raw := rfl

theorem same_assignment_same_key (assignment : Assignment s View)
    (first second : Owner) (origin₁ origin₂ : Declaration)
    (parents₁ parents₂ : List (EventStep (Runtime s View))) (occurrence₁ occurrence₂ : Nat)
    (raw₁ raw₂ : Runtime s View)
    (same : actualKey first origin₁ parents₁ occurrence₁ raw₁ =
      actualKey second origin₂ parents₂ occurrence₂ raw₂) :
    (instantiate assignment first origin₁ parents₁ occurrence₁ raw₁).joint =
      (instantiate assignment second origin₂ parents₂ occurrence₂ raw₂).joint :=
  congrArg assignment same

theorem different_routes_different_keys (first second : Owner)
    (different : first.route ≠ second.route) (origin : Declaration)
    (parents : List (EventStep (Runtime s View))) (occurrence : Nat) (raw : Runtime s View) :
    actualKey first origin parents occurrence raw ≠ actualKey second origin parents occurrence raw := by
  intro same
  exact different (congrArg ActualKey.route same)

theorem actual_parent_path (assignment : Assignment s View) (introduction : Owner)
    (origin : Declaration) (parents : List (EventStep (Runtime s View)))
    (occurrence : Nat) (raw : Runtime s View) :
    (instantiate assignment introduction origin parents occurrence raw).key.parents = parents := rfl

/-- Description-owned proofs remain outside both the actual key and packet.
Their type is independently supplied by the original proof catalogue. -/
structure Description (s : Sorts) (View Proof : Type) where
  actual : Packet s View
  frame : Nat
  proof : Proof

theorem description_keeps_actual (packet : Packet s View) (frame₁ frame₂ : Nat)
    (proof₁ proof₂ : Proof) :
    (Description.mk packet frame₁ proof₁).actual =
      (Description.mk packet frame₂ proof₂).actual := rfl

/-- An ordered dependent product of the actual original source telescope.
Each value retains its full payload and its structural binder sort only. -/
def ScopeValues (s : Sorts) (View : Type) : List ScopeEntry → Type
  | [] => Unit
  | first :: rest => {payload : Payload s View // payload.atKind first.binder.kind} ×
      ScopeValues s View rest

def ScopeValues.append {first second : List ScopeEntry}
    (left : ScopeValues s View first) (right : ScopeValues s View second) :
    ScopeValues s View (first ++ second) :=
  match first with
  | [] => right
  | _ :: tail => (left.1, ScopeValues.append (first := tail) left.2 right)

/-- A description may vary its proof without replacing the actual packet or
its runtime-field catalogue. No equality of decorated logical witnesses is
claimed, and the proof interpreter may use the new description. -/
def Description.interpret (description : Description s View Proof)
    (meaning : Joint s → Nat → Proof → Event s) : Event s :=
  meaning description.actual.joint description.frame description.proof

structure ScopedPacket (s : Sorts) (View : Type) where
  actual : Packet s View
  prior : ScopeValues s View actual.introduction.telescope

/-- The exact four source binders enclosing a real Lambda parameter entry.
All logical payloads remain present; runtime identity never stores them. -/
def lambdaPrefix (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression)
    (description view : Logical s View) (invocation : Invocation s View)
    (receipt : ReceiptData s View) :
    ScopeValues s View (lambdaEntry context site formal pattern body).telescope :=
  (⟨.logical .description description, rfl⟩,
   ⟨.logical .viewLogic view, rfl⟩,
   ⟨.runtime (.invocation invocation), rfl⟩,
   ⟨.runtime (.receipt receipt), rfl⟩, ())

/-- A local readout constructor at the registered original owner. The old
core does not pass route/parent/occurrence, so these are captured here. This
is not a claim that one such closure covers all core binder occurrences. -/
def ownedReadout (assignment : Assignment s View) (introduction : Owner)
    (origin : Declaration) (parents : List (EventStep (Runtime s View)))
    (occurrence : Nat) : RuntimeReadout s View where
  eta := fun _ _ _ raw => (assignment (actualKey introduction origin parents occurrence raw)).event.eta
  witness := fun _ _ _ raw => (assignment (actualKey introduction origin parents occurrence raw)).event.witness
  scope := fun _ _ _ raw => (assignment (actualKey introduction origin parents occurrence raw)).event.scope
  authority := fun _ _ _ raw => (assignment (actualKey introduction origin parents occurrence raw)).event.authority
  incidence := fun _ _ _ raw => (assignment (actualKey introduction origin parents occurrence raw)).event.incidence
  dictionary := fun _ _ _ raw => (assignment (actualKey introduction origin parents occurrence raw)).event.dictionary

/-- Only the six dynamic fields come from the registered assignment. The
original fiber/eta0 and the actual raw current state are retained separately. -/
def ownedEvent (assignment : Assignment s View) (introduction : Owner)
    (origin : Declaration) (parents : List (EventStep (Runtime s View)))
    (occurrence : Nat) (before : Event s) (raw : Runtime s View) : Event s :=
  let fields := (assignment (actualKey introduction origin parents occurrence raw)).event
  let current := raw.after.getD ⟨before.history, before.current⟩
  {before with
    eta := fields.eta
    witness := fields.witness
    scope := fields.scope
    authority := fields.authority
    incidence := fields.incidence
    dictionary := fields.dictionary
    history := current.history
    current := current.configuration}

theorem owned_readout_computes_event (assignment : Assignment s View) (introduction : Owner)
    (origin : Declaration) (parents : List (EventStep (Runtime s View)))
    (occurrence : Nat) (before : Event s) (raw : Runtime s View)
    (prior : List (Frame (Payload s View))) :
    (ownedReadout assignment introduction origin parents occurrence).event prior before
      introduction.binder raw = ownedEvent assignment introduction origin parents occurrence before raw := rfl

theorem owned_event_keeps_fiber (assignment : Assignment s View) (introduction : Owner)
    (origin : Declaration) (parents : List (EventStep (Runtime s View)))
    (occurrence : Nat) (before : Event s) (raw : Runtime s View) :
    (ownedEvent assignment introduction origin parents occurrence before raw).fiber = before.fiber ∧
    (ownedEvent assignment introduction origin parents occurrence before raw).eta0 = before.eta0 := ⟨rfl, rfl⟩

theorem owned_invocation_current (assignment : Assignment s View) (introduction : Owner)
    (origin : Declaration) (parents : List (EventStep (Runtime s View)))
    (occurrence : Nat) (before : Event s) (raw : Invocation s View) :
    (ownedEvent assignment introduction origin parents occurrence before (.invocation raw)).history = raw.current.history ∧
    (ownedEvent assignment introduction origin parents occurrence before (.invocation raw)).current = raw.current.configuration :=
  ⟨rfl, rfl⟩

inductive EntryData (s : Sorts) : Entry → Type where
  | value (descriptor : s.Descriptor) (value : s.Value) (root : s.Root) : EntryData s .value
  | computation (interface : s.Interface) (carrier : s.Carrier) (root : s.Root) : EntryData s .computation

def EntryData.installed : {entry : Entry} → EntryData s entry → Installed s
  | _, .value descriptor rawValue root => .value descriptor rawValue root
  | _, .computation interface carrier root => .carrier interface carrier root

/-- A retained installed tuple at the actual original formal owner. No V/Car
membership, current-world validity or complete typing certificate is stored. -/
structure Retained (s : Sorts) (registration : EntryRegistration) where
  address : Nat
  data : EntryData s registration.entry
  witness : s.WitnessValue

def Retained.shared (registration : EntryRegistration) (data : Retained s registration) : Shared s :=
  ⟨(registration.context.head?).toList.map (fun binding => (binding.name, data.address)),
    [(data.address, data.data.installed)], data.witness⟩

def Retained.frame (registration : EntryRegistration) (data : Retained s registration)
    (parents : List (EventStep (Payload s View))) (occurrence : Nat) : Frame (Payload s View) :=
  ⟨registration.retainedOwner.binder,
    ⟨.shared (data.shared registration), ⟨parents, occurrence⟩⟩, parents⟩

/-- Apply the existing decoder's actual Shared installation operation. This
is the missing output's local consumer, not a claim that Outcome emits it. -/
theorem retained_installs_actual_object (registration : EntryRegistration)
    (data : Retained s registration) (state : Decoded s View) :
    (state.shared (data.shared registration)).installed data.address = some data.data.installed := by
  simp [Decoded.shared, Retained.shared, put]

theorem retained_preserves_other (registration : EntryRegistration)
    (data : Retained s registration) (state : Decoded s View) (address : Nat)
    (different : address ≠ data.address) :
    (state.shared (data.shared registration)).installed address = state.installed address := by
  simp [Decoded.shared, Retained.shared, put, different]

theorem lambda_retained_binds_formal (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression)
    (data : Retained s (lambdaEntry context site formal pattern body)) (state : Decoded s View) :
    (state.shared (data.shared (lambdaEntry context site formal pattern body))).assignment.binding formal.name =
      some data.address := by
  simp [Decoded.shared, Retained.shared, lambdaEntry, formalContext, put]

theorem retained_frame_preserves_prior (registration : EntryRegistration)
    (data : Retained s registration) (state : Decoded s View) (readout : RuntimeReadout s View)
    (parents : List (EventStep (Payload s View))) (occurrence : Nat) :
    (decodeFrame readout state (data.frame registration parents occurrence)).fixedFrames =
      state.fixedFrames ++ [data.frame registration parents occurrence] := rfl

/-- The actual returned object owns the Value-entry retained tuple. There
is no arbitrary equality between a caller-chosen value and an opaque outcome. -/
structure Returned (s : Sorts) where
  observation : s.Observation
  value : s.Value
  root : s.Root
  after : Current s
  endpoints : List (Endpoint × Object s)
  bindings : List (Name × Nat)

def Returned.outcome (returned : Returned s) : Outcome s :=
  ⟨returned.observation, some (.value returned.value returned.root), returned.after,
    returned.endpoints, returned.bindings⟩

def returnedEvidence (registration : EntryRegistration) (mode : registration.entry = .value)
    (returned : Returned s) (descriptor : s.Descriptor) (address : Nat)
    (witness : s.WitnessValue) : Retained s registration where
  address := address
  data := by rw [mode]; exact .value descriptor returned.value returned.root
  witness := witness

def retainedCarrier (registration : EntryRegistration) (mode : registration.entry = .computation)
    (carrier : s.Carrier) (root : s.Root) (interface : s.Interface) (address : Nat)
    (witness : s.WitnessValue) : Retained s registration where
  address := address
  data := by rw [mode]; exact .computation interface carrier root
  witness := witness

def returnedPrefix (registration : EntryRegistration) (mode : registration.entry = .value)
    (prior : ScopeValues s View registration.telescope) (returned : Returned s) :
    ScopeValues s View registration.retainedOwner.telescope := by
  rw [value_retained_below_return registration mode]
  exact ScopeValues.append prior (⟨.runtime (.returnRebind returned.outcome), rfl⟩, ())

def carrierPrefix (registration : EntryRegistration) (mode : registration.entry = .computation)
    (prior : ScopeValues s View registration.telescope) :
    ScopeValues s View registration.retainedOwner.telescope := by
  rw [computation_retained_below_receipt registration mode]
  exact prior

theorem returned_evidence_object (registration : EntryRegistration) (mode : registration.entry = .value)
    (returned : Returned s) (descriptor : s.Descriptor) (address : Nat) (witness : s.WitnessValue) :
    (returnedEvidence registration mode returned descriptor address witness).data.installed =
      .value descriptor returned.value returned.root := by
  cases registration with
  | mk route telescope site context role receipt entry =>
    cases entry <;> cases mode <;> rfl

theorem carrier_evidence_object {s : Sorts} (registration : EntryRegistration) (mode : registration.entry = .computation)
    (carrier : s.Carrier) (root : s.Root) (interface : s.Interface) (address : Nat) (witness : s.WitnessValue) :
    (retainedCarrier registration mode carrier root interface address witness).data.installed =
      .carrier interface carrier root := by
  cases registration with
  | mk route telescope site context role receipt entry =>
    cases entry <;> cases mode <;> rfl

theorem actual_return_and_retained_object (registration : EntryRegistration)
    (mode : registration.entry = .value) (returned : Returned s) (descriptor : s.Descriptor)
    (address : Nat) (witness : s.WitnessValue) :
    returned.outcome.result = some (.value returned.value returned.root) ∧
    (returnedEvidence registration mode returned descriptor address witness).data.installed =
      .value descriptor returned.value returned.root :=
  ⟨rfl, returned_evidence_object registration mode returned descriptor address witness⟩

/-- Complete source-to-local-consumer application at a genuine Lambda's
Value formal; the source supplies name/role/receipt incidence and the actual
Return supplies the installed value/root. The core emission remains open. -/
theorem lambda_actual_return_install (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) (mode : formal.entry = .value)
    (returned : Returned s) (descriptor : s.Descriptor) (address : Nat) (witness : s.WitnessValue)
    (state : Decoded s View) :
    let registration := lambdaEntry context site formal pattern body
    let evidence := returnedEvidence registration mode returned descriptor address witness
    (state.shared (evidence.shared registration)).installed address =
      some (.value descriptor returned.value returned.root) ∧
    (state.shared (evidence.shared registration)).assignment.binding formal.name = some address := by
  dsimp only
  constructor
  · exact (retained_installs_actual_object
      (lambdaEntry context site formal pattern body)
      (returnedEvidence (lambdaEntry context site formal pattern body) mode returned descriptor address witness) state).trans
        (congrArg some (returned_evidence_object
          (lambdaEntry context site formal pattern body) mode returned descriptor address witness))
  · exact lambda_retained_binds_formal context site formal pattern body _ state

structure ParameterPacket (s : Sorts) (View : Type) (registration : EntryRegistration) where
  prior : ScopeValues s View registration.retainedOwner.telescope
  evidence : Retained s registration

/-- The source constructor builds the actual dependent telescope and the
new retained tuple together. Its `returned` input is an actual Return record,
not an eventual-return restriction on an arbitrary effectful computation. -/
def lambdaValuePacket (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) (mode : formal.entry = .value)
    (description view : Logical s View) (invocation : Invocation s View) (receipt : ReceiptData s View)
    (returned : Returned s) (descriptor : s.Descriptor) (address : Nat) (witness : s.WitnessValue) :
    ParameterPacket s View (lambdaEntry context site formal pattern body) :=
  ⟨returnedPrefix _ mode (lambdaPrefix context site formal pattern body description view invocation receipt) returned,
    returnedEvidence _ mode returned descriptor address witness⟩

/-- Computation entry installs its retained carrier without inventing a
Force/Return event or a returned value. -/
def lambdaComputationPacket (context : Context) (site : Site) (formal : Formal)
    (pattern : Source .pattern) (body : Source .expression) (mode : formal.entry = .computation)
    (description view : Logical s View) (invocation : Invocation s View) (receipt : ReceiptData s View)
    (interface : s.Interface) (address : Nat) (witness : s.WitnessValue) :
    ParameterPacket s View (lambdaEntry context site formal pattern body) :=
  ⟨carrierPrefix _ mode (lambdaPrefix context site formal pattern body description view invocation receipt),
    retainedCarrier _ mode invocation.carrier invocation.carrierRoot interface address witness⟩

/-- Shared catalogue fields retain the whole locally installed tuple. -/
def Retained.decorate (registration : EntryRegistration) (evidence : Retained s registration)
    (event : Event s) : Joint s :=
  ⟨event, evidence.witness, (evidence.shared registration).bindings,
    (evidence.shared registration).installed⟩

theorem retained_catalogue_objects (registration : EntryRegistration)
    (evidence : Retained s registration) (event : Event s) :
    (evidence.decorate registration event).retainedObjects = [(evidence.address, evidence.data.installed)] := rfl

/-! Independent record constructors. Their fields precede admission: there
is no membership, successful execution, reached-history or decoder-image test.
The full original semantic admission of these records remains independent. -/

structure Initial (s : Sorts) (View : Type) where
  invocation : Invocation s View
  callableHole : s.Value × s.Root
  carrierHole : s.Carrier × s.Root
  otherEnvironment : s.Context
  joint : Joint s

structure Response (s : Sorts) (View : Type) where
  original : Invocation s View
  otherEnvironment : s.Context
  request : s.Observation
  operation : Declaration
  rawHandle : s.Continuation
  continuation : s.Continuation
  suffix : s.Context
  response : ResponseData s View
  joint : Joint s

structure RawResume (s : Sorts) (View : Type) where
  original : Invocation s View
  otherEnvironment : s.Context
  request : s.Observation
  operation : Declaration
  originalHandle : s.Continuation
  continuation : s.Continuation
  suffix : s.Context
  response : ResponseData s View
  joint : Joint s

structure FutureUse (s : Sorts) (View : Type) where
  returnedProvider : s.Provider
  returnedValue : s.Value
  returnedRoot : s.Root
  port : Endpoint
  invocation : Invocation s View
  originalContext : s.Context
  joint : Joint s

inductive HistoryRecord (s : Sorts) (View : Type) where
  | initial (data : Initial s View)
  | response (data : Response s View)
  | rawResume (data : RawResume s View)
  | futureUse (data : FutureUse s View)

inductive RawRecord (s : Sorts) (View : Type) where
  | initial (invocation : Invocation s View) (callable : s.Value × s.Root)
      (carrier : s.Carrier × s.Root) (otherEnvironment : s.Context)
  | response (original : Invocation s View) (otherEnvironment : s.Context)
      (request : s.Observation) (operation : Declaration) (handle continuation : s.Continuation)
      (suffix : s.Context) (response : ResponseData s View)
  | rawResume (original : Invocation s View) (otherEnvironment : s.Context)
      (request : s.Observation) (operation : Declaration) (handle continuation : s.Continuation)
      (suffix : s.Context) (response : ResponseData s View)
  | futureUse (provider : s.Provider) (value : s.Value) (root : s.Root) (port : Endpoint)
      (invocation : Invocation s View) (originalContext : s.Context)

def HistoryRecord.raw : HistoryRecord s View → RawRecord s View
  | .initial d => .initial d.invocation d.callableHole d.carrierHole d.otherEnvironment
  | .response d => .response d.original d.otherEnvironment d.request d.operation d.rawHandle d.continuation d.suffix d.response
  | .rawResume d => .rawResume d.original d.otherEnvironment d.request d.operation d.originalHandle d.continuation d.suffix d.response
  | .futureUse d => .futureUse d.returnedProvider d.returnedValue d.returnedRoot d.port d.invocation d.originalContext

def HistoryRecord.joint : HistoryRecord s View → Joint s
  | .initial d => d.joint | .response d => d.joint | .rawResume d => d.joint | .futureUse d => d.joint

def RawRecord.decorate (joint : Joint s) : RawRecord s View → HistoryRecord s View
  | .initial invocation callable carrier others => .initial ⟨invocation, callable, carrier, others, joint⟩
  | .response original others request operation handle continuation suffix responseData =>
      .response ⟨original, others, request, operation, handle, continuation, suffix, responseData, joint⟩
  | .rawResume original others request operation handle continuation suffix responseData =>
      .rawResume ⟨original, others, request, operation, handle, continuation, suffix, responseData, joint⟩
  | .futureUse provider value root port invocation context =>
      .futureUse ⟨provider, value, root, port, invocation, context, joint⟩

theorem record_roundtrip (record : HistoryRecord s View) :
    record.raw.decorate record.joint = record := by cases record <;> rfl

theorem raw_record_roundtrip (record : RawRecord s View) (joint : Joint s) :
    (record.decorate joint).raw = record := by cases record <;> rfl

theorem record_keeps_joint (record : RawRecord s View) (joint : Joint s) :
    (record.decorate joint).joint = joint := by cases record <;> rfl

theorem dynamic_fields_distinguishable (record : RawRecord s View) (first second : Joint s)
    (different : first ≠ second) : record.decorate first ≠ record.decorate second := by
  intro same
  exact different (by simpa only [record_keeps_joint] using congrArg HistoryRecord.joint same)

theorem raw_erasure_independent (record : RawRecord s View) (first second : Joint s) :
    (record.decorate first).raw = (record.decorate second).raw := by
  rw [raw_record_roundtrip, raw_record_roundtrip]

/-- Coverage of the DATA grammar, explicitly not a theorem that every
original independently admitted semantic history has been interpreted. -/
theorem record_data_coverage (record : HistoryRecord s View) :
    ∃ (raw : RawRecord s View) (joint : Joint s), record = raw.decorate joint := ⟨record.raw, record.joint, (record_roundtrip record).symm⟩

/-- Complete history-record identity, including request/handle/suffix operands
which the current core Runtime.response does not yet carry. No latest-parent
selection or reached-history predicate is used. -/
structure HistoryStep (s : Sorts) (View : Type) where
  origin : Declaration
  route : Route
  binder : Binder
  occurrence : Nat
  raw : RawRecord s View

structure RecordKey (s : Sorts) (View : Type) where
  step : HistoryStep s View
  parents : List (HistoryStep s View)

abbrev RecordAssignment (s : Sorts) (View : Type) := RecordKey s View → Joint s

def recordKey (introduction : Owner) (origin : Declaration)
    (parents : List (HistoryStep s View)) (occurrence : Nat) (raw : RawRecord s View) : RecordKey s View :=
  ⟨⟨origin, introduction.route, introduction.binder, occurrence, raw⟩, parents⟩

def instantiateRecord (assignment : RecordAssignment s View) (introduction : Owner)
    (origin : Declaration) (parents : List (HistoryStep s View))
    (occurrence : Nat) (raw : RawRecord s View) : HistoryRecord s View :=
  raw.decorate (assignment (recordKey introduction origin parents occurrence raw))

theorem original_record_operands (assignment : RecordAssignment s View) (introduction : Owner)
    (origin : Declaration) (parents : List (HistoryStep s View))
    (occurrence : Nat) (raw : RawRecord s View) :
    (instantiateRecord assignment introduction origin parents occurrence raw).raw = raw :=
  raw_record_roundtrip raw _

theorem record_keeps_full_parent_path (introduction : Owner) (origin : Declaration)
    (parents : List (HistoryStep s View)) (occurrence : Nat) (raw : RawRecord s View) :
    (recordKey introduction origin parents occurrence raw).parents = parents := rfl

theorem record_assignment_shared (assignment : RecordAssignment s View) (first second : Owner)
    (origin₁ origin₂ : Declaration) (parents₁ parents₂ : List (HistoryStep s View))
    (occurrence₁ occurrence₂ : Nat) (raw₁ raw₂ : RawRecord s View)
    (same : recordKey first origin₁ parents₁ occurrence₁ raw₁ =
      recordKey second origin₂ parents₂ occurrence₂ raw₂) :
    (instantiateRecord assignment first origin₁ parents₁ occurrence₁ raw₁).joint =
      (instantiateRecord assignment second origin₂ parents₂ occurrence₂ raw₂).joint := by
  simp only [instantiateRecord, record_keeps_joint]
  exact congrArg assignment same

/-- The old runtime carrier is an erasure of these richer original records.
Request/operation/handle/suffix and returned-provider ownership are retained
by RecordKey; they cannot be reconstructed from this projection alone. -/
def RawRecord.runtime : RawRecord s View → Runtime s View
  | .initial invocation _ _ _ => .invocation invocation
  | .response _ _ _ _ _ _ _ responseData => .response responseData
  | .rawResume _ _ _ _ _ _ _ responseData => .response responseData
  | .futureUse _ _ _ _ invocation _ => .invocation invocation

theorem different_operations_same_runtime (original : Invocation s View)
    (others : s.Context) (request : s.Observation) (handle continuation : s.Continuation)
    (suffix : s.Context) (responseData : ResponseData s View) :
    let first := RawRecord.response original others request 0 handle continuation suffix responseData
    let second := RawRecord.response original others request 1 handle continuation suffix responseData
    first.runtime = second.runtime ∧ first ≠ second := by
  dsimp only
  constructor
  · rfl
  · intro same
    cases same

/-- Registration is taken from the actual source builder, with its occurrence
route. The index selects a declaration, not an observed execution or an
admitted-domain member. The only check is structural binder sort; no original
admission predicate, anchor presence or safety condition is consulted. Failure
means that source has no such declaration of that structural sort. -/
def sourceRecord (assignment : RecordAssignment s View) (context : Context)
    (source : Source category) (index : Nat) (origin : Declaration)
    (parents : List (HistoryStep s View)) (occurrence : Nat) (raw : RawRecord s View) :
    Option (HistoryRecord s View) := do
  let introduction ← ((sourceOwners context source).filter
    (fun introduced => introduced.lifetime == .actualEvent))[index]?
  if introduction.binder.kind = raw.runtime.kind then
    pure (instantiateRecord assignment introduction origin parents occurrence raw)
  else none

theorem source_lambda_record (assignment : RecordAssignment s View) (context : Context)
    (site : Site) (formal : Formal) (pattern : Source .pattern) (body : Source .expression)
    (origin : Declaration) (parents : List (HistoryStep s View)) (occurrence : Nat)
    (raw : RawRecord s View) (kind : raw.runtime.kind = .invocation) :
    sourceRecord assignment context (.lambda ⟨site, none⟩ formal pattern body) 0
      origin parents occurrence raw =
      some (instantiateRecord assignment (lambdaInvocationOwner site formal) origin parents occurrence raw) := by
  simp only [sourceRecord, sourceOwners, sourceRules]
  change (if BinderKind.invocation = raw.runtime.kind then some _ else none) = _
  rw [kind]
  rfl

/-! Complete position inventory and route uniqueness for arbitrary rule
programs. This proof does not assume that sourceRules omits any constructor. -/
mutual
def treeRoutes (route : Route) : RuleTree → List Route
  | .rule _ _ _ _ children => route :: forestRoutes (route ++ [0]) children
  | .existsE _ body | .forallE _ body | .executionE _ body | .sharedE _ body
  | .initializerE _ body | .publishGroup _ body | .atPublication _ body
  | .aliasPublication _ _ body => route :: treeRoutes (route ++ [0]) body
  | .choice _ left right => route :: (treeRoutes (route ++ [0]) left ++ treeRoutes (route ++ [3]) right)
def forestRoutes (route : Route) : RuleForest → List Route
  | .nil => []
  | .cons head tail => treeRoutes route head ++ forestRoutes (route ++ [1]) tail
end

/-- Every generated relative path avoids reserved retained-evidence tag 2. -/
def Routed (route : Route) (paths : List Route) : Prop :=
  ∀ path ∈ paths, ∃ suffix, path = route ++ suffix ∧ 2 ∉ suffix

theorem routed_root (route : Route) {paths : List Route} (rest : Routed route paths) :
    Routed route (route :: paths) := by
  intro path present
  rcases List.mem_cons.mp present with same | inside
  · subst path; exact ⟨[], by simp, by simp⟩
  · exact rest path inside

theorem routed_append {route : Route} {left right : List Route}
    (first : Routed route left) (second : Routed route right) : Routed route (left ++ right) := by
  intro path present
  rcases List.mem_append.mp present with inside | inside
  · exact first path inside
  · exact second path inside

theorem routed_step {route : Route} {tag : Nat} {paths : List Route}
    (ordinary : tag ≠ 2) (rest : Routed (route ++ [tag]) paths) : Routed route paths := by
  intro path present
  obtain ⟨suffix, same, fresh⟩ := rest path present
  refine ⟨tag :: suffix, ?_, ?_⟩
  · simpa only [List.append_assoc, List.singleton_append] using same
  · simp only [List.mem_cons, not_or]
    exact ⟨Ne.symm ordinary, fresh⟩

mutual
theorem tree_routes_routed (route : Route) (tree : RuleTree) : Routed route (treeRoutes route tree) := by
  cases tree with
  | rule rule site context premises children =>
    exact routed_root route (routed_step (by decide) (forest_routes_routed (route ++ [0]) children))
  | existsE binder body =>
    exact routed_root route (routed_step (by decide) (tree_routes_routed (route ++ [0]) body))
  | forallE binder body =>
    exact routed_root route (routed_step (by decide) (tree_routes_routed (route ++ [0]) body))
  | executionE binder body =>
    exact routed_root route (routed_step (by decide) (tree_routes_routed (route ++ [0]) body))
  | sharedE binder body =>
    exact routed_root route (routed_step (by decide) (tree_routes_routed (route ++ [0]) body))
  | initializerE site body =>
    exact routed_root route (routed_step (by decide) (tree_routes_routed (route ++ [0]) body))
  | publishGroup bindings body =>
    exact routed_root route (routed_step (by decide) (tree_routes_routed (route ++ [0]) body))
  | atPublication binding body =>
    exact routed_root route (routed_step (by decide) (tree_routes_routed (route ++ [0]) body))
  | aliasPublication first last body =>
    exact routed_root route (routed_step (by decide) (tree_routes_routed (route ++ [0]) body))
  | choice site left right =>
    exact routed_root route (routed_append
      (routed_step (by decide) (tree_routes_routed (route ++ [0]) left))
      (routed_step (by decide) (tree_routes_routed (route ++ [3]) right)))
theorem forest_routes_routed (route : Route) (forest : RuleForest) : Routed route (forestRoutes route forest) := by
  cases forest with
  | nil => intro path present; cases present
  | cons head tail =>
    exact routed_append (tree_routes_routed route head)
      (routed_step (by decide) (forest_routes_routed (route ++ [1]) tail))
end

/-- Distinct edge tags separate their entire descendant subtrees, not just
one immediate child fixture. -/
theorem route_edges_separate (route left right : Route) (first second : Nat)
    (different : first ≠ second) :
    (route ++ [first]) ++ left ≠ (route ++ [second]) ++ right := by
  intro same
  have tails : first :: left = second :: right := List.append_cancel_left
    (by simpa only [List.append_assoc, List.singleton_append] using same)
  exact different (List.cons.inj tails).1

theorem route_extension_not_root (route suffix : Route) (tag : Nat) :
    (route ++ [tag]) ++ suffix ≠ route := by
  intro same
  have expanded : route ++ (tag :: suffix) = route ++ [] := by
    simpa only [List.append_assoc, List.singleton_append, List.append_nil] using same
  have tails : tag :: suffix = [] := List.append_cancel_left expanded
  cases tails

theorem routed_not_root {route : Route} {tag : Nat} {paths : List Route}
    (under : Routed (route ++ [tag]) paths) : route ∉ paths := by
  intro present
  obtain ⟨suffix, same, _⟩ := under route present
  exact route_extension_not_root route suffix tag same.symm

theorem routed_edges_disjoint {route : Route} {first second : Nat} {left right : List Route}
    (different : first ≠ second) (one : Routed (route ++ [first]) left)
    (two : Routed (route ++ [second]) right) :
    ∀ a ∈ left, ∀ b ∈ right, a ≠ b := by
  intro a insideA b insideB same
  obtain ⟨leftTail, leftEq, _⟩ := one a insideA
  obtain ⟨rightTail, rightEq, _⟩ := two b insideB
  exact route_edges_separate route leftTail rightTail first second different
    (leftEq.symm.trans (same.trans rightEq))

/-- A tree's own root or a descent/choice edge begins every tree address.
Sibling tag 1 can only be traversed after entering a forest. -/
theorem tree_route_shape (route : Route) (tree : RuleTree) (path : Route)
    (present : path ∈ treeRoutes route tree) :
    path = route ∨ (∃ suffix, path = (route ++ [0]) ++ suffix) ∨
      (∃ suffix, path = (route ++ [3]) ++ suffix) := by
  cases tree with
  | rule rule site context premises children =>
    rcases List.mem_cons.mp present with same | inside
    · exact Or.inl same
    · obtain ⟨suffix, same, _⟩ := forest_routes_routed (route ++ [0]) children path inside
      exact Or.inr (Or.inl ⟨suffix, same⟩)
  | existsE binder body =>
    rcases List.mem_cons.mp present with same | inside
    · exact Or.inl same
    · obtain ⟨suffix, same, _⟩ := tree_routes_routed (route ++ [0]) body path inside
      exact Or.inr (Or.inl ⟨suffix, same⟩)
  | forallE binder body =>
    rcases List.mem_cons.mp present with same | inside
    · exact Or.inl same
    · obtain ⟨suffix, same, _⟩ := tree_routes_routed (route ++ [0]) body path inside
      exact Or.inr (Or.inl ⟨suffix, same⟩)
  | executionE binder body =>
    rcases List.mem_cons.mp present with same | inside
    · exact Or.inl same
    · obtain ⟨suffix, same, _⟩ := tree_routes_routed (route ++ [0]) body path inside
      exact Or.inr (Or.inl ⟨suffix, same⟩)
  | sharedE binder body =>
    rcases List.mem_cons.mp present with same | inside
    · exact Or.inl same
    · obtain ⟨suffix, same, _⟩ := tree_routes_routed (route ++ [0]) body path inside
      exact Or.inr (Or.inl ⟨suffix, same⟩)
  | initializerE site body =>
    rcases List.mem_cons.mp present with same | inside
    · exact Or.inl same
    · obtain ⟨suffix, same, _⟩ := tree_routes_routed (route ++ [0]) body path inside
      exact Or.inr (Or.inl ⟨suffix, same⟩)
  | publishGroup bindings body =>
    rcases List.mem_cons.mp present with same | inside
    · exact Or.inl same
    · obtain ⟨suffix, same, _⟩ := tree_routes_routed (route ++ [0]) body path inside
      exact Or.inr (Or.inl ⟨suffix, same⟩)
  | atPublication binding body =>
    rcases List.mem_cons.mp present with same | inside
    · exact Or.inl same
    · obtain ⟨suffix, same, _⟩ := tree_routes_routed (route ++ [0]) body path inside
      exact Or.inr (Or.inl ⟨suffix, same⟩)
  | aliasPublication first last body =>
    rcases List.mem_cons.mp present with same | inside
    · exact Or.inl same
    · obtain ⟨suffix, same, _⟩ := tree_routes_routed (route ++ [0]) body path inside
      exact Or.inr (Or.inl ⟨suffix, same⟩)
  | choice site left right =>
    rcases List.mem_cons.mp present with same | inside
    · exact Or.inl same
    · rcases List.mem_append.mp inside with inLeft | inRight
      · obtain ⟨suffix, same, _⟩ := tree_routes_routed (route ++ [0]) left path inLeft
        exact Or.inr (Or.inl ⟨suffix, same⟩)
      · obtain ⟨suffix, same, _⟩ := tree_routes_routed (route ++ [3]) right path inRight
        exact Or.inr (Or.inr ⟨suffix, same⟩)

theorem tree_sibling_separation (route : Route) (tree : RuleTree) (suffix : Route) :
    (route ++ [1]) ++ suffix ∉ treeRoutes route tree := by
  intro present
  rcases tree_route_shape route tree _ present with same | ⟨tail, same⟩ | ⟨tail, same⟩
  · exact route_extension_not_root route suffix 1 same
  · exact route_edges_separate route suffix tail 1 0 (by decide) same
  · exact route_edges_separate route suffix tail 1 3 (by decide) same

theorem root_cons_nodup {route : Route} {tag : Nat} {paths : List Route}
    (under : Routed (route ++ [tag]) paths) (unique : paths.Nodup) :
    (route :: paths).Nodup := List.nodup_cons.mpr ⟨routed_not_root under, unique⟩

mutual
theorem tree_routes_nodup (route : Route) (tree : RuleTree) : (treeRoutes route tree).Nodup := by
  cases tree with
  | rule rule site context premises children =>
    exact root_cons_nodup (forest_routes_routed (route ++ [0]) children)
      (forest_routes_nodup (route ++ [0]) children)
  | existsE binder body =>
    exact root_cons_nodup (tree_routes_routed (route ++ [0]) body)
      (tree_routes_nodup (route ++ [0]) body)
  | forallE binder body =>
    exact root_cons_nodup (tree_routes_routed (route ++ [0]) body)
      (tree_routes_nodup (route ++ [0]) body)
  | executionE binder body =>
    exact root_cons_nodup (tree_routes_routed (route ++ [0]) body)
      (tree_routes_nodup (route ++ [0]) body)
  | sharedE binder body =>
    exact root_cons_nodup (tree_routes_routed (route ++ [0]) body)
      (tree_routes_nodup (route ++ [0]) body)
  | initializerE site body =>
    exact root_cons_nodup (tree_routes_routed (route ++ [0]) body)
      (tree_routes_nodup (route ++ [0]) body)
  | publishGroup bindings body =>
    exact root_cons_nodup (tree_routes_routed (route ++ [0]) body)
      (tree_routes_nodup (route ++ [0]) body)
  | atPublication binding body =>
    exact root_cons_nodup (tree_routes_routed (route ++ [0]) body)
      (tree_routes_nodup (route ++ [0]) body)
  | aliasPublication first last body =>
    exact root_cons_nodup (tree_routes_routed (route ++ [0]) body)
      (tree_routes_nodup (route ++ [0]) body)
  | choice site left right =>
    apply List.nodup_cons.mpr
    constructor
    · exact List.not_mem_append (routed_not_root (tree_routes_routed (route ++ [0]) left))
        (routed_not_root (tree_routes_routed (route ++ [3]) right))
    · exact List.nodup_append.mpr ⟨tree_routes_nodup (route ++ [0]) left,
        tree_routes_nodup (route ++ [3]) right,
        routed_edges_disjoint (by decide) (tree_routes_routed (route ++ [0]) left)
          (tree_routes_routed (route ++ [3]) right)⟩
theorem forest_routes_nodup (route : Route) (forest : RuleForest) : (forestRoutes route forest).Nodup := by
  cases forest with
  | nil => exact List.nodup_nil
  | cons head tail =>
    apply List.nodup_append.mpr
    refine ⟨tree_routes_nodup route head, forest_routes_nodup (route ++ [1]) tail, ?_⟩
    intro a inHead b inTail same
    obtain ⟨suffix, atTail, _⟩ := forest_routes_routed (route ++ [1]) tail b inTail
    exact tree_sibling_separation route head suffix (by rw [← atTail, ← same]; exact inHead)
end

theorem binder_owner_routes_sublist (route : Route) (scope : List ScopeEntry) (binder : Binder) :
    List.Sublist ((binderOwner route scope binder).map Owner.route) [route] := by
  unfold binderOwner
  split
  · exact List.Sublist.refl _
  · split
    · exact List.Sublist.refl _
    · split
      · exact List.Sublist.refl _
      · exact List.nil_sublist _

mutual
theorem owner_routes_sublist (route : Route) (scope : List ScopeEntry) (tree : RuleTree) :
    List.Sublist ((owners route scope tree).map Owner.route) (treeRoutes route tree) := by
  cases tree with
  | rule rule site context premises children =>
    exact (forest_owner_routes_sublist (route ++ [0]) scope children).cons route
  | existsE binder body =>
    simpa only [owners, List.map_append, treeRoutes, List.singleton_append] using
      (binder_owner_routes_sublist route scope binder).append
        (owner_routes_sublist (route ++ [0]) (extendScope scope route binder) body)
  | forallE binder body =>
    simpa only [owners, List.map_append, treeRoutes, List.singleton_append] using
      (binder_owner_routes_sublist route scope binder).append
        (owner_routes_sublist (route ++ [0]) (extendScope scope route binder) body)
  | executionE binder body =>
    simpa only [owners, List.map_append, treeRoutes, List.singleton_append] using
      (binder_owner_routes_sublist route scope binder).append
        (owner_routes_sublist (route ++ [0]) (extendScope scope route binder) body)
  | sharedE binder body =>
    simpa only [owners, List.map_append, treeRoutes, List.singleton_append] using
      (binder_owner_routes_sublist route scope binder).append
        (owner_routes_sublist (route ++ [0]) (extendScope scope route binder) body)
  | initializerE site body =>
    exact (owner_routes_sublist (route ++ [0]) scope body).cons route
  | publishGroup bindings body =>
    exact (owner_routes_sublist (route ++ [0]) scope body).cons route
  | atPublication binding body =>
    exact (owner_routes_sublist (route ++ [0]) scope body).cons route
  | aliasPublication first last body =>
    exact (owner_routes_sublist (route ++ [0]) scope body).cons route
  | choice site left right =>
    simpa only [owners, List.map_append, treeRoutes, List.singleton_append] using
      ((owner_routes_sublist (route ++ [0]) scope left).append
        (owner_routes_sublist (route ++ [3]) scope right)).cons route
theorem forest_owner_routes_sublist (route : Route) (scope : List ScopeEntry) (forest : RuleForest) :
    List.Sublist ((forestOwners route scope forest).map Owner.route) (forestRoutes route forest) := by
  cases forest with
  | nil => exact List.Sublist.refl _
  | cons head tail =>
    simpa only [forestOwners, List.map_append, forestRoutes] using
      (owner_routes_sublist route scope head).append
        (forest_owner_routes_sublist (route ++ [1]) scope tail)
end

theorem entry_at_routes_sublist (route : Route) (scope : List ScopeEntry) (rule : Rule)
    (site : Site) (context : Context) (premises : List Premise) :
    List.Sublist ((entryAt route scope rule site context premises).toList.map EntryRegistration.route) [route] := by
  unfold entryAt
  split
  · exact List.nil_sublist _
  · cases role : atomOfKind .sourceFormalRole premises with
    | none => exact List.nil_sublist _
    | some roleData =>
      cases receipt : atomOfKind .receiptFormation premises with
      | none => exact List.nil_sublist _
      | some receiptData =>
        dsimp only [Bind.bind, Option.bind]
        cases entry : roleData.entry with
        | none => exact List.nil_sublist _
        | some actualEntry => exact List.Sublist.refl _

mutual
theorem entry_routes_sublist (route : Route) (scope : List ScopeEntry) (tree : RuleTree) :
    List.Sublist ((entries route scope tree).map EntryRegistration.route) (treeRoutes route tree) := by
  cases tree with
  | rule rule site context premises children =>
    simpa only [entries, List.map_append, treeRoutes, List.singleton_append] using
      (entry_at_routes_sublist route scope rule site context premises).append
        (forest_entry_routes_sublist (route ++ [0]) scope children)
  | existsE binder body =>
    exact (entry_routes_sublist (route ++ [0]) (extendScope scope route binder) body).cons route
  | forallE binder body =>
    exact (entry_routes_sublist (route ++ [0]) (extendScope scope route binder) body).cons route
  | executionE binder body =>
    exact (entry_routes_sublist (route ++ [0]) (extendScope scope route binder) body).cons route
  | sharedE binder body =>
    exact (entry_routes_sublist (route ++ [0]) (extendScope scope route binder) body).cons route
  | initializerE site body =>
    exact (entry_routes_sublist (route ++ [0]) scope body).cons route
  | publishGroup bindings body =>
    exact (entry_routes_sublist (route ++ [0]) scope body).cons route
  | atPublication binding body =>
    exact (entry_routes_sublist (route ++ [0]) scope body).cons route
  | aliasPublication first last body =>
    exact (entry_routes_sublist (route ++ [0]) scope body).cons route
  | choice site left right =>
    simpa only [entries, List.map_append, treeRoutes, List.singleton_append] using
      ((entry_routes_sublist (route ++ [0]) scope left).append
        (entry_routes_sublist (route ++ [3]) scope right)).cons route
theorem forest_entry_routes_sublist (route : Route) (scope : List ScopeEntry) (forest : RuleForest) :
    List.Sublist ((forestEntries route scope forest).map EntryRegistration.route) (forestRoutes route forest) := by
  cases forest with
  | nil => exact List.Sublist.refl _
  | cons head tail =>
    simpa only [forestEntries, List.map_append, forestRoutes] using
      (entry_routes_sublist route scope head).append
        (forest_entry_routes_sublist (route ++ [1]) scope tail)
end

theorem owner_routes_nodup (route : Route) (scope : List ScopeEntry) (tree : RuleTree) :
    ((owners route scope tree).map Owner.route).Nodup :=
  List.Nodup.sublist (owner_routes_sublist route scope tree) (tree_routes_nodup route tree)

theorem forest_owner_routes_nodup (route : Route) (scope : List ScopeEntry) (forest : RuleForest) :
    ((forestOwners route scope forest).map Owner.route).Nodup :=
  List.Nodup.sublist (forest_owner_routes_sublist route scope forest) (forest_routes_nodup route forest)

theorem entry_routes_nodup (route : Route) (scope : List ScopeEntry) (tree : RuleTree) :
    ((entries route scope tree).map EntryRegistration.route).Nodup :=
  List.Nodup.sublist (entry_routes_sublist route scope tree) (tree_routes_nodup route tree)

theorem forest_entry_routes_nodup (route : Route) (scope : List ScopeEntry) (forest : RuleForest) :
    ((forestEntries route scope forest).map EntryRegistration.route).Nodup :=
  List.Nodup.sublist (forest_entry_routes_sublist route scope forest) (forest_routes_nodup route forest)

theorem retained_slot_separate (route suffix : Route) (tree : RuleTree) :
    (route ++ [2]) ++ suffix ∉ treeRoutes route tree := by
  intro present
  obtain ⟨tail, same, fresh⟩ := tree_routes_routed route tree _ present
  have tails : 2 :: suffix = tail := List.append_cancel_left
    (by simpa only [List.append_assoc, List.singleton_append] using same)
  exact fresh (tails ▸ List.mem_cons_self)

theorem forest_retained_slot_separate (route suffix : Route) (forest : RuleForest) :
    (route ++ [2]) ++ suffix ∉ forestRoutes route forest := by
  intro present
  obtain ⟨tail, same, fresh⟩ := forest_routes_routed route forest _ present
  have tails : 2 :: suffix = tail := List.append_cancel_left
    (by simpa only [List.append_assoc, List.singleton_append] using same)
  exact fresh (tails ▸ List.mem_cons_self)

/-- Reserved tag 2 is separated at every depth, including a retained field
under a parameter entry far below the traversal root. -/
theorem reserved_tag_separation (route before after : Route) (tree : RuleTree) :
    ((route ++ before) ++ [2]) ++ after ∉ treeRoutes route tree := by
  intro present
  obtain ⟨tail, same, fresh⟩ := tree_routes_routed route tree _ present
  have tails : before ++ (2 :: after) = tail := List.append_cancel_left
    (by simpa only [List.append_assoc, List.singleton_append] using same)
  exact fresh (tails ▸ List.mem_append_right before List.mem_cons_self)

theorem forest_reserved_tag_separation (route before after : Route) (forest : RuleForest) :
    ((route ++ before) ++ [2]) ++ after ∉ forestRoutes route forest := by
  intro present
  obtain ⟨tail, same, fresh⟩ := forest_routes_routed route forest _ present
  have tails : before ++ (2 :: after) = tail := List.append_cancel_left
    (by simpa only [List.append_assoc, List.singleton_append] using same)
  exact fresh (tails ▸ List.mem_append_right before List.mem_cons_self)

theorem retained_owner_route (entry : EntryRegistration) :
    entry.retainedOwner.route = entry.route ++ [2] := rfl

theorem retained_owner_separate_from_tree (route : Route) (scope : List ScopeEntry)
    (tree : RuleTree) (entry : EntryRegistration) (present : entry ∈ entries route scope tree) :
    entry.retainedOwner.route ∉ treeRoutes route tree := by
  have mapped := List.mem_map_of_mem (f := EntryRegistration.route) present
  have located := List.Sublist.mem mapped (entry_routes_sublist route scope tree)
  obtain ⟨suffix, same, _⟩ := tree_routes_routed route tree _ located
  rw [retained_owner_route, same]
  simpa only [List.append_nil] using reserved_tag_separation route suffix [] tree

theorem distinct_retained_routes (first second : EntryRegistration)
    (different : first.route ≠ second.route) : first.retainedOwner.route ≠ second.retainedOwner.route := by
  intro same
  exact different (List.append_cancel_right same)

theorem different_record_routes_different_keys (first second : Owner)
    (different : first.route ≠ second.route) (origin : Declaration)
    (parents : List (HistoryStep s View)) (occurrence : Nat) (raw : RawRecord s View) :
    recordKey first origin parents occurrence raw ≠ recordKey second origin parents occurrence raw := by
  intro same
  exact different (congrArg (fun key : RecordKey s View => key.step.route) same)

end YulangClosure.OriginalSourceEvents
