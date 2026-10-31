import YulangClosure.CollectedDefinitionBridgeR79

/-!
R80 constructs the existing R66 Incidence, rather than assuming it. The aligned
choice and native record reads share exactly one plan, formal, origin, recipe,
receipt and permission. Primitive checks are executable finite record checks;
no sourceProbe/ownerSelection/Incidence/Root success is supplied by a caller.
This is a finite record construction, not authenticated Rust extraction.
-/
namespace YulangClosure.ConstructedSourceIncidenceR80

open SourceInternalContextR55 ProviderNativeContextR57 SourceInternalChoiceR77

variable {S T : Type} [DecidableEq S] [DecidableEq T]

abbrev Source (S T : Type) := OccurrenceQualifiedConsumerR66.Source S T
abbrev Inventory (S T : Type) := OccurrenceQualifiedFactReadersR65.Inventory S T

structure Records (S T : Type) where
  permission : SourceInternalContextR55.Permission (Key S T)
  root : T
  child : T
  fact : Fact

/-- Annotation and row remain original permission coordinates. Neither is a
canonical representative, nor the Apply checking occurrence. -/
def request (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Choice s u receiving target) (annotation row : Key S T) :
    OccurrenceQualifiedConsumerR66.Request S T :=
  ⟨use u, receiving, target, c.origin.registration, c.origin.lambda, annotation, row⟩

def projected {s : Source S T} {u : Use Nat (Key S T)}
    {receiving target : Key S T} (c : Choice s u receiving target) (d : Records S T) :
    InternalPermissionIncidenceR45.Probe Nat (Key S T) T Fact :=
  ⟨formal c.formal, d.root, c.recipe.rootComponent, construction c.origin,
    permission d.permission, plan c.plan, receipt c.receipt, d.fact, d.child⟩

/-- Read the owner-indexed registration, permission and native Function child.
The root comes from the Lambda recipe component, never Formal.nativeRoot. -/
def readRecords (s : Source S T) (u : Use Nat (Key S T))
    (receiving target : Key S T) (c : Choice s u receiving target) : Option (Records S T) := do
  let (_, root) ← (SourceInternalContextR55.internalInputs s).formals c.origin.registration
  let p ← unique (fun p => decide (p.registration = c.origin.registration)) s.permissions
  let child ← (SourceInternalContextR55.internalInputs s).positiveFunctionChild c.origin.function
  let fact ← c.receipt.fact
  pure ⟨p, root, child, fact⟩

/-- Primitive native records and field identities. These checks are evaluated
inside construct. They are not a new incidence relation and are never exported
as a replacement for R66 Incidence. Slot-0 and slot-2 use R65's complete-key
readers, so duplicate provenance competitors cannot disappear by FactId filtering.
-/
def PrimitiveRecords (s : Source S T) (inventory : Inventory S T)
    (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T) : Prop :=
  let e := SourceInternalContextR55.internalInputs s
  e.formals c.origin.registration = some (formal c.formal, d.root) ∧
  e.source.formals[c.origin.registration]? = some (formal c.formal) ∧
  e.constructions.filter (fun x => x.registration == c.origin.registration) = [construction c.origin] ∧
  e.permissions.filter (fun x => x.registration == c.origin.registration) = [permission d.permission] ∧
  e.receipts.filter (fun x => x.use == use u) = [receipt c.receipt] ∧
  ComputationPermissionEntryR39.sourceLambda e.source (formal c.formal) =
    some (c.origin.lambda, c.formal.parameter) ∧
  OccurrenceQualifiedFactReadersR65.routeFact inventory u.occurrence d.fact =
    some (u.occurrence, c.plan.targetRoot, c.plan.useValue) ∧
  OccurrenceQualifiedFactReadersR65.lambdaFact inventory c.origin.lambda =
    some (c.origin.function, d.root) ∧
  e.positiveFunctionChild c.origin.function = some d.child ∧
  e.negativeEntry d.child = some c.origin.entryEffect ∧
  e.lambdaRecipe c.origin.lambda = some (c.origin.registration, c.recipe.rootComponent) ∧
  e.componentTerm c.plan.targetRootComponent = some c.plan.targetRoot ∧
  e.componentTerm c.plan.useValueComponent = some c.plan.useValue ∧
  c.formal.owner = target ∧ c.formal.role = .computation ∧
  c.formal.entryEffect = some c.origin.entryEffect ∧ d.root = c.plan.targetRoot ∧
  c.receipt.use = u ∧ c.receipt.fact = some d.fact ∧
  d.permission.registration = c.origin.registration ∧
  d.permission.parameterPosition = c.formal.recipePosition ∧
  d.permission.formal = c.formal.parameter ∧ d.permission.sourceOwner = c.formal.owner ∧
  d.permission.occurrence = c.origin.lambda ∧ d.permission.scope = c.formal.scope ∧
  d.permission.annotationPosition = annotation ∧ d.permission.sourceRow = row ∧
  d.permission.entryEffect = c.origin.entryEffect ∧ d.permission.concrete ≠ []

instance (s : Source S T) (inventory : Inventory S T)
    (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T) :
    Decidable (PrimitiveRecords s inventory u receiving target c d annotation row) := by
  dsimp only [PrimitiveRecords]
  infer_instance

/-- The three fields required by the original R66 certificate are derived
jointly on the same projected probe and permission. -/
theorem primitive_records_derive_fields (s : Source S T) (inventory : Inventory S T)
    (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T)
    (checked : PrimitiveRecords s inventory u receiving target c d annotation row) :
    InternalPermissionIncidenceR45.OwnerReads
      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence)
      (request u receiving target c annotation row) (projected c d) ∧
    InternalPermissionIncidenceR45.Identity
      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence)
      (request u receiving target c annotation row) (projected c d) ∧
    s.parameterRecipes[(projected c d).formal.recipe]? = some (projected c d).formal.parameter := by
  have premises := choice_applies_r66 s inventory u receiving target c
  rcases checked with ⟨hf, hsf, hc, hp, hr, hl, hroute, hlam, hchild, hentry,
    hrecipe, ht, hv, howner, hrole, hformalEntry, hroot, huse, hfact,
    hregistration, hparameter, hformal, hpermissionOwner, hpermissionOccurrence,
    hscope, hannotation, hrow, hpermissionEntry, hnonempty⟩
  refine ⟨?_, ?_, c.parameter⟩
  · exact ⟨hf, hsf, hc, hp, hr, premises.1, hl, hroute, hlam, hchild,
      hentry, hrecipe, ht, hv⟩
  · exact ⟨c.artifact, c.owners.1, c.owners.2, howner,
      (by simp [formal, hrole]), hformalEntry, hroot, rfl, rfl, congrArg use huse,
      (by simp [receipt, c.internal.1]), hfact,
      hregistration, hparameter, hformal, hpermissionOwner, hpermissionOccurrence,
      hscope, hannotation, hrow, hpermissionEntry, hnonempty, c.component⟩

/-- Agreement is derived from the computed R77 global choice and primitive
native reads. It is not a sourceProbe success assumption. -/
theorem primitive_records_derive_source_probe (s : Source S T) (inventory : Inventory S T)
    (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T)
    (checked : PrimitiveRecords s inventory u receiving target c d annotation row) :
    OccurrenceQualifiedConsumerR66.sourceProbe s inventory
      (request u receiving target c annotation row) = some (projected c d) := by
  have premises := choice_applies_r66 s inventory u receiving target c
  rcases checked with ⟨hf, hsf, hc, hp, hr, hl, hroute, hlam, hchild, hentry,
    hrecipe, ht, hv, howner, hrole, hformalEntry, hroot, huse, receiptFact,
    hregistration, hparameter, hformal, hpermissionOwner, hpermissionOccurrence,
    hscope, hannotation, hrow, hpermissionEntry, hnonempty⟩
  have constructionRead : unique (fun x : InternalPermissionIncidenceR45.Construction (Key S T) T =>
      x.registration == c.origin.registration)
      (SourceInternalContextR55.internalInputs s).constructions = some (construction c.origin) := by
    simp [unique, hc]
  have permissionRead : unique (fun x : ComputationPermissionEntryR39.Permission (Key S T) =>
      x.registration == c.origin.registration)
      (SourceInternalContextR55.internalInputs s).permissions = some (permission d.permission) := by
    simp [unique, hp]
  have receiptRead : unique (fun x : InternalPermissionIncidenceR45.Receipt Nat (Key S T) Fact =>
      x.use == use u)
      (SourceInternalContextR55.internalInputs s).receipts = some (receipt c.receipt) := by
    simp [unique, hr]
  simp only [OccurrenceQualifiedConsumerR66.sourceProbe, request]
  rw [premises.1, premises.2.1]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte]
  change (do
    let (f, root) ← (SourceInternalContextR55.internalInputs s).formals c.origin.registration
    let origin ← unique (fun x => x.registration == c.origin.registration)
      (SourceInternalContextR55.internalInputs s).constructions
    let p ← unique (fun x => x.registration == c.origin.registration)
      (SourceInternalContextR55.internalInputs s).permissions
    let r ← unique (fun x => x.use == use u) (SourceInternalContextR55.internalInputs s).receipts
    let fact ← r.fact
    let (_, component) ← (SourceInternalContextR55.internalInputs s).lambdaRecipe c.origin.lambda
    let child ← (SourceInternalContextR55.internalInputs s).positiveFunctionChild origin.function
    pure ⟨f, root, component, origin, p, plan c.plan, r, fact, child⟩) = some (projected c d)
  simp [hf, constructionRead, permissionRead, receiptRead, receipt, receiptFact,
    hrecipe, construction, hchild, projected]

/-- Exact application to the parent Incidence, with no alternative relation. -/
def assemble (s : Source S T) (inventory : Inventory S T)
    (u : Use Nat (Key S T)) (receiving target : Key S T)
    (c : Choice s u receiving target) (d : Records S T) (annotation row : Key S T)
    (checked : PrimitiveRecords s inventory u receiving target c d annotation row) :
    OccurrenceQualifiedConsumerR66.Incidence s inventory (request u receiving target c annotation row) :=
  let fields := primitive_records_derive_fields s inventory u receiving target c d annotation row checked
  ⟨projected c d,
    primitive_records_derive_source_probe s inventory u receiving target c d annotation row checked,
    fields.1, fields.2.1, fields.2.2⟩

structure Constructed (s : Source S T) (inventory : Inventory S T)
    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (u : Use Nat (Key S T)) (receiving target annotation row : Key S T) where
  aligned : AlignedChoice s source calls u receiving target
  incidence : OccurrenceQualifiedConsumerR66.Incidence s inventory
    (request u receiving target aligned.choice annotation row)

/-- Caller inputs are inventories and coordinates only. Every proof-bearing
field is obtained by computation or the preceding derivations. -/
def construct (s : Source S T) (inventory : Inventory S T)
    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (u : Use Nat (Key S T)) (receiving target annotation row : Key S T) :
    Option (Constructed s inventory source calls u receiving target annotation row) := do
  let aligned ← constructAligned s source calls u receiving target
  let d ← readRecords s u receiving target aligned.choice
  if checked : PrimitiveRecords s inventory u receiving target aligned.choice d annotation row then
    some ⟨aligned, assemble s inventory u receiving target aligned.choice d annotation row checked⟩
  else none

/-- R45 acceptance follows on the same permission retained by the R66 result. -/
theorem constructed_applies_r45 (s : Source S T) (inventory : Inventory S T)
    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (u : Use Nat (Key S T)) (receiving target annotation row : Key S T)
    (out : Constructed s inventory source calls u receiving target annotation row) :
    PeelsTo source.expressions out.aligned.alignment.call.callee u.occurrence target ∧
    InternalPermissionIncidenceR45.extract
      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence)
      (request u receiving target out.aligned.choice annotation row) out.incidence.probe =
      some (InternalPermissionIncidenceR45.certificate
        (request u receiving target out.aligned.choice annotation row) out.incidence.probe) :=
  ⟨(alignment_has_name source calls u receiving target out.aligned.alignment).2.2,
    (by exact if_pos ⟨out.incidence.owners, out.incidence.identity⟩)⟩

/-- The R79 bridge computes a complete collected identity before selecting a
source target. The HIR identity is never cast into the solver key. -/
structure BridgedConstructed (b : CollectedDefinitionBridgeR79.Batch)
    (query : CollectedDefinitionBridgeR79.HirDef)
    (s : Source CollectedDefinitionBridgeR79.CollectedDef Nat)
    (inventory : Inventory CollectedDefinitionBridgeR79.CollectedDef Nat)
    (source : OwnerSource (Key CollectedDefinitionBridgeR79.CollectedDef Nat))
    (calls : List (SourceCall (Key CollectedDefinitionBridgeR79.CollectedDef Nat)))
    (u : Use Nat (Key CollectedDefinitionBridgeR79.CollectedDef Nat))
    (receiving annotation row : Key CollectedDefinitionBridgeR79.CollectedDef Nat) where
  target : CollectedDefinitionBridgeR79.CollectedDef
  translated : CollectedDefinitionBridgeR79.lookup b query = some target
  constructed : Constructed s inventory source calls u receiving (.source target) annotation row

def constructBridged (b : CollectedDefinitionBridgeR79.Batch)
    (query : CollectedDefinitionBridgeR79.HirDef)
    (s : Source CollectedDefinitionBridgeR79.CollectedDef Nat)
    (inventory : Inventory CollectedDefinitionBridgeR79.CollectedDef Nat)
    (source : OwnerSource (Key CollectedDefinitionBridgeR79.CollectedDef Nat))
    (calls : List (SourceCall (Key CollectedDefinitionBridgeR79.CollectedDef Nat)))
    (u : Use Nat (Key CollectedDefinitionBridgeR79.CollectedDef Nat))
    (receiving annotation row : Key CollectedDefinitionBridgeR79.CollectedDef Nat) :
    Option (BridgedConstructed b query s inventory source calls u receiving annotation row) :=
  match translated : CollectedDefinitionBridgeR79.lookup b query with
  | none => none
  | some target => do
    let constructed ← construct s inventory source calls u receiving (.source target) annotation row
    pure ⟨target, translated, constructed⟩

theorem bridged_target_in_collection (b : CollectedDefinitionBridgeR79.Batch)
    (ordered : CollectedDefinitionBridgeR79.OrderedRoots b)
    (query : CollectedDefinitionBridgeR79.HirDef)
    (s : Source CollectedDefinitionBridgeR79.CollectedDef Nat)
    (inventory : Inventory CollectedDefinitionBridgeR79.CollectedDef Nat)
    (source : OwnerSource (Key CollectedDefinitionBridgeR79.CollectedDef Nat))
    (calls : List (SourceCall (Key CollectedDefinitionBridgeR79.CollectedDef Nat)))
    (u : Use Nat (Key CollectedDefinitionBridgeR79.CollectedDef Nat))
    (receiving annotation row : Key CollectedDefinitionBridgeR79.CollectedDef Nat)
    (out : BridgedConstructed b query s inventory source calls u receiving annotation row) :
    (query, out.target) ∈ CollectedDefinitionBridgeR79.collectionMap b :=
  CollectedDefinitionBridgeR79.lookup_agrees_with_collection_map b ordered query out.target out.translated

abbrev fixture := SourceInternalChoiceR77.fixture
abbrev fixtureInventory := OccurrenceQualifiedFactReadersR65.fixtureInventory
abbrev fixtureSource := fixtureOwnerSource
abbrev fixtureCalls := [fixtureCall]

def fixtureResult := construct fixture fixtureInventory fixtureSource fixtureCalls
  SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1) (.source 6) (.source 5)

theorem nonempty_successful_finite_witness :
    fixtureResult.isSome = true ∧ SourceInternalChoiceR77.fixtureUse.occurrence ≠ fixtureCall.checking ∧
    ProviderNativeContextR57.fixtureFormal.nativeRoot = some 700 := by decide

/-- The retained permission's concrete row is nonempty and keeps duplicates.
Formal.nativeRoot=700 is not the recipe's registered Lambda root=300. -/
theorem finite_permission_and_root_identity :
    match fixtureResult with
    | none => False
    | some out => out.incidence.probe.permission.concrete = [.source 7, .source 7, .source 11] ∧
        out.incidence.probe.registeredRoot = 300 ∧ out.incidence.probe.registeredRoot ≠ 700 := by decide

def mismatchedLocalGlobal : Source Nat Nat :=
  {fixture with sources := [⟨.source 1, [.lambda (.source 18) (.source 2)]⟩]}

theorem local_global_and_shared_foreign_rejected :
    (SourceInternalChoiceR77.constructAligned mismatchedLocalGlobal fixtureSource fixtureCalls
      SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1)).isSome = true ∧
    (construct mismatchedLocalGlobal fixtureInventory fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse
      (.source 10) (.source 1) (.source 6) (.source 5)).isSome = false ∧
    SourceInternalChoiceR77.foreignOrigin.function = ProviderNativeContextR57.fixtureConstruction.function ∧
    SourceInternalChoiceR77.foreignOrigin.entryEffect = ProviderNativeContextR57.fixtureConstruction.entryEffect ∧
    (construct SourceInternalChoiceR77.foreignSource fixtureInventory fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse
      (.source 10) (.source 1) (.source 6) (.source 5)).isSome = false := by decide

theorem adversarial_inventories_rejected :
    (construct {fixture with constructions := [SourceInternalChoiceR77.foreignOrigin]}
      fixtureInventory fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1) (.source 6) (.source 5)).isSome = false ∧
    (construct {fixture with permissions := fixture.permissions.map (fun p => {p with registration := 1})}
      fixtureInventory fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1) (.source 6) (.source 5)).isSome = false ∧
    (construct {fixture with permissions := fixture.permissions.map (fun p => {p with annotationPosition := .source 999})}
      fixtureInventory fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1) (.source 6) (.source 5)).isSome = false ∧
    (construct {fixture with parameterRecipes := [.source 999]}
      fixtureInventory fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1) (.source 6) (.source 5)).isSome = false ∧
    (construct fixture {fixtureInventory with edges := fixtureInventory.edges ++ [OccurrenceQualifiedFactReadersR65.fixtureFirst]}
      fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1) (.source 6) (.source 5)).isSome = false ∧
    (construct fixture {fixtureInventory with edges := fixtureInventory.edges ++ [OccurrenceQualifiedFactReadersR65.fixtureLambdaEdge]}
      fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1) (.source 6) (.source 5)).isSome = false ∧
    (construct {fixture with componentTerms := fixture.componentTerms.map (fun p => if p.1 = 20 then (20, 700) else p)}
      fixtureInventory fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1) (.source 6) (.source 5)).isSome = false ∧
    (construct {fixture with recipes := fixture.recipes.map (fun r => {r with rootComponent := 21})}
      fixtureInventory fixtureSource fixtureCalls SourceInternalChoiceR77.fixtureUse (.source 10) (.source 1) (.source 6) (.source 5)).isSome = false := by decide

end YulangClosure.ConstructedSourceIncidenceR80
