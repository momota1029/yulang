import YulangClosure.AuthenticatedResidualConsumerR49

/-!
R55 source/Internal fragment. Primitive records mirror retained HIR, native
registration/permission/origin/recipe/fact/TermView fields. Constructors below
produce existing R39/R45/R49 fragments from primitive fields. Parent applications
retain an explicit independent context for fields outside this fragment.
This is not a complete R49 Context or R50 interpretation, nor Rust execution.
-/
namespace YulangClosure.SourceInternalContextR55


variable {Artifact Id Term Fact : Type}

inductive NativeRole where | value | computation deriving DecidableEq
structure Formal (Id Term : Type) where
  owner : Id
  lambdaIndex : Nat
  parameter : Id
  recipePosition : Nat
  scope : Id
  role : NativeRole
  entryEffect : Option Id
  nativeRoot : Option Term

inductive Expression (Id : Type) where
  | lambda (occurrence parameter : Id)
  | other (occurrence : Id)
  deriving DecidableEq
structure LocalSource (Id : Type) where
  owner : Id
  expressions : List (Expression Id)

structure Permission (Id : Type) where
  registration : Nat
  parameterPosition : Nat
  formal : Id
  occurrence : Id
  sourceOwner : Id
  scope : Id
  annotationPosition : Id
  sourceRow : Id
  entryEffect : Id
  concrete : List Id

structure Construction (Id Term : Type) where
  registration : Nat
  lambda : Id
  function : Term
  entryEffect : Id

structure Use (Artifact Id : Type) where
  artifact : Artifact
  occurrence : Id
  deriving DecidableEq
inductive RouteKind where | internal | incomingInt | incomingBottomTrivial | incomingStructured deriving DecidableEq
structure Receipt (Artifact Id Fact : Type) where
  use : Use Artifact Id
  kind : RouteKind
  fact : Option Fact
structure Plan (Artifact Id Term : Type) where
  use : Use Artifact Id
  sourceOwner : Id
  targetOwner : Id
  targetRootComponent : Nat
  useValueComponent : Nat
  targetRoot : Term
  useValue : Term
structure Recipe (Id : Type) where
  occurrence : Id
  formalRegistration : Option Nat
  rootComponent : Nat
structure AdmittedFact (Id Term Fact : Type) where
  fact : Fact
  occurrence : Id
  slot : Nat
  lower : Term
  upper : Term
inductive TermView (Id Term : Type) where
  | positiveFunction (argumentEffect : Term)
  | negativeEffectVariable (rawEntry : Id)
  | other

/-- All inventories precede selection; no permission or fact is prefiltered
by matching Function, canonical entry or expected conclusion. -/
structure Native (Artifact Id Term Fact : Type) where
  artifact : Artifact
  formals : List (Formal Id Term)
  parameterRecipes : List Id
  schedules : List Id
  sources : List (LocalSource Id)
  sourceOwners : List (Id × Id)
  occupiedDomains : List Nat
  retainedRegistrations : List Nat
  constructions : List (Construction Id Term)
  permissions : List (Permission Id)
  receipts : List (Receipt Artifact Id Fact)
  plans : List (Plan Artifact Id Term)
  recipes : List (Recipe Id)
  admittedFacts : List (AdmittedFact Id Term Fact)
  componentTerms : List (Nat × Term)
  termViews : List (Term × TermView Id Term)

def unique {A : Type} (predicate : A → Bool) (xs : List A) : Option A :=
  match xs.filter predicate with | [item] => some item | _ => none

def formal (f : Formal Id Term) : ComputationPermissionEntryR39.Registration Id :=
  ⟨f.owner, f.lambdaIndex, f.parameter, f.recipePosition, f.scope,
    match f.role with | .value => .value | .computation => .computation, f.entryEffect⟩
def expression : Expression Id → ComputationPermissionEntryR39.SourceExpr Id
  | .lambda occurrence parameter => .lambda occurrence parameter
  | .other occurrence => .other occurrence

def sourceInputs (n : Native Artifact Id Term Fact) : ComputationPermissionEntryR39.Inputs Id :=
  ⟨n.formals.map formal, n.parameterRecipes, n.schedules,
    n.sources.map (fun source => (source.owner, source.expressions.map expression)),
    n.sourceOwners, n.occupiedDomains, n.retainedRegistrations⟩
def permission (p : Permission Id) : ComputationPermissionEntryR39.Permission Id :=
  ⟨p.registration, p.parameterPosition, p.formal, p.occurrence, p.sourceOwner, p.scope,
    p.annotationPosition, p.sourceRow, p.entryEffect, p.concrete⟩
def construction (c : Construction Id Term) : InternalPermissionIncidenceR45.Construction Id Term :=
  ⟨c.registration, c.lambda, c.function, c.entryEffect⟩
def use (u : Use Artifact Id) : InternalPermissionIncidenceR45.UseId Artifact Id := ⟨u.artifact, u.occurrence⟩
def receipt (r : Receipt Artifact Id Fact) : InternalPermissionIncidenceR45.Receipt Artifact Id Fact :=
  ⟨use r.use, match r.kind with
    | .internal => .internal | .incomingInt => .incomingInt
    | .incomingBottomTrivial => .incomingBottomTrivial | .incomingStructured => .incomingStructured, r.fact⟩
def plan (p : Plan Artifact Id Term) : InternalPermissionIncidenceR45.Plan Id Term :=
  ⟨p.sourceOwner, p.targetOwner, p.targetRootComponent, p.useValueComponent, p.targetRoot, p.useValue⟩

def internalInputs [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]
    (n : Native Artifact Id Term Fact) : InternalPermissionIncidenceR45.Inputs Artifact Id Term Fact :=
  { artifact := n.artifact
    source := sourceInputs n
    formals := fun index => (n.formals[index]?).bind (fun f =>
      (unique (fun recipe => decide (recipe.formalRegistration = some index)) n.recipes).bind (fun recipe =>
        (unique (fun entry => decide (entry.1 = recipe.rootComponent)) n.componentTerms).map
          (fun entry => (formal f, entry.2))))
    constructions := n.constructions.map construction
    permissions := n.permissions.map permission
    receipts := n.receipts.map receipt
    plan := fun u => (unique (fun p => decide (use p.use = u)) n.plans).map plan
    routeFact := fun fact => (unique (fun f => decide (f.fact = fact)) n.admittedFacts).bind
      (fun f => if f.slot = 0 then some (f.occurrence, f.lower, f.upper) else none)
    lambdaRecipe := fun occurrence => (unique (fun r => decide (r.occurrence = occurrence)) n.recipes).bind
      (fun r => r.formalRegistration.map (fun index => (index, r.rootComponent)))
    componentTerm := fun index => (unique (fun entry => decide (entry.1 = index)) n.componentTerms).map Prod.snd
    lambdaFact := fun occurrence => (unique (fun f => decide (f.occurrence = occurrence ∧ f.slot = 2)) n.admittedFacts).map
      (fun f => (f.lower, f.upper))
    positiveFunctionChild := fun term => (unique (fun entry => decide (entry.1 = term)) n.termViews).bind
      (fun entry => match entry.2 with | .positiveFunction child => some child | _ => none)
    negativeEntry := fun term => (unique (fun entry => decide (entry.1 = term)) n.termViews).bind
      (fun entry => match entry.2 with | .negativeEffectVariable entry => some entry | _ => none) }

/-- The source projection rejects duplicate owner/local-Lambda coordinates
before selecting a registration. This guard is independent of R45 acceptance. -/
def internalFragment [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]
    (n : Native Artifact Id Term Fact) : Option (InternalPermissionIncidenceR45.Inputs Artifact Id Term Fact) :=
  if (n.formals.map (fun f => (f.owner, f.lambdaIndex))).Nodup then some (internalInputs n) else none

theorem native_reader_equations [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]
    (n : Native Artifact Id Term Fact) (u : Use Artifact Id) (fact : Fact) (occurrence : Id) (index : Nat) (term : Term) :
    (sourceInputs n).formals = n.formals.map formal ∧
    (sourceInputs n).recipes = n.parameterRecipes ∧
    (sourceInputs n).schedules = n.schedules ∧
    (sourceInputs n).owners = n.sourceOwners ∧
    (sourceInputs n).occupiedDomains = n.occupiedDomains ∧
    (sourceInputs n).retainedRegistrations = n.retainedRegistrations ∧
    (internalInputs n).constructions = n.constructions.map construction ∧
    (internalInputs n).receipts = n.receipts.map receipt ∧
    (internalInputs n).plan (use u) = (unique (fun p => decide (use p.use = use u)) n.plans).map plan ∧
    (internalInputs n).routeFact fact = (unique (fun f => decide (f.fact = fact)) n.admittedFacts).bind
      (fun f => if f.slot = 0 then some (f.occurrence, f.lower, f.upper) else none) ∧
    (internalInputs n).lambdaRecipe occurrence = (unique (fun r => decide (r.occurrence = occurrence)) n.recipes).bind
      (fun r => r.formalRegistration.map (fun registration => (registration, r.rootComponent))) ∧
    (internalInputs n).componentTerm index = (unique (fun entry => decide (entry.1 = index)) n.componentTerms).map Prod.snd ∧
    (internalInputs n).lambdaFact occurrence = (unique (fun f => decide (f.occurrence = occurrence ∧ f.slot = 2)) n.admittedFacts).map
      (fun f => (f.lower, f.upper)) ∧
    (internalInputs n).positiveFunctionChild term = (unique (fun entry => decide (entry.1 = term)) n.termViews).bind
      (fun entry => match entry.2 with | .positiveFunction child => some child | _ => none) ∧
    (internalInputs n).negativeEntry term = (unique (fun entry => decide (entry.1 = term)) n.termViews).bind
      (fun entry => match entry.2 with | .negativeEffectVariable raw => some raw | _ => none) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

structure Query (Artifact Id : Type) where
  use : Use Artifact Id
  sourceOwner : Id
  targetOwner : Id
  registration : Nat
  lambda : Id
  annotationPosition : Id
  rowPosition : Id
structure Probe (Artifact Id Term Fact : Type) where
  formal : Formal Id Term
  registeredRoot : Term
  recipeRootComponent : Nat
  construction : Construction Id Term
  permission : Permission Id
  plan : Plan Artifact Id Term
  receipt : Receipt Artifact Id Fact
  fact : Fact
  child : Term

def query (q : Query Artifact Id) : InternalPermissionIncidenceR45.Query Artifact Id :=
  ⟨use q.use, q.sourceOwner, q.targetOwner, q.registration, q.lambda, q.annotationPosition, q.rowPosition⟩
def probe (p : Probe Artifact Id Term Fact) : InternalPermissionIncidenceR45.Probe Artifact Id Term Fact :=
  ⟨formal p.formal, p.registeredRoot, p.recipeRootComponent, construction p.construction,
    permission p.permission, plan p.plan, receipt p.receipt, p.fact, p.child⟩

/-- The formal's nativeRoot is the PARAMETER root. R45 registeredRoot is
instead the exact LambdaRecipe root_component term; never substitute them. -/
theorem formal_reader_equation [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]
    (n : Native Artifact Id Term Fact) (index : Nat) (f : Formal Id Term) (recipe : Recipe Id) (root : Term)
    (atIndex : n.formals[index]? = some f)
    (recipeRead : unique (fun found => decide (found.formalRegistration = some index)) n.recipes = some recipe)
    (componentRead : unique (fun entry => decide (entry.1 = recipe.rootComponent)) n.componentTerms = some (recipe.rootComponent, root)) :
    (internalInputs n).formals index = some (formal f, root) := by
  simp [internalInputs, atIndex, recipeRead, componentRead]

def localLookup [DecidableEq Id] : List (LocalSource Id) → Id → Option (LocalSource Id)
  | [], _ => none
  | source :: rest, owner => if source.owner = owner then some source else localLookup rest owner

theorem local_source_lookup [DecidableEq Id] (sources : List (LocalSource Id)) (owner : Id) :
    ComputationPermissionEntryR39.localSource
      (sources.map (fun source => (source.owner, source.expressions.map expression))) owner =
      (localLookup sources owner).map (fun source => source.expressions.map expression) := by
  induction sources with
  | nil => rfl
  | cons source rest ih =>
    by_cases same : source.owner = owner <;> simp [ComputationPermissionEntryR39.localSource, localLookup, same, ih]

theorem source_lambda_reader [DecidableEq Id] (n : Native Artifact Id Term Fact)
    (f : Formal Id Term) (source : LocalSource Id) (occurrence : Id)
    (ownerRead : localLookup n.sources f.owner = some source)
    (atIndex : source.expressions[f.lambdaIndex]? = some (.lambda occurrence f.parameter)) :
    ComputationPermissionEntryR39.sourceLambda (sourceInputs n) (formal f) = some (occurrence, f.parameter) := by
  have sourceRead := local_source_lookup n.sources f.owner
  rw [ownerRead] at sourceRead
  simp [ComputationPermissionEntryR39.sourceLambda, formal, sourceInputs, sourceRead, List.getElem?_map, atIndex, expression]

theorem complete_permission_inventory [DecidableEq Artifact] [DecidableEq Id] [DecidableEq Term] [DecidableEq Fact]
    (n : Native Artifact Id Term Fact) :
    (internalInputs n).permissions = n.permissions.map permission := rfl

inductive ValuePattern (Id : Type) where | wildcard | binder (identity : Id) deriving DecidableEq
inductive Payload (Id : Type) where
  | unitSyntax (source : Id) (range : Nat × Nat)
  | value (pattern : ValuePattern Id)
  deriving DecidableEq
inductive Pattern (Id : Type) where
  | operation (operationSource : Id) (resolved : Option (Id × Id))
      (payloads : List (Payload Id)) (continuation : ValuePattern Id)
  | value (pattern : ValuePattern Id)
  deriving DecidableEq
structure Arm (Id : Type) where
  source : Id
  range : Nat × Nat
  pattern : Pattern Id
  bodyIndex : Nat
structure Catch (Id : Type) where
  owner : Id
  occurrence : Id
  edgeScrutinee : Id
  arms : List (Arm Id)
structure Operation (Id : Type) where
  source : Id
  declaration : Id
  family : Id

def valuePattern : ValuePattern Id → AuthenticatedResidualConsumerR49.ValuePattern Id
  | .wildcard => .wildcard | .binder identity => .binder identity

def payload : Payload Id → AuthenticatedResidualConsumerR49.PayloadPattern Id
  | .unitSyntax source _ => .unitSyntax source
  | .value pattern => .value (valuePattern pattern)
def pattern : Pattern Id → Option (AuthenticatedResidualConsumerR49.Pattern Id)
  | .value p => some (.value (valuePattern p))
  | .operation source resolved payloads continuation =>
      resolved.map (fun (declaration, family) => .operation source declaration family
        (payloads.map payload) (valuePattern continuation))
def arm (a : Arm Id) : Option (AuthenticatedResidualConsumerR49.Arm Id) := (pattern a.pattern).map (fun p => ⟨a.source, a.range, p⟩)

def arms : List (Arm Id) → Option (List (AuthenticatedResidualConsumerR49.Arm Id))
  | [] => some []
  | a :: rest => do let head ← arm a; let tail ← arms rest; pure (head :: tail)
def catchRecord (c : Catch Id) : Option (AuthenticatedResidualConsumerR49.SourceCatch Id) :=
  (arms c.arms).map (fun translated => ⟨c.occurrence, c.edgeScrutinee, translated⟩)

def catchInputs [DecidableEq Id] (catches : List (Catch Id)) (operations : List (Operation Id)) : AuthenticatedResidualConsumerR49.SourceInputs Id :=
  ⟨(fun occurrence => (unique (fun c => decide (c.occurrence = occurrence)) catches).bind catchRecord),
    (fun source => (unique (fun operation => decide (operation.source = source)) operations).map
      (fun operation => (operation.declaration, operation.family)))⟩

theorem catch_reader_equation [DecidableEq Id] (catches : List (Catch Id)) (operations : List (Operation Id))
    (c : Catch Id) (out : AuthenticatedResidualConsumerR49.SourceCatch Id)
    (selected : unique (fun found => decide (found.occurrence = c.occurrence)) catches = some c)
    (translated : catchRecord c = some out) :
    (catchInputs catches operations).catchSource c.occurrence = some out := by
  simp [catchInputs, selected, translated]

theorem resolved_operation_reader [DecidableEq Id] (catches : List (Catch Id)) (operations : List (Operation Id))
    (operation : Operation Id)
    (selected : unique (fun found => decide (found.source = operation.source)) operations = some operation) :
    (catchInputs catches operations).resolvedOperation operation.source = some (operation.declaration, operation.family) := by
  simp [catchInputs, selected]

/-- Exact constructed-reader characterization, not a semantic/extraction
assumption. The concrete instance below discharges both existing predicates. -/
theorem constructed_internal_characterization [DecidableEq Artifact] [DecidableEq Id]
    [DecidableEq Term] [DecidableEq Fact] (n : Native Artifact Id Term Fact)
    (q : Query Artifact Id) (p : Probe Artifact Id Term Fact) :
    InternalPermissionIncidenceR45.extract (internalInputs n) (query q) (probe p) =
      some (InternalPermissionIncidenceR45.certificate (query q) (probe p)) ↔
    InternalPermissionIncidenceR45.OwnerReads (internalInputs n) (query q) (probe p) ∧
      InternalPermissionIncidenceR45.Identity (internalInputs n) (query q) (probe p) := by
  constructor
  · intro accepted
    have exactReads := (InternalPermissionIncidenceR45.accepted_iff _ _ _ _).mp accepted
    exact ⟨exactReads.1, exactReads.2.1⟩
  · intro reads
    exact (InternalPermissionIncidenceR45.accepted_iff _ _ _ _).mpr ⟨reads.1, reads.2, rfl⟩

theorem constructed_internal_application [DecidableEq Artifact] [DecidableEq Id]
    [DecidableEq Term] [DecidableEq Fact] (n : Native Artifact Id Term Fact)
    (q : Query Artifact Id) (p : Probe Artifact Id Term Fact)
    (accepted : InternalPermissionIncidenceR45.extract (internalInputs n) (query q) (probe p) =
      some (InternalPermissionIncidenceR45.certificate (query q) (probe p))) :
    (internalInputs n).positiveFunctionChild p.construction.function = some p.child ∧
    (internalInputs n).negativeEntry p.child = some p.permission.entryEffect ∧
    (permission p.permission).concrete = p.permission.concrete := by
  have fields := InternalPermissionIncidenceR45.accepted_constructor_and_endpoints _ _ _ _ accepted
  exact ⟨fields.2.1, fields.2.2.1, rfl⟩

structure Selection (Id : Type) where
  catchOccurrence : Id
  position : Nat
  armSource : Id
  armRange : Nat × Nat
  operationSource : Id
  payloadSource : Id
  declaration : Id
  family : Id

def selection (s : Selection Id) : AuthenticatedResidualConsumerR49.Selection Id :=
  ⟨s.catchOccurrence, s.position, s.armSource, s.armRange, s.operationSource,
    s.payloadSource, s.declaration, s.family⟩

/-- Supply only the constructed source fragment. All independent provider,
arrival and Internal fields of the parent context are preserved as supplied. -/
def withSource {Artifact Id Term Fact : Type} [DecidableEq Id]
    (c : AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
    (catches : List (Catch Id)) (operations : List (Operation Id)) (s : Selection Id) :
    AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact :=
  { c with
    source := catchInputs catches operations
    probe := { c.probe with selection := selection s } }

theorem constructed_known_unmatched [DecidableEq Artifact] [DecidableEq Id]
    [DecidableEq Term] [DecidableEq Fact]
    (c : AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
    (catches : List (Catch Id)) (operations : List (Operation Id)) (s : Selection Id)
    (armRead : AuthenticatedResidualConsumerR49.SelectedArmReads (catchInputs catches operations) c.query (selection s))
    (providerRead : c.inputs.arrival.sourceOperation c.query.provider = some (c.query.declaration, c.query.family))
    (different : s.declaration ≠ c.query.declaration) :
    AuthenticatedResidualConsumerR49.classifyIdentity (withSource c catches operations s) = .knownUnmatched := by
  apply (AuthenticatedResidualConsumerR49.classification_known_unmatched_iff _).mpr
  exact ⟨⟨armRead, providerRead⟩, different⟩

def nativeFormal : Formal Nat Nat := ⟨1, 0, 2, 0, 3, .computation, some 4, some 700⟩
def nativeConstruction : Construction Nat Nat := ⟨0, 17, 200, 4⟩
def nativePermission : Permission Nat := ⟨0, 0, 2, 17, 1, 3, 6, 5, 4, [7, 7, 11]⟩
def nativeUse : Use Nat Nat := ⟨99, 100⟩
def nativeReceipt : Receipt Nat Nat Nat := ⟨nativeUse, .internal, some 88⟩
def nativePlan : Plan Nat Nat Nat := ⟨nativeUse, 10, 1, 20, 21, 300, 400⟩
def nativeQuery : Query Nat Nat := ⟨nativeUse, 10, 1, 0, 17, 6, 5⟩
def nativeProbe : Probe Nat Nat Nat Nat :=
  ⟨nativeFormal, 300, 20, nativeConstruction, nativePermission, nativePlan, nativeReceipt, 88, 201⟩

/-- Primitive finite source/native records, not an existing model Inputs or
Context. Schedule999 deliberately differs from LocalSource lambda17. -/
def nativeInputs : Native Nat Nat Nat Nat :=
  ⟨99, [nativeFormal], [2], [999], [⟨1, [.lambda 17 2]⟩], [(17, 1)], [], [],
    [nativeConstruction], [nativePermission], [nativeReceipt], [nativePlan], [⟨17, some 0, 20⟩],
    [⟨88, 100, 0, 300, 400⟩, ⟨89, 17, 2, 200, 300⟩], [(20, 300), (21, 400)],
    [(200, .positiveFunction 201), (201, .negativeEffectVariable 4)]⟩

theorem concrete_existing_internal_extraction :
    ComputationPermissionEntryR39.sourceLambda (sourceInputs nativeInputs) (formal nativeFormal) = some (17, 2) ∧
    (sourceInputs nativeInputs).schedules[0]? = some 999 ∧
    InternalPermissionIncidenceR45.extract (internalInputs nativeInputs) (query nativeQuery) (probe nativeProbe) =
      some (InternalPermissionIncidenceR45.certificate (query nativeQuery) (probe nativeProbe)) ∧
    (internalInputs nativeInputs).permissions = [permission nativePermission] ∧
    (permission nativePermission).concrete = [7, 7, 11] := by decide

theorem concrete_parameter_and_lambda_roots_distinct :
    nativeFormal.nativeRoot = some 700 ∧
    (internalInputs nativeInputs).formals 0 = some (formal nativeFormal, 300) ∧
    InternalPermissionIncidenceR45.extract (internalInputs nativeInputs) (query nativeQuery)
      (probe { nativeProbe with registeredRoot := 700 }) = none := by decide

theorem concrete_complete_fragment_and_duplicate_formal_rejection :
    internalFragment nativeInputs = some (internalInputs nativeInputs) ∧
    internalFragment { nativeInputs with formals := [nativeFormal, nativeFormal] } = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with formals := [] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with recipes := [] })
      (query nativeQuery) (probe nativeProbe) = none := by
  constructor
  · simp [internalFragment, nativeInputs]
  constructor
  · simp [internalFragment]
  decide

theorem concrete_same_native_parent_application :
    (internalInputs nativeInputs).positiveFunctionChild nativeConstruction.function = some nativeProbe.child ∧
    (internalInputs nativeInputs).negativeEntry nativeProbe.child = some nativePermission.entryEffect ∧
    (permission nativePermission).concrete = nativePermission.concrete :=
  constructed_internal_application nativeInputs nativeQuery nativeProbe concrete_existing_internal_extraction.2.2.1

/-- Every raw list is checked at its owning key before image comparison.
Missing/duplicate permissions, constructions, receipts, facts, recipes and
native children cannot instantiate the existing R45 extraction. -/
theorem concrete_missing_duplicate_internal_rejected :
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with permissions := [] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with permissions := [nativePermission, nativePermission] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with constructions := [nativeConstruction, nativeConstruction] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with receipts := [nativeReceipt, nativeReceipt] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with admittedFacts := nativeInputs.admittedFacts ++ nativeInputs.admittedFacts })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with recipes := [⟨17, some 0, 20⟩, ⟨17, some 0, 20⟩] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with termViews := [(200, .other), (201, .negativeEffectVariable 4)] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with termViews := nativeInputs.termViews ++ nativeInputs.termViews })
      (query nativeQuery) (probe nativeProbe) = none := by decide

theorem concrete_owner_index_and_raw_identity_rejected :
    InternalPermissionIncidenceR45.extract (internalInputs nativeInputs) (query { nativeQuery with use := ⟨98, 100⟩ })
      (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with sources := [⟨1, [.other 999]⟩] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs nativeInputs)
      (query nativeQuery) (probe { nativeProbe with permission := { nativePermission with entryEffect := 44 } }) = none ∧
    (fun _ : Nat => 0) nativePermission.entryEffect = (fun _ : Nat => 0) 44 := by decide

theorem concrete_missing_foreign_native_reads_rejected :
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with constructions := [] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with receipts := [] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with admittedFacts := [] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with admittedFacts :=
      [⟨88, 100, 0, 301, 400⟩, ⟨89, 17, 2, 200, 300⟩] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with termViews := [] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with termViews :=
      [(200, .positiveFunction 202), (201, .negativeEffectVariable 4)] })
      (query nativeQuery) (probe nativeProbe) = none ∧
    InternalPermissionIncidenceR45.extract (internalInputs { nativeInputs with termViews :=
      [(200, .positiveFunction 201), (201, .negativeEffectVariable 44)] })
      (query nativeQuery) (probe nativeProbe) = none := by decide

def nativeCatch : Catch Nat :=
  ⟨1, 400, 200,
    [⟨401, (10, 20), .operation 402 (some (40, 41)) [.unitSyntax 403 (12, 14)] .wildcard, 8⟩,
      ⟨404, (21, 25), .value (.binder 405), 9⟩]⟩
def nativeOperation : Operation Nat := ⟨402, 40, 41⟩
def nativeSelection : Selection Nat := ⟨400, 0, 401, (10, 20), 402, 403, 40, 41⟩

theorem concrete_complete_catch_and_arm :
    (catchInputs [nativeCatch] [nativeOperation]).catchSource 400 =
      some ⟨400, 200, [⟨401, (10, 20), .operation 402 40 41 [.unitSyntax 403] .wildcard⟩,
        ⟨404, (21, 25), .value (.binder 405)⟩]⟩ ∧
    AuthenticatedResidualConsumerR49.SelectedArmReads (catchInputs [nativeCatch] [nativeOperation])
      AuthenticatedResidualConsumerR49.knownUnmatchedContext.query (selection nativeSelection) := by decide

theorem concrete_source_classification_application :
    AuthenticatedResidualConsumerR49.classifyIdentity
      (withSource AuthenticatedResidualConsumerR49.knownUnmatchedContext [nativeCatch] [nativeOperation] nativeSelection) =
      .knownUnmatched :=
  constructed_known_unmatched _ _ _ _ concrete_complete_catch_and_arm.2 (by decide) (by decide)

/-- Forwarding still needs the independent provider/native reader. No provider
reader is synthesized from a Catch or Internal certificate in this fragment. -/
theorem constructed_known_unmatched_forward [DecidableEq Artifact] [DecidableEq Id]
    [DecidableEq Term] [DecidableEq Fact]
    (c : AuthenticatedResidualConsumerR49.Context Artifact Id Term Fact)
    (catches : List (Catch Id)) (operations : List (Operation Id)) (s : Selection Id)
    (endpoint : CurrentEmissionOwnershipR47.Endpoint Id) (candidate : Bool)
    (armRead : AuthenticatedResidualConsumerR49.SelectedArmReads (catchInputs catches operations) c.query (selection s))
    (providerRead : c.inputs.arrival.sourceOperation c.query.provider = some (c.query.declaration, c.query.family))
    (different : s.declaration ≠ c.query.declaration)
    (native : AuthenticatedResidualConsumerR49.providerCandidate (withSource c catches operations s) endpoint = some candidate) :
    AuthenticatedResidualConsumerR49.decideEndpoint (withSource c catches operations s) endpoint = some .forward :=
  AuthenticatedResidualConsumerR49.known_unmatched_decision _ _
    (constructed_known_unmatched c catches operations s armRead providerRead different) candidate native

theorem concrete_missing_reordered_foreign_source_rejected :
    ¬ AuthenticatedResidualConsumerR49.SelectedArmReads (catchInputs [] [nativeOperation])
      AuthenticatedResidualConsumerR49.knownUnmatchedContext.query (selection nativeSelection) ∧
    ¬ AuthenticatedResidualConsumerR49.SelectedArmReads (catchInputs [{ nativeCatch with arms := nativeCatch.arms.reverse }] [nativeOperation])
      AuthenticatedResidualConsumerR49.knownUnmatchedContext.query (selection nativeSelection) ∧
    ¬ AuthenticatedResidualConsumerR49.SelectedArmReads (catchInputs [nativeCatch] [nativeOperation, nativeOperation])
      AuthenticatedResidualConsumerR49.knownUnmatchedContext.query (selection nativeSelection) ∧
    ¬ AuthenticatedResidualConsumerR49.SelectedArmReads (catchInputs [nativeCatch] [{ nativeOperation with declaration := 42 }])
      AuthenticatedResidualConsumerR49.knownUnmatchedContext.query (selection nativeSelection) ∧
    (fun _ : Nat => "ping") nativeOperation.declaration = (fun _ : Nat => "ping") 42 := by decide

theorem concrete_unresolved_unselected_arm_rejected :
    catchRecord { nativeCatch with arms := nativeCatch.arms ++
      [⟨406, (26, 30), .operation 407 none [] .wildcard, 10⟩] } = none := by decide

end YulangClosure.SourceInternalContextR55
