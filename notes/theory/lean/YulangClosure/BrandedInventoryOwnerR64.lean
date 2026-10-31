import YulangClosure.RustInventoryRequestR63

/-!
R64 structural reification candidate. The record fields below describe the
borrowed InventoryPackage, not the execution of Rust or an identity encoding
from native allocation tokens into Nat. No faithfulness predicate is assumed.
The construction keeps every provenance edge. R55 can reject a fact with
multiple occurrences; this restriction is exposed below, never repaired by
silently dropping occurrences. Actual Rust correspondence remains open.
-/
namespace YulangClosure.BrandedInventoryOwnerR64
open ProviderNativeContextR57 ReachedSlotSearchR58

inductive VariableKind where | value | effect deriving DecidableEq
inductive RawView (S T : Type) where
  | leaf (identity : S)
  | component (identity : S)
  | liveVariable (kind : VariableKind) (polarity : Polarity) (ordinal : Nat)
  | positiveBottom | negativeTop | negativeBottom
  | positiveFunction (argument argumentEffect resultEffect result : T)
  | negativeFunction (argument argumentEffect resultEffect result : T)
  | positiveVariant (alternatives : List (String × List T))
  | negativeVariant (alternatives : List (String × List T))
  | positiveRecord (fields : List (String × Bool × T))
  | negativeRecord (fields : List (String × Bool × T))
  | positiveTuple (elements : List T)
  | negativeTuple (elements : List T)

def children {S T : Type} : RawView S T → List T
  | .positiveFunction a ae re r | .negativeFunction a ae re r => [a,ae,re,r]
  | .positiveVariant alternatives | .negativeVariant alternatives => alternatives.flatMap Prod.snd
  | .positiveRecord fields | .negativeRecord fields => fields.map (fun f => f.2.2)
  | .positiveTuple elements | .negativeTuple elements => elements
  | _ => []

def termView {S T : Type} (state : Nat) : RawView S T → SourceInternalContextR55.TermView (Key S T) T
  | .positiveFunction _ ae _ _ => .positiveFunction ae
  | .liveVariable .effect .negative ordinal => .negativeEffectVariable (.effectRow state ordinal)
  | _ => .other

structure OwnedTerm (S T : Type) where
  term : T
  view : RawView S T

structure SemanticFact (T : Type) where
  index : Nat
  lower : T
  upper : T
  rawLower : Endpoint T
  rawUpper : Endpoint T
  canonicalLower : Endpoint T
  canonicalUpper : Endpoint T

structure Provenance (S : Type) where
  edgeIndex : Nat
  factIndex : Nat
  occurrence : S
  slot : Nat

structure SourceCall (S : Type) where
  callIndex : Nat
  sourceOwner : S
  expressionIndex : Nat
  occurrence : S
  checkingOccurrence : S

structure Schema (S : Type) where
  catchOccurrence : S
  scrutineeOccurrence : S
  providerOccurrence : S
  providerDeclaration : S
  providerFamily : S

/-- Primitive package tables. Source/native consumers are constructed below;
there is no supplied R63 Owner, R55 Native, reader, or expected package. The
opaque native token encoding is a separate source-correspondence obligation. -/
structure Carrier (S T : Type) where
  artifact : Nat
  state : Nat
  store : Nat
  batch : Nat
  entryRow : Nat
  entryRoot : Nat
  formals : List (SourceInternalContextR55.Formal (Key S T) T)
  parameterRecipes : List (Key S T)
  schedules : List (Key S T)
  localSources : List (SourceInternalContextR55.LocalSource (Key S T))
  sourceOwners : List (Key S T × Key S T)
  occupiedDomains : List Nat
  retainedRegistrations : List Nat
  lambdaOrigins : List (SourceInternalContextR55.Construction (Key S T) T)
  permissions : List (SourceInternalContextR55.Permission (Key S T))
  routes : List (SourceInternalContextR55.Receipt Nat (Key S T) Fact)
  uses : List (SourceInternalContextR55.Plan Nat (Key S T) T)
  recipes : List (SourceInternalContextR55.Recipe (Key S T))
  components : List (Nat × T)
  semanticFacts : List (SemanticFact T)
  provenance : List (Provenance S)
  nativeFacts : List (SourceFact S T)
  terms : List (OwnedTerm S T)
  admissions : List (Admission T)
  emissions : List (Emission T)
  valueRows : List (ValueRow T)
  effectRows : List EffectRow
  relations : List (Relation T)
  dependencies : List BoundedAncestryR61.Record
  origins : List (Origin S T)
  views : List (View S)
  resolvedOperations : List (Operation S)
  catches : List (SourceInternalContextR55.Catch (Key S T))
  sourceCalls : List (SourceCall S)
  internalSourceCall : Nat
  schema : Schema S

variable {S T : Type} [DecidableEq S] [DecidableEq T]

def name (c : Carrier S T) : RustInventoryRequestR63.OwnerName := ⟨c.artifact,c.state,c.store,c.batch⟩

def occurrences (c : Carrier S T) (f : SemanticFact T) : List (Provenance S) :=
  c.provenance.filter (fun edge => decide (edge.factIndex = f.index))

def admittedOccurrence (c : Carrier S T) (f : SemanticFact T) (edge : Provenance S) :
    SourceInternalContextR55.AdmittedFact (Key S T) T Fact :=
  ⟨.semantic c.store f.index,.source edge.occurrence,edge.slot,f.lower,f.upper⟩

def sourceOccurrence (c : Carrier S T) (f : SemanticFact T) (edge : Provenance S) : SourceFact S T :=
  ⟨.semantic c.store f.index,edge.occurrence,edge.slot,
    f.rawLower,f.rawUpper,f.canonicalLower,f.canonicalUpper⟩

def admittedFacts (c : Carrier S T) :=
  c.semanticFacts.flatMap (fun f => (occurrences c f).map (admittedOccurrence c f))
def sourceFacts (c : Carrier S T) :=
  c.semanticFacts.flatMap (fun f => (occurrences c f).map (sourceOccurrence c f)) ++ c.nativeFacts

def termViews (c : Carrier S T) := c.terms.map (fun node => (node.term,termView c.state node.view))

def owner (c : Carrier S T) : RustInventoryRequestR63.Owner S T :=
  { name := name c, entryRow := c.entryRow, entryRoot := c.entryRoot
    formals := c.formals, parameterRecipes := c.parameterRecipes, schedules := c.schedules
    sources := c.localSources, sourceOwners := c.sourceOwners
    occupiedDomains := c.occupiedDomains, retainedRegistrations := c.retainedRegistrations
    constructions := c.lambdaOrigins, permissions := c.permissions
    receipts := c.routes, plans := c.uses, recipes := c.recipes
    admittedFacts := admittedFacts c, componentTerms := c.components, termViews := termViews c
    admissions := c.admissions, emissions := c.emissions, valueRows := c.valueRows
    effectRows := c.effectRows, relations := c.relations, dependencies := c.dependencies
    origins := c.origins, facts := sourceFacts c, views := c.views
    operations := c.resolvedOperations, catches := c.catches }

/-- Request coordinates come from the owner-local source-call record and
schema. Missing or duplicated owner-local call indices fail. -/
def call (c : Carrier S T) : Option (RustInventoryRequestR63.Call S) := do
  let actual ← SourceInternalContextR55.unique (fun row => decide (row.callIndex = c.internalSourceCall)) c.sourceCalls
  if actual.occurrence = actual.checkingOccurrence then
    some ⟨name c,actual.occurrence,c.schema.catchOccurrence,c.schema.providerOccurrence⟩
  else none

/-- The seed set is derived from every field read by the R55/R62 term readers,
including every competing construction and every admitted endpoint. -/
def seeds (c : Carrier S T) : List T :=
  c.components.map Prod.snd ++ c.formals.filterMap (fun f => f.nativeRoot) ++
  c.lambdaOrigins.map (fun f => f.function) ++
  c.uses.flatMap (fun p => [p.targetRoot,p.useValue]) ++
  c.semanticFacts.flatMap (fun f => [f.lower,f.upper])

def hasTerm (c : Carrier S T) (term : T) : Bool :=
  (SourceInternalContextR55.unique (fun node => decide (node.term = term)) c.terms).isSome

/-- Finite closure check over owned terms and every immediate child. An empty
inventory is accepted when its derived seeds and children are empty. -/
def termCoverage (c : Carrier S T) : Bool :=
  (seeds c).all (hasTerm c) && c.terms.all (fun node => (children node.view).all (hasTerm c))

def construct (c : Carrier S T) : Option (RustInventoryRequestR63.Owner S T × RustInventoryRequestR63.Call S) := do
  if termCoverage c then
    let request ← call c
    some (owner c,request)
  else none

omit [DecidableEq S] [DecidableEq T] in
theorem complete_fields (c : Carrier S T) :
    (owner c).name = ⟨c.artifact,c.state,c.store,c.batch⟩ ∧
    (owner c).entryRow = c.entryRow ∧ (owner c).entryRoot = c.entryRoot ∧
    (owner c).formals = c.formals ∧ (owner c).parameterRecipes = c.parameterRecipes ∧
    (owner c).schedules = c.schedules ∧ (owner c).sources = c.localSources ∧
    (owner c).sourceOwners = c.sourceOwners ∧
    (owner c).occupiedDomains = c.occupiedDomains ∧
    (owner c).retainedRegistrations = c.retainedRegistrations ∧
    (owner c).constructions = c.lambdaOrigins ∧ (owner c).permissions = c.permissions ∧
    (owner c).receipts = c.routes ∧ (owner c).plans = c.uses ∧
    (owner c).recipes = c.recipes ∧ (owner c).admittedFacts = admittedFacts c ∧
    (owner c).componentTerms = c.components ∧ (owner c).termViews = termViews c ∧
    (owner c).admissions = c.admissions ∧ (owner c).emissions = c.emissions ∧
    (owner c).valueRows = c.valueRows ∧ (owner c).effectRows = c.effectRows ∧
    (owner c).relations = c.relations ∧ (owner c).dependencies = c.dependencies ∧
    (owner c).origins = c.origins ∧ (owner c).facts = sourceFacts c ∧
    (owner c).views = c.views ∧ (owner c).operations = c.resolvedOperations ∧
    (owner c).catches = c.catches := by
  repeat' constructor

omit [DecidableEq S] [DecidableEq T] in
theorem provenance_multiplicity (c : Carrier S T) (f : SemanticFact T) :
    ((occurrences c f).map (admittedOccurrence c f)).length = (occurrences c f).length ∧
    ((occurrences c f).map (sourceOccurrence c f)).length = (occurrences c f).length := by
  simp

omit [DecidableEq S] [DecidableEq T] in
theorem every_provenance_occurrence (c : Carrier S T) (f : SemanticFact T)
    (fact : f ∈ c.semanticFacts) (edge : Provenance S)
    (retained : edge ∈ c.provenance) (same : edge.factIndex = f.index) :
    admittedOccurrence c f edge ∈ (owner c).admittedFacts ∧
    sourceOccurrence c f edge ∈ (owner c).facts := by
  have present : edge ∈ occurrences c f := List.mem_filter.mpr ⟨retained,by simp [same]⟩
  constructor
  · exact List.mem_flatMap.mpr ⟨f,fact,List.mem_map.mpr ⟨edge,present,rfl⟩⟩
  · apply List.mem_append_left
    exact List.mem_flatMap.mpr ⟨f,fact,List.mem_map.mpr ⟨edge,present,rfl⟩⟩

omit [DecidableEq S] [DecidableEq T] in
theorem every_collected_fact (c : Carrier S T) (f : SourceFact S T) :
    f ∈ c.nativeFacts → f ∈ (owner c).facts := by
  intro present
  exact List.mem_append_right _ present

omit [DecidableEq S] [DecidableEq T] in
theorem every_permission (c : Carrier S T) (p : SourceInternalContextR55.Permission (Key S T)) :
    p ∈ (RustInventoryRequestR63.source (owner c)).permissions ↔ p ∈ c.permissions := Iff.rfl

theorem every_provider_competitor (c : Carrier S T) (provider declaration family candidate : Key S T) :
    candidate ∈ providers (RustInventoryRequestR63.native (owner c)) provider declaration family ↔
    ∃ v ∈ c.views, ∃ f ordinal, (f,ordinal) ∈ v.allowed.zipIdx ∧
      v.state = c.state ∧ operationOrigin v.origin provider declaration ∧ family = .source f ∧
      candidate = .effectAtom c.state (.annotationMember v.index ordinal) :=
  RustInventoryRequestR63.all_provider_competitors_retained (owner c) provider declaration family candidate

omit [DecidableEq S] [DecidableEq T] in
theorem owned_term_views (c : Carrier S T) (node : OwnedTerm S T) (present : node ∈ c.terms) :
    (node.term,termView c.state node.view) ∈ (owner c).termViews :=
  List.mem_map.mpr ⟨node,present,rfl⟩

theorem unique_map {A B : Type} (f : A → B) (test : B → Bool) (xs : List A) :
    SourceInternalContextR55.unique test (xs.map f) =
      (SourceInternalContextR55.unique (fun x => test (f x)) xs).map f := by
  unfold SourceInternalContextR55.unique
  rw [List.filter_map]
  simp only [Function.comp_def]
  cases xs.filter (fun x => test (f x)) with
  | nil => rfl
  | cons a rest => cases rest with
    | nil => rfl
    | cons b rest => rfl

theorem consumed_lookup_equations (c : Carrier S T) (term : T) :
    (SourceInternalContextR55.internalInputs (RustInventoryRequestR63.source (owner c))).positiveFunctionChild term =
      (SourceInternalContextR55.unique (fun entry => decide (entry.1 = term)) (termViews c)).bind
        (fun entry => match entry.2 with | .positiveFunction child => some child | _ => none) ∧
    (SourceInternalContextR55.internalInputs (RustInventoryRequestR63.source (owner c))).negativeEntry term =
      (SourceInternalContextR55.unique (fun entry => decide (entry.1 = term)) (termViews c)).bind
        (fun entry => match entry.2 with | .negativeEffectVariable raw => some raw | _ => none) :=
  by
    simp only [SourceInternalContextR55.internalInputs,RustInventoryRequestR63.source,owner]
    cases found : SourceInternalContextR55.unique (fun entry => decide (entry.1 = term)) (termViews c) with
    | none => exact ⟨rfl,rfl⟩
    | some entry => rcases entry with ⟨key,view⟩; cases view <;> exact ⟨rfl,rfl⟩

omit [DecidableEq S] in
theorem owned_lookup_equation (c : Carrier S T) (term : T) :
    SourceInternalContextR55.unique (fun entry => decide (entry.1 = term)) (termViews c) =
      (SourceInternalContextR55.unique (fun node => decide (node.term = term)) c.terms).map
        (fun node => (node.term,termView c.state node.view)) :=
  unique_map (fun node => (node.term,termView c.state node.view))
    (fun entry => decide (entry.1 = term)) c.terms

theorem raw_consumed_lookup_equations (c : Carrier S T) (term : T) :
    (SourceInternalContextR55.internalInputs (RustInventoryRequestR63.source (owner c))).positiveFunctionChild term =
      (SourceInternalContextR55.unique (fun node => decide (node.term = term)) c.terms).bind
        (fun node => match node.view with | .positiveFunction _ child _ _ => some child | _ => none) ∧
    (SourceInternalContextR55.internalInputs (RustInventoryRequestR63.source (owner c))).negativeEntry term =
      (SourceInternalContextR55.unique (fun node => decide (node.term = term)) c.terms).bind
        (fun node => match node.view with
          | .liveVariable .effect .negative ordinal => some (.effectRow c.state ordinal)
          | _ => none) := by
  rw [(consumed_lookup_equations c term).1,(consumed_lookup_equations c term).2,owned_lookup_equation]
  cases found : SourceInternalContextR55.unique (fun node => decide (node.term = term)) c.terms with
  | none => exact ⟨rfl,rfl⟩
  | some node =>
    simp only [Option.map,Option.bind]
    rcases node with ⟨key,view⟩
    cases view with
    | liveVariable kind polarity ordinal => cases kind <;> cases polarity <;> exact ⟨rfl,rfl⟩
    | _ => exact ⟨rfl,rfl⟩

omit [DecidableEq S] in
theorem coverage_contains_seeds_and_children (c : Carrier S T) (checked : termCoverage c = true) :
    (∀ term ∈ seeds c, hasTerm c term = true) ∧
    (∀ node ∈ c.terms, ∀ child ∈ children node.view, hasTerm c child = true) := by
  have both := Bool.and_eq_true_iff.mp checked
  exact ⟨List.all_eq_true.mp both.1,fun node present => List.all_eq_true.mp (List.all_eq_true.mp both.2 node present)⟩

omit [DecidableEq T] in
theorem call_coordinates (c : Carrier S T) (request : RustInventoryRequestR63.Call S) (built : call c = some request) :
    request.owner = name c ∧ request.catchOccurrence = c.schema.catchOccurrence ∧
    request.providerOccurrence = c.schema.providerOccurrence ∧
    ∃ actual ∈ c.sourceCalls, actual.callIndex = c.internalSourceCall ∧
      actual.occurrence = actual.checkingOccurrence ∧ request.useOccurrence = actual.occurrence := by
  unfold call at built
  cases found : SourceInternalContextR55.unique (fun row => decide (row.callIndex = c.internalSourceCall)) c.sourceCalls with
  | none => simp [found] at built
  | some actual =>
    simp only [found,Bind.bind,Option.bind] at built
    split at built
    next same =>
      have eq : (⟨name c,actual.occurrence,c.schema.catchOccurrence,c.schema.providerOccurrence⟩ : RustInventoryRequestR63.Call S) = request := Option.some.inj built
      subst request
      have present := RustInventoryRequestR63.unique_success _ c.sourceCalls actual found
      exact ⟨rfl,rfl,rfl,actual,present.1,of_decide_eq_true present.2,same,rfl⟩
    next different => cases built

theorem construct_exact (c : Carrier S T) (o : RustInventoryRequestR63.Owner S T) (request : RustInventoryRequestR63.Call S)
    (built : construct c = some (o,request)) :
    o = owner c ∧ call c = some request ∧ termCoverage c = true := by
  unfold construct at built
  split at built
  next checked =>
    cases found : call c with
    | none => simp [found] at built
    | some actual =>
      have eq : (owner c,actual) = (o,request) := by simpa [found] using built
      have parts := Prod.mk.inj eq
      exact ⟨parts.1.symm,congrArg some parts.2,checked⟩
  next failed => cases built

omit [DecidableEq S] [DecidableEq T] in
/-- Both derived source lookup operations preserve multiplicity. In particular,
there is no nonempty assumption on any legitimate empty native table. -/
theorem empty_derived_inventories (c : Carrier S T)
    (facts : c.semanticFacts = []) (collected : c.nativeFacts = []) (terms : c.terms = []) :
    (owner c).admittedFacts = [] ∧ (owner c).facts = [] ∧ (owner c).termViews = [] := by
  simp [owner,admittedFacts,sourceFacts,termViews,facts,collected,terms]

/-- Exact R63 parent application to the same constructed owner and source call.
The successful finite extraction and outer Run/Checked/terminal hypotheses
remain unchanged; neither construction nor a proposition definition proves them. -/
theorem same_constructed_consumer (c : Carrier S T) (request : RustInventoryRequestR63.Call S)
    (callRead : call c = some request) (p : RustInventoryRequestR63.Package S T)
    (success : RustInventoryRequestR63.extract (owner c) request = some p)
    (schedule : Nat → Nat → BoundedAncestryR61.Schedule) (search : Search S T)
    (mode : Mode) (limits : Limits) (resource : Resource) (results : List (Branch S T))
    (run : Run (RustInventoryRequestR63.readers p schedule) (RustInventoryRequestR63.request p mode) limits
      (.live ⟨resource,[initial (RustInventoryRequestR63.request p mode)],[],.pop⟩) (.success results))
    (goal : Branch S T) (checked : Checked (RustInventoryRequestR63.readers p schedule) (RustInventoryRequestR63.request p mode) goal)
    (terminal : goal.endpoint = (RustInventoryRequestR63.request p mode).target) :
    request.owner = name c ∧ goal ∈ results ∧
    AuthenticatedResidualConsumerR49.pathCheck (inputs (RustInventoryRequestR63.native (owner c)) search)
      (encodedEndpoint (RustInventoryRequestR63.readers p schedule) (RustInventoryRequestR63.request p mode).root)
      (goal.steps.map ProviderNativeContextR57.step)
      (encodedEndpoint (RustInventoryRequestR63.readers p schedule) (RustInventoryRequestR63.request p mode).target) = true ∧
    AuthenticatedResidualConsumerR49.Arrival (inputs (RustInventoryRequestR63.native (owner c)) search)
      (encodedEndpoint (RustInventoryRequestR63.readers p schedule) (RustInventoryRequestR63.request p mode).target)
      (encodedEndpoint (RustInventoryRequestR63.readers p schedule) (RustInventoryRequestR63.request p mode).root) :=
  ⟨(call_coordinates c request callRead).1,
    RustInventoryRequestR63.constructed_call_candidates_apply_consumer (owner c) request p success
      schedule search mode limits resource results run goal checked terminal⟩

/-- Minimal obstruction: two retained occurrences of one semantic fact make
R55's fact-only uniqueness reader fail, even if the occurrence IDs differ. -/
theorem two_occurrences_routeFact_rejected (c : Carrier S T) (f : SemanticFact T)
    (a b : Provenance S)
    (first : a.factIndex = f.index) (second : b.factIndex = f.index)
    (facts : c.semanticFacts = [f]) (edges : c.provenance = [a,b]) :
    (SourceInternalContextR55.internalInputs (RustInventoryRequestR63.source (owner c))).routeFact (.semantic c.store f.index) = none := by
  simp [SourceInternalContextR55.internalInputs,RustInventoryRequestR63.source,owner,admittedFacts,occurrences,
    facts,edges,first,second,admittedOccurrence,SourceInternalContextR55.unique]

omit [DecidableEq T] in
/-- The native-context source reader distinguishes the two causes, whereas
R55's routeFact reader above rejects the same retained semantic identity.
This is a finite model discriminator, not an executed-source counterexample. -/
theorem two_distinct_causes_native_source_read (c : Carrier S T) (f : SemanticFact T)
    (a b : Provenance S)
    (first : a.factIndex = f.index) (second : b.factIndex = f.index)
    (facts : c.semanticFacts = [f]) (edges : c.provenance = [a,b])
    (collected : c.nativeFacts = []) (slotA : a.slot = 0) (slotB : b.slot = 0)
    (distinct : a.occurrence ≠ b.occurrence) :
    sourceFact (RustInventoryRequestR63.native (owner c)) (.source a.occurrence,0) =
      some (.semantic c.store f.index) := by
  simp [sourceFact,unique,SourceInternalContextR55.unique,RustInventoryRequestR63.native,
    BoundedAncestryR61.native,RustInventoryRequestR63.base,owner,sourceFacts,occurrences,
    facts,edges,first,second,collected,sourceOccurrence,slotA,slotB,Ne.symm distinct,name]

end YulangClosure.BrandedInventoryOwnerR64
