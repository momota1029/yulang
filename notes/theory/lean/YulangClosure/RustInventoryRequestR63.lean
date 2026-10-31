import YulangClosure.InternalRootPolicyR62

/-!
R63: finite construction from typed owner-record carriers. These carriers are
the mathematical inputs to extraction, not a proved interpretation of Rust
borrows. Every source/native list is retained before request selection. No
expected package, preselected successful path, or faithfulness law is an input.
The outer Rust-to-Run, resource and original whole-language obligations remain.
-/
namespace YulangClosure.RustInventoryRequestR63
open ProviderNativeContextR57 ReachedSlotSearchR58

structure OwnerName where
  artifact : Nat
  state : Nat
  store : Nat
  batch : Nat
  deriving DecidableEq

/-- Full typed owner carriers; fields are primitive records, not an R55/R57
Native, Context, reader callback or expected package. Source identities retain
the Key constructors, so an entry row is never a source ordinal. -/
structure Owner (S T : Type) where
  name : OwnerName
  entryRow : Nat
  entryRoot : Nat
  formals : List (SourceInternalContextR55.Formal (Key S T) T)
  parameterRecipes : List (Key S T)
  schedules : List (Key S T)
  sources : List (SourceInternalContextR55.LocalSource (Key S T))
  sourceOwners : List (Key S T × Key S T)
  occupiedDomains : List Nat
  retainedRegistrations : List Nat
  constructions : List (SourceInternalContextR55.Construction (Key S T) T)
  permissions : List (SourceInternalContextR55.Permission (Key S T))
  receipts : List (SourceInternalContextR55.Receipt Nat (Key S T) Fact)
  plans : List (SourceInternalContextR55.Plan Nat (Key S T) T)
  recipes : List (SourceInternalContextR55.Recipe (Key S T))
  admittedFacts : List (SourceInternalContextR55.AdmittedFact (Key S T) T Fact)
  componentTerms : List (Nat × T)
  termViews : List (T × SourceInternalContextR55.TermView (Key S T) T)
  admissions : List (Admission T)
  emissions : List (Emission T)
  valueRows : List (ValueRow T)
  effectRows : List EffectRow
  relations : List (Relation T)
  dependencies : List BoundedAncestryR61.Record
  origins : List (Origin S T)
  facts : List (SourceFact S T)
  views : List (View S)
  operations : List (Operation S)
  catches : List (SourceInternalContextR55.Catch (Key S T))

structure Call (S : Type) where
  owner : OwnerName
  useOccurrence : S
  catchOccurrence : S
  providerOccurrence : S

variable {S T : Type} [DecidableEq S] [DecidableEq T]

def source (o : Owner S T) : InternalRootPolicyR62.Source S T :=
  ⟨o.name.artifact,o.formals,o.parameterRecipes,o.schedules,o.sources,
    o.sourceOwners,o.occupiedDomains,o.retainedRegistrations,o.constructions,
    o.permissions,o.receipts,o.plans,o.recipes,o.admittedFacts,o.componentTerms,o.termViews⟩

def base (o : Owner S T) : Native S T :=
  ⟨o.name.artifact,o.name.state,o.name.store,o.name.batch,o.entryRow,o.entryRoot,
    o.admissions,o.emissions,o.valueRows,o.effectRows,o.relations,
    BoundedAncestryR61.dependencyRows o.name.state o.dependencies,
    o.origins,o.facts,o.views,o.operations⟩

def native (o : Owner S T) : Native S T := BoundedAncestryR61.native (base o) o.dependencies

/-- Coordinates of the actual use select a plan, owner/component constructor
and permission. Registration/Lambda/annotation/row are read, not expected values
provided by the caller. R62 still checks the semantic incidence independently. -/
def internal (o : Owner S T) (c : Call S) : Option (InternalRootPolicyR62.Request S T) := do
  let u : InternalPermissionIncidenceR45.UseId Nat (Key S T) := ⟨o.name.artifact,.source c.useOccurrence⟩
  let p ← (SourceInternalContextR55.internalInputs (source o)).plan u
  let selected ← InternalRootPolicyR62.ownerSelection (source o) p.targetOwner p.targetRootComponent
  let permission ← SourceInternalContextR55.unique
    (fun p => decide (p.registration = selected.registration)) o.permissions
  pure ⟨u,p.sourceOwner,p.targetOwner,selected.registration,selected.lambda,
    permission.annotationPosition,permission.sourceRow⟩

def catchSource (o : Owner S T) (c : Call S) : Option (SourceInternalContextR55.Catch (Key S T)) :=
  SourceInternalContextR55.unique (fun found => decide (found.occurrence = .source c.catchOccurrence)) o.catches

def catchFact (o : Owner S T) (c : Call S) : Option (SourceFact S T) := do
  let retained ← catchSource o c
  unique (fun f => decide (Key.source f.occurrence = retained.edgeScrutinee ∧ f.slot = 51) &&
    match f.identity with | .collected batch _ => decide (batch = o.name.batch) | _ => false) o.facts

def catchRoot (f : SourceFact S T) : Option EffectEndpoint :=
  match f.canonicalLower with | .effect e => some e | _ => none

/-- Compute the common terminal by enumerating all owner views for the exact
operation identity, declaration and family; no expected endpoint is supplied. -/
def target (o : Owner S T) (c : Call S) : Option EffectEndpoint := do
  let operation ← unique (fun op => decide (op.occurrence = c.providerOccurrence)) o.operations
  match providers (native o) (.source operation.occurrence) (.source operation.declaration) (.source operation.family) with
  | [.effectAtom state e] => if state = o.name.state then some e else none
  | _ => none

def terminal (o : Owner S T) (c : Call S) : EffectEndpoint := (target o c).getD .bottomPositive

def canonicalEntry (o : Owner S T) : Option Nat :=
  (unique (fun r => decide (r.state = o.name.state ∧ r.index = o.entryRow)) o.effectRows).map EffectRow.canonical

structure Package (S T : Type) where
  source : InternalRootPolicyR62.Source S T
  base : Native S T
  records : List BoundedAncestryR61.Record
  internal : InternalRootPolicyR62.Request S T
  entry : Query
  catchSearch : Query
  entryCanonical : Nat
  selectedCatch : SourceFact S T

def package (o : Owner S T) (c : Call S) (q : InternalRootPolicyR62.Request S T)
    (f : SourceFact S T) (root : EffectEndpoint) (canonical : Nat) : Package S T :=
  ⟨source o,base o,o.dependencies,q,⟨.row o.entryRow,terminal o c,.entrySearch⟩,
    ⟨root,terminal o c,.catchSearch⟩,canonical,f⟩

/-- Fallible finite construction. Checks precede package creation and preserve
every competing record. Canonical entry is retained alongside raw entry. -/
def extract (o : Owner S T) (c : Call S) : Option (Package S T) := do
  if c.owner ≠ o.name then none else do
    if ¬ Owned (base o) then none else do
      if ¬ (o.formals.map (fun f => (f.owner,f.lambdaIndex))).Nodup then none else do
        let canonical ← canonicalEntry o
        let q ← internal o c
        let f ← catchFact o c
        let root ← catchRoot f
        if (target o c).isSome then pure (package o c q f root canonical) else none

theorem extract_exact (o : Owner S T) (c : Call S) (p : Package S T)
    (success : extract o c = some p) :
    c.owner = o.name ∧ Owned (base o) ∧
    (o.formals.map (fun f => (f.owner,f.lambdaIndex))).Nodup ∧
    ∃ canonical q f root, canonicalEntry o = some canonical ∧ internal o c = some q ∧
      catchFact o c = some f ∧ catchRoot f = some root ∧ (target o c).isSome = true ∧ p = package o c q f root canonical := by
  unfold extract at success
  split at success
  · simp at success
  next own =>
    split at success
    · simp at success
    next owned =>
      split at success
      · simp at success
      next uniqueFormals =>
        cases ce : canonicalEntry o with
        | none => simp [ce] at success
        | some canonical =>
          cases iq : internal o c with
          | none => simp [ce,iq] at success
          | some q =>
            cases cf : catchFact o c with
            | none => simp [ce,iq,cf] at success
            | some f =>
              cases cr : catchRoot f with
              | none => simp [ce,iq,cf,cr] at success
              | some root =>
                cases tt : target o c with
                | none => simp [ce,iq,cf,tt] at success
                | some t =>
                  have same : package o c q f root canonical = p := by simpa [ce,iq,cf,cr,tt] using success
                  exact ⟨Decidable.of_not_not own,Decidable.of_not_not owned,
                    Decidable.of_not_not uniqueFormals,canonical,q,f,root,rfl,rfl,rfl,cr,by simp,same.symm⟩

theorem foreign_owner_rejected (o : Owner S T) (c : Call S) (foreign : c.owner ≠ o.name) :
    extract o c = none := by simp [extract,foreign]

theorem same_batch_foreign_state_rejected (o : Owner S T) (c : Call S)
    (foreign : c.owner.state ≠ o.name.state) : extract o c = none :=
  foreign_owner_rejected o c (fun same => foreign (congrArg OwnerName.state same))

omit [DecidableEq S] [DecidableEq T] in
/-- Source inventories are literal owner fields, including all competitors,
duplicates, recipes and native TermViews; no filter is used in construction. -/
theorem source_inventory_equations (o : Owner S T) :
    (source o).formals = o.formals ∧ (source o).parameterRecipes = o.parameterRecipes ∧
    (source o).schedules = o.schedules ∧ (source o).sources = o.sources ∧
    (source o).sourceOwners = o.sourceOwners ∧ (source o).occupiedDomains = o.occupiedDomains ∧
    (source o).retainedRegistrations = o.retainedRegistrations ∧
    (source o).constructions = o.constructions ∧ (source o).permissions = o.permissions ∧
    (source o).receipts = o.receipts ∧ (source o).plans = o.plans ∧
    (source o).recipes = o.recipes ∧ (source o).admittedFacts = o.admittedFacts ∧
    (source o).componentTerms = o.componentTerms ∧ (source o).termViews = o.termViews :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

omit [DecidableEq S] [DecidableEq T] in
theorem native_inventory_equations (o : Owner S T) :
    (native o).admissions = o.admissions ∧ (native o).emissions = o.emissions ∧
    (native o).valueRows = o.valueRows ∧ (native o).effectRows = o.effectRows ∧
    (native o).origins = o.origins ∧ (native o).facts = o.facts ∧
    (native o).views = o.views ∧ (native o).operations = o.operations ∧
    (native o).relations = o.relations.zipIdx.map (fun (r,i) => {r with state := o.name.state,index := i}) ∧
    (native o).dependencies = BoundedAncestryR61.dependencyRows o.name.state o.dependencies :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

omit [DecidableEq S] [DecidableEq T] in
theorem permission_lookup (o : Owner S T) (index : Nat) :
    (source o).permissions[index]? = o.permissions[index]? := rfl

omit [DecidableEq S] [DecidableEq T] in
theorem emission_lookup (o : Owner S T) (index : Nat) :
    (native o).emissions[index]? = o.emissions[index]? := rfl

omit [DecidableEq S] [DecidableEq T] in
theorem all_permissions_retained (o : Owner S T) (p : SourceInternalContextR55.Permission (Key S T)) :
    p ∈ (source o).permissions ↔ p ∈ o.permissions := Iff.rfl

theorem all_provider_competitors_retained (o : Owner S T) (provider declaration family candidate : Key S T) :
    candidate ∈ providers (native o) provider declaration family ↔
    ∃ v ∈ o.views, ∃ f ordinal, (f,ordinal) ∈ v.allowed.zipIdx ∧
      v.state = o.name.state ∧ operationOrigin v.origin provider declaration ∧ family = .source f ∧
      candidate = .effectAtom o.name.state (.annotationMember v.index ordinal) :=
  provider_inventory_coverage (native o) provider declaration family candidate

theorem ordered_dependency_equations (o : Owner S T) :
    (current (native o)).dependencies = BoundedAncestryR61.edges o.dependencies ∧
    (native o).relations.length = o.relations.length :=
  ⟨BoundedAncestryR61.native_edges (base o) o.dependencies,
    BoundedAncestryR61.native_relation_count (base o) o.dependencies⟩

theorem fact_namespaces_disjoint (store batch index : Nat) :
    Fact.semantic store index ≠ Fact.collected batch index := by intro h; cases h

theorem unique_success {A : Type} (test : A → Bool) (xs : List A) (value : A)
    (success : SourceInternalContextR55.unique test xs = some value) :
    value ∈ xs ∧ test value = true := by
  cases filtered : xs.filter test with
  | nil => simp [SourceInternalContextR55.unique,filtered] at success
  | cons head tail =>
    cases tail with
    | cons next rest => simp [SourceInternalContextR55.unique,filtered] at success
    | nil =>
      have same : head = value := by simpa [SourceInternalContextR55.unique,filtered] using success
      subst head
      have present : value ∈ xs.filter test := by rw [filtered]; simp
      exact List.mem_filter.mp present

theorem catch_request_namespace (o : Owner S T) (c : Call S) (f : SourceFact S T)
    (selected : catchFact o c = some f) :
    ∃ retained ∈ o.catches, retained.occurrence = .source c.catchOccurrence ∧
      f ∈ o.facts ∧ Key.source f.occurrence = retained.edgeScrutinee ∧ f.slot = 51 ∧
      ∃ index, f.identity = .collected o.name.batch index := by
  unfold catchFact at selected
  cases sourceRead : catchSource o c with
  | none => simp [sourceRead] at selected
  | some retained =>
    simp only [sourceRead] at selected
    have sourceReads := unique_success _ o.catches retained sourceRead
    have reads := unique_success _ o.facts f selected
    refine ⟨retained,sourceReads.1,of_decide_eq_true sourceReads.2,reads.1,?_,?_,?_⟩
    · exact (of_decide_eq_true (Bool.and_eq_true_iff.mp reads.2).1).1
    · exact (of_decide_eq_true (Bool.and_eq_true_iff.mp reads.2).1).2
    · have tagged := (Bool.and_eq_true_iff.mp reads.2).2
      cases identity : f.identity with
      | semantic store index => simp [identity] at tagged
      | collected batch index =>
        have same : batch = o.name.batch := of_decide_eq_true (by simpa [identity] using tagged)
        exact ⟨index,by simp [same]⟩

omit [DecidableEq S] [DecidableEq T] in
theorem canonical_entry_from_owner (o : Owner S T) (canonical : Nat)
    (read : canonicalEntry o = some canonical) :
    ∃ r ∈ o.effectRows, r.state = o.name.state ∧ r.index = o.entryRow ∧ r.canonical = canonical := by
  unfold canonicalEntry at read
  cases selected : unique (fun r => decide (r.state = o.name.state ∧ r.index = o.entryRow)) o.effectRows with
  | none => rw [selected] at read; cases read
  | some r =>
    rw [selected] at read
    have same : r.canonical = canonical := Option.some.inj read
    have present := unique_success _ o.effectRows r selected
    have coordinates := of_decide_eq_true present.2
    exact ⟨r,present.1,coordinates.1,coordinates.2,same⟩

omit [DecidableEq T] in
theorem source_slot_zero_is_semantic (n : Native S T) (occurrence : S) (id : Fact)
    (read : sourceFact n (.source occurrence,0) = some id) :
    ∃ index, id = .semantic n.store index := by
  change (unique (fun f => decide (f.occurrence = occurrence ∧ f.slot = 0) &&
    match f.identity with | .collected owner _ => decide (owner = n.batch ∧ (0 : Nat) = 51)
                          | .semantic owner _ => decide (owner = n.store ∧ (0 : Nat) ≠ 51)) n.facts).map SourceFact.identity = some id at read
  cases selected : unique (fun f => decide (f.occurrence = occurrence ∧ f.slot = 0) &&
    match f.identity with | .collected owner _ => decide (owner = n.batch ∧ (0 : Nat) = 51)
                          | .semantic owner _ => decide (owner = n.store ∧ (0 : Nat) ≠ 51)) n.facts with
  | none => rw [selected] at read; cases read
  | some f =>
    rw [selected] at read
    have same : f.identity = id := Option.some.inj read
    have test := (Bool.and_eq_true_iff.mp (unique_success _ n.facts f selected).2).2
    cases tagged : f.identity with
    | collected owner index => simp [tagged] at test
    | semantic owner index =>
      have own : owner = n.store := by simpa [tagged] using test
      exact ⟨index,by rw [← same,tagged,own]⟩

omit [DecidableEq S] [DecidableEq T] in
theorem source_and_row_namespaces_disjoint (s : S) (state index : Nat) :
    (Key.source s : Key S T) ≠ .effectRow state index := by intro h; cases h

omit [DecidableEq S] [DecidableEq T] in
theorem raw_and_canonical_fact_equations (o : Owner S T) (index : Nat) (f : SourceFact S T)
    (lookup : o.facts[index]? = some f) :
    (native o).facts[index]? = some f ∧
    ((native o).facts[index]?).map (fun f => (f.rawLower,f.rawUpper)) = some (f.rawLower,f.rawUpper) ∧
    ((native o).facts[index]?).map (fun f => (f.canonicalLower,f.canonicalUpper)) = some (f.canonicalLower,f.canonicalUpper) := by
  change o.facts[index]? = some f ∧ _
  simp [native,base,BoundedAncestryR61.native,lookup]

theorem internal_request_equation (o : Owner S T) (c : Call S) (q : InternalRootPolicyR62.Request S T)
    (built : internal o c = some q) :
    q.use = ⟨o.name.artifact,.source c.useOccurrence⟩ ∧
    ∃ p selected permission,
      (SourceInternalContextR55.internalInputs (source o)).plan q.use = some p ∧
      InternalRootPolicyR62.ownerSelection (source o) p.targetOwner p.targetRootComponent = some selected ∧
      SourceInternalContextR55.unique (fun p => decide (p.registration = selected.registration)) o.permissions = some permission ∧
      q.sourceOwner = p.sourceOwner ∧ q.targetOwner = p.targetOwner ∧
      q.registration = selected.registration ∧ q.lambda = selected.lambda ∧
      q.annotationPosition = permission.annotationPosition ∧ q.rowPosition = permission.sourceRow := by
  unfold internal at built
  cases planRead : (SourceInternalContextR55.internalInputs (source o)).plan ⟨o.name.artifact,.source c.useOccurrence⟩ with
  | none => simp [planRead] at built
  | some p =>
    cases selectedRead : InternalRootPolicyR62.ownerSelection (source o) p.targetOwner p.targetRootComponent with
    | none => simp [planRead,selectedRead] at built
    | some selected =>
      cases permissionRead : SourceInternalContextR55.unique (fun p => decide (p.registration = selected.registration)) o.permissions with
      | none => simp [planRead,selectedRead,permissionRead] at built
      | some permission =>
        have same : (⟨⟨o.name.artifact,.source c.useOccurrence⟩,p.sourceOwner,p.targetOwner,
          selected.registration,selected.lambda,permission.annotationPosition,permission.sourceRow⟩ : InternalRootPolicyR62.Request S T) = q := by
          simpa [planRead,selectedRead,permissionRead] using built
        subst q
        exact ⟨rfl,p,selected,permission,planRead,selectedRead,permissionRead,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem constructed_request_coordinates (o : Owner S T) (c : Call S) (p : Package S T)
    (success : extract o c = some p) :
    p.source = source o ∧ p.base = base o ∧ p.records = o.dependencies ∧
    p.entry = ⟨.row o.entryRow,terminal o c,.entrySearch⟩ ∧
    p.catchSearch.mode = .catchSearch ∧ p.catchSearch.target = terminal o c ∧
    canonicalEntry o = some p.entryCanonical ∧
    catchFact o c = some p.selectedCatch ∧
    p.selectedCatch.canonicalLower = .effect p.catchSearch.root ∧ internal o c = some p.internal := by
  obtain ⟨_,_,_,canonical,q,f,root,ce,iq,cf,cr,_,same⟩ := extract_exact o c p success
  subst p
  have lower : f.canonicalLower = .effect root := by
    unfold catchRoot at cr
    cases h : f.canonicalLower with
    | value _ => simp [h] at cr
    | effect e => simp [h] at cr; subst root; rfl
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,ce,cf,lower,iq⟩

theorem raw_entry_is_not_replaced (o : Owner S T) (c : Call S) (p : Package S T)
    (success : extract o c = some p) (different : o.entryRow ≠ p.entryCanonical) :
    p.entry.root ≠ .row p.entryCanonical := by
  have raw := (constructed_request_coordinates o c p success).2.2.2.1
  rw [raw]
  intro same
  exact different (EffectEndpoint.row.inj same)

theorem target_from_complete_provider_inventory (o : Owner S T) (c : Call S) (t : EffectEndpoint)
    (built : target o c = some t) :
    ∃ op, unique (fun op => decide (op.occurrence = c.providerOccurrence)) o.operations = some op ∧
      providers (native o) (.source op.occurrence) (.source op.declaration) (.source op.family) =
        [.effectAtom o.name.state t] := by
  unfold target at built
  cases read : unique (fun op => decide (op.occurrence = c.providerOccurrence)) o.operations with
  | none => simp [read] at built
  | some op =>
    refine ⟨op,rfl,?_⟩
    rw [read] at built
    change (match providers (native o) (.source op.occurrence) (.source op.declaration) (.source op.family) with
      | [.effectAtom state e] => if state = o.name.state then some e else none
      | _ => none) = some t at built
    split at built
    next state e candidates =>
      split at built
      next same =>
        have result : e = t := Option.some.inj built
        simpa only [same,result] using candidates
      next different => cases built
    next different => cases built

theorem constructed_terminal_checked (o : Owner S T) (c : Call S) (p : Package S T)
    (success : extract o c = some p) :
    target o c = some p.entry.target ∧ p.catchSearch.target = p.entry.target := by
  obtain ⟨_,_,_,canonical,q,f,root,_,_,_,_,has,same⟩ := extract_exact o c p success
  subst p
  refine ⟨?_,rfl⟩
  change target o c = some (terminal o c)
  cases selected : target o c with
  | none => simp [selected] at has
  | some t => simp [terminal,selected]

theorem constructed_internal_fact_namespace (o : Owner S T) (c : Call S) (p : Package S T)
    (success : extract o c = some p)
    (r : InternalRootPolicyR62.Root (source o) (native o) p.internal) :
    ∃ index, r.incidence.probe.fact = .semantic o.name.store index := by
  have coordinates := constructed_request_coordinates o c p success
  have iq := coordinates.2.2.2.2.2.2.2.2.2
  have use := (internal_request_equation o c p.internal iq).1
  have occurrence : p.internal.use.occurrence = .source c.useOccurrence := congrArg (fun u => u.occurrence) use
  have read := (InternalRootPolicyR62.root_native_projection (source o) (native o) p.internal r).2.2.2.2
  rw [occurrence] at read
  exact source_slot_zero_is_semantic (native o) c.useOccurrence r.incidence.probe.fact read

def readers (p : Package S T) (schedule : Nat → Nat → BoundedAncestryR61.Schedule) : Readers S T :=
  InternalRootPolicyR62.readers p.source p.base p.records p.internal schedule

def request (p : Package S T) : Mode → Query
  | .entrySearch => p.entry | .catchSearch => p.catchSearch

theorem constructed_same_inputs_decoder (o : Owner S T) (c : Call S) (p : Package S T)
    (success : extract o c = some p) (schedule : Nat → Nat → BoundedAncestryR61.Schedule)
    (search : Search S T) :
    ReachedSlotSearchR58.LocalDecode (readers p schedule) (inputs (native o) search) := by
  obtain ⟨_,_,_,canonical,q,f,root,_,_,_,_,_,same⟩ := extract_exact o c p success
  subst p
  exact InternalRootPolicyR62.same_inputs_decoder (source o) (base o) o.dependencies q schedule search

/-- R62 applied to exactly the constructed owner/package. The successful
outer Run, checked goal and terminal equality remain unchanged premises. -/
theorem constructed_candidates_apply_consumer (o : Owner S T) (c : Call S) (p : Package S T)
    (success : extract o c = some p) (schedule : Nat → Nat → BoundedAncestryR61.Schedule)
    (search : Search S T) (q : Query) (limits : Limits) (resource : Resource)
    (results : List (Branch S T))
    (run : Run (readers p schedule) q limits (.live ⟨resource,[initial q],[],.pop⟩) (.success results))
    (goal : Branch S T) (checked : Checked (readers p schedule) q goal) (terminal : goal.endpoint = q.target) :
    goal ∈ results ∧ AuthenticatedResidualConsumerR49.pathCheck (inputs (native o) search)
      (ReachedSlotSearchR58.encodedEndpoint (readers p schedule) q.root)
      (goal.steps.map ProviderNativeContextR57.step)
      (ReachedSlotSearchR58.encodedEndpoint (readers p schedule) q.target) = true ∧
    AuthenticatedResidualConsumerR49.Arrival (inputs (native o) search)
      (ReachedSlotSearchR58.encodedEndpoint (readers p schedule) q.target)
      (ReachedSlotSearchR58.encodedEndpoint (readers p schedule) q.root) := by
  obtain ⟨_,_,_,canonical,request,f,root,_,_,_,_,_,same⟩ := extract_exact o c p success
  subst p
  exact InternalRootPolicyR62.callback_free_candidates_apply_consumer
    (source o) (base o) o.dependencies request schedule search q limits resource results run goal checked terminal

theorem constructed_call_candidates_apply_consumer (o : Owner S T) (c : Call S) (p : Package S T)
    (success : extract o c = some p) (schedule : Nat → Nat → BoundedAncestryR61.Schedule)
    (search : Search S T) (mode : Mode) (limits : Limits) (resource : Resource)
    (results : List (Branch S T))
    (run : Run (readers p schedule) (request p mode) limits
      (.live ⟨resource,[initial (request p mode)],[],.pop⟩) (.success results))
    (goal : Branch S T) (checked : Checked (readers p schedule) (request p mode) goal)
    (terminal : goal.endpoint = (request p mode).target) :
    goal ∈ results ∧ AuthenticatedResidualConsumerR49.pathCheck (inputs (native o) search)
      (encodedEndpoint (readers p schedule) (request p mode).root)
      (goal.steps.map ProviderNativeContextR57.step)
      (encodedEndpoint (readers p schedule) (request p mode).target) = true ∧
    AuthenticatedResidualConsumerR49.Arrival (inputs (native o) search)
      (encodedEndpoint (readers p schedule) (request p mode).target)
      (encodedEndpoint (readers p schedule) (request p mode).root) :=
  constructed_candidates_apply_consumer o c p success schedule search (request p mode)
    limits resource results run goal checked terminal

theorem constructed_first_entry_certificates (o : Owner S T) (c : Call S) (p : Package S T)
    (success : extract o c = some p) (schedule : Nat → Nat → BoundedAncestryR61.Schedule)
    (b : Branch S T) (physical : Physical T) (result : Option Nat)
    (accepted : ReachedSlotSearchR58.policy (readers p schedule) .entrySearch
      {b with useRoot := none,steps := []} physical = .ok result) :
    ∃ r : InternalRootPolicyR62.Root (source o) (native o) p.internal,
      InternalRootPolicyR62.readRoot (source o) (native o) p.internal physical.emissionIndex = .ok r ∧
      InternalPermissionIncidenceR45.extract (SourceInternalContextR55.internalInputs (source o))
        p.internal r.incidence.probe = some (InternalPermissionIncidenceR45.certificate p.internal r.incidence.probe) ∧
      (r.receipt.emissionIndex = physical.emissionIndex ∧ r.receipt.admissionIndex = physical.admissionIndex ∧
        r.receipt.slot = physical.emission.physical ∧ r.receipt.bound = physical.emission.bound) ∧
      ∃ witness, CurrentEmissionOwnershipR47.Matches (current (native o))
        (InternalRootPolicyR62.rootQuery (native o) p.internal r.incidence r.root)
        {ProviderNativeContextR57.physical r.value with ancestry := witness} := by
  obtain ⟨_,_,_,canonical,q,f,root,_,_,_,_,_,same⟩ := extract_exact o c p success
  subst p
  exact InternalRootPolicyR62.first_entry_success_has_both_certificates
    (source o) (base o) o.dependencies q schedule b physical result accepted

theorem constructed_catch_policy (p : Package S T) (schedule : Nat → Nat → BoundedAncestryR61.Schedule)
    (b : Branch S T) (physical : Physical T) :
    ReachedSlotSearchR58.policy (readers p schedule) .catchSearch b physical = .ok none :=
  InternalRootPolicyR62.catch_keeps_existing_policy p.source p.base p.records p.internal schedule b physical

/- A discharged finite example. The fields reuse existing primitive fixtures;
this is not a native extraction or successful outer-Run receipt. -/
def finiteCatch : SourceFact Nat Nat :=
  ⟨.collected 3 88,200,51,.effect (.row 6),.effect (.row 7),.effect (.row 60),.effect (.row 70)⟩

def finiteOwner : Owner Nat Nat :=
  { name := ⟨99,1,2,3⟩, entryRow := 4, entryRoot := 2
    formals := [fixtureFormal], parameterRecipes := [.source 2], schedules := [.source 999]
    sources := [⟨.source 1,[.lambda (.source 17) (.source 2)]⟩]
    sourceOwners := [(.source 17,.source 1)], occupiedDomains := [], retainedRegistrations := []
    constructions := [fixtureConstruction], permissions := [fixturePermission]
    receipts := [fixtureReceipt], plans := [fixturePlan], recipes := [⟨.source 17,some 0,20⟩]
    admittedFacts := [⟨.semantic 2 88,.source 100,0,300,400⟩,⟨.semantic 2 89,.source 17,2,200,300⟩]
    componentTerms := [(20,300),(21,400)]
    termViews := [(200,.positiveFunction 201),(201,.negativeEffectVariable (.effectRow 1 4))]
    admissions := fixtureNative.admissions, emissions := fixtureNative.emissions
    valueRows := [], effectRows := fixtureNative.effectRows, relations := fixtureNative.relations
    dependencies := [.derived 0 2], origins := fixtureNative.origins
    facts := [⟨.semantic 2 88,100,0,.value (.positiveFunction 300),.value (.negativeFunction 400),.value (.positiveFunction 300),.value (.negativeFunction 400)⟩,finiteCatch], views := [fixtureView], operations := [⟨300,301,7⟩], catches := [fixtureCatch] }

def finiteCall : Call Nat := ⟨⟨99,1,2,3⟩,100,400,300⟩
def finitePackage : Package Nat Nat :=
  package finiteOwner finiteCall InternalRootPolicyR62.fixtureRequest finiteCatch (.row 60) 40

theorem concrete_package_is_constructed : extract finiteOwner finiteCall = some finitePackage := rfl

theorem concrete_raw_entry_canonical_catch :
    finitePackage.entry.root = .row 4 ∧ finitePackage.entryCanonical = 40 ∧
    finitePackage.selectedCatch.rawLower = .effect (.row 6) ∧
    finitePackage.catchSearch.root = .row 60 ∧
    finitePackage.selectedCatch.canonicalLower = .effect (.row 60) := ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem concrete_foreign_and_incomplete_rejected :
    extract finiteOwner {finiteCall with owner := ⟨99,2,2,3⟩} = none ∧
    extract {finiteOwner with permissions := []} finiteCall = none ∧
    extract {finiteOwner with permissions := [fixturePermission,fixturePermission]} finiteCall = none ∧
    extract {finiteOwner with views := [fixtureView,fixtureView]} finiteCall = none ∧
    extract {finiteOwner with facts := [⟨.semantic 2 88,100,0,.value (.positiveFunction 300),.value (.negativeFunction 400),.value (.positiveFunction 300),.value (.negativeFunction 400)⟩]} finiteCall = none :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem concrete_distinct_provider_competitor_rejected :
    extract {finiteOwner with views := [fixtureView,{fixtureView with index := 1}]} finiteCall = none := rfl

theorem concrete_constructed_first_entry :
    ReachedSlotSearchR58.policy (readers finitePackage InternalRootPolicyR62.fixtureSchedule)
      .entrySearch InternalRootPolicyR62.fixtureBranch InternalRootPolicyR62.fixturePhysical = .ok (some 2) := rfl

end YulangClosure.RustInventoryRequestR63
