import YulangClosure.ProviderNativeContextR57

/-!
R65 versioned occurrence-qualified finite readers. Selection enumerates every
edge at the source key before resolving the owning semantic table. The selected
native-fact comparison includes identity and all endpoints. This models finite
records, not Rust pointer/token authenticity or successful native execution.
R55/R57 remain unchanged; no equivalence to their FactId-only readers is claimed.
-/
namespace YulangClosure.OccurrenceQualifiedFactReadersR65
open ProviderNativeContextR57

structure FactRow (T : Type) where
  identity : Fact
  lower : T
  upper : T
  rawLower : Endpoint T
  rawUpper : Endpoint T
  canonicalLower : Endpoint T
  canonicalUpper : Endpoint T
  deriving DecidableEq

structure Edge (S : Type) where
  edgeIndex : Nat
  fact : Fact
  occurrence : S
  slot : Nat
  deriving DecidableEq

structure Inventory (S T : Type) where
  store : Nat
  facts : List (FactRow T)
  edges : List (Edge S)

structure Read (S T : Type) where
  edge : Edge S
  fact : FactRow T
  deriving DecidableEq

variable {S T : Type} [DecidableEq S] [DecidableEq T]

/-- No fact, owner or endpoint predicate prefilters provenance competitors. -/
def candidates (n : Inventory S T) (occurrence : S) (slot : Nat) : List (Edge S) :=
  n.edges.filter (fun edge => decide (edge.occurrence = occurrence ∧ edge.slot = slot))

omit [DecidableEq T] in
theorem every_edge_at_key (n : Inventory S T) (occurrence : S) (slot : Nat) (edge : Edge S) :
    edge ∈ candidates n occurrence slot ↔
      edge ∈ n.edges ∧ edge.occurrence = occurrence ∧ edge.slot = slot := by
  simp [candidates]

def resolve (n : Inventory S T) (id : Fact) : Option (FactRow T) :=
  match id with
  | .semantic owner index =>
      if owner = n.store then
        (n.facts[index]?).bind (fun fact => if fact.identity = id then some fact else none)
      else none
  | .collected _ _ => none

def readAt (n : Inventory S T) (occurrence : S) (slot : Nat) : Option (Read S T) :=
  match candidates n occurrence slot with
  | [edge] => (resolve n edge.fact).map (fun fact => ⟨edge, fact⟩)
  | _ => none

/-- Full selected-fact comparison includes raw/canonical and term endpoints.
Native pointer identity still needs an independently authenticated encoding. -/
def readSelectedAt (n : Inventory S T) (occurrence : S) (slot : Nat)
    (selected : FactRow T) : Option (Read S T) := do
  let found ← readAt n occurrence slot
  if found.fact = selected then some found else none

omit [DecidableEq S] [DecidableEq T] in
theorem resolve_iff (n : Inventory S T) (id : Fact) (f : FactRow T) :
    resolve n id = some f ↔ ∃ index,
      id = .semantic n.store index ∧ n.facts[index]? = some f ∧ f.identity = id := by
  cases id with
  | collected owner index => simp [resolve]
  | semantic owner index =>
      by_cases same : owner = n.store
      · subst owner
        simp only [resolve, ite_true]
        cases atIndex : n.facts[index]? with
        | none => simp [atIndex]
        | some row =>
            by_cases identity : row.identity = .semantic n.store index
            · simp [atIndex, identity, eq_comm]
              intro equal
              subst f
              exact identity
            · simp [atIndex, identity]
              intro equal
              subst row
              exact identity
      · simp [resolve, same]

omit [DecidableEq T] in
theorem readAt_iff (n : Inventory S T) (occurrence : S) (slot : Nat) (out : Read S T) :
    readAt n occurrence slot = some out ↔
      candidates n occurrence slot = [out.edge] ∧ resolve n out.edge.fact = some out.fact := by
  unfold readAt
  cases selected : candidates n occurrence slot with
  | nil => simp
  | cons edge rest =>
      cases rest with
      | cons second tail => simp
      | nil =>
          cases found : resolve n edge.fact with
          | none =>
              simp [found]
              intro equal
              subst edge
              simp [found]
          | some f =>
              cases out with
              | mk outEdge outFact =>
                  simp [found, Read.mk.injEq]
                  intro equal
                  subst outEdge
                  simp [found]

omit [DecidableEq T] in
theorem readAt_coordinate (n : Inventory S T) (occurrence : S) (slot : Nat) (out : Read S T)
    (accepted : readAt n occurrence slot = some out) :
    out.edge ∈ n.edges ∧ out.edge.occurrence = occurrence ∧ out.edge.slot = slot ∧
      out.fact.identity = out.edge.fact := by
  obtain ⟨only, resolved⟩ := (readAt_iff n occurrence slot out).mp accepted
  have member : out.edge ∈ candidates n occurrence slot := by rw [only]; simp
  obtain ⟨retained, key⟩ := List.mem_filter.mp member
  obtain ⟨_, _, _, identity⟩ := (resolve_iff n out.edge.fact out.fact).mp resolved
  exact ⟨retained, (of_decide_eq_true key).1, (of_decide_eq_true key).2, identity⟩

theorem readSelectedAt_iff (n : Inventory S T) (occurrence : S) (slot : Nat)
    (selected : FactRow T) (out : Read S T) :
    readSelectedAt n occurrence slot selected = some out ↔
      readAt n occurrence slot = some out ∧ out.fact = selected := by
  unfold readSelectedAt
  cases found : readAt n occurrence slot with
  | none => simp
  | some row =>
      by_cases same : row.fact = selected
      · simp [same, eq_comm]
        intro equal
        subst out
        exact same.symm
      · simp [same]
        intro equal
        subst row
        exact same

omit [DecidableEq T] in
theorem dangling_rejected (n : Inventory S T) (occurrence : S) (slot : Nat) (edge : Edge S)
    (only : candidates n occurrence slot = [edge]) (dangling : resolve n edge.fact = none) :
    readAt n occurrence slot = none := by simp [readAt, only, dangling]

omit [DecidableEq T] in
theorem same_key_ambiguity_rejected (n : Inventory S T) (occurrence : S) (slot : Nat)
    (first second : Edge S) (rest : List (Edge S))
    (ambiguous : candidates n occurrence slot = first :: second :: rest) :
    readAt n occurrence slot = none := by simp [readAt, ambiguous]

omit [DecidableEq T] in
theorem foreign_key_extension_preserved (n : Inventory S T) (occurrence : S) (slot : Nat)
    (extra : List (Edge S))
    (foreign : ∀ edge ∈ extra, ¬ (edge.occurrence = occurrence ∧ edge.slot = slot)) :
    readAt { n with edges := n.edges ++ extra } occurrence slot = readAt n occurrence slot := by
  have empty : extra.filter (fun edge => decide (edge.occurrence = occurrence ∧ edge.slot = slot)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro edge member
    simpa using foreign edge member
  simp only [readAt, candidates, List.filter_append, empty, List.append_nil]
  rfl

omit [DecidableEq S] [DecidableEq T] in
theorem foreign_owner_rejected (n : Inventory S T) (owner index : Nat)
    (foreign : owner ≠ n.store) : resolve n (.semantic owner index) = none := by
  simp [resolve, foreign]

omit [DecidableEq S] [DecidableEq T] in
theorem indexed_identity_mismatch_rejected (n : Inventory S T) (index : Nat) (row : FactRow T)
    (atIndex : n.facts[index]? = some row) (mismatch : row.identity ≠ .semantic n.store index) :
    resolve n (.semantic n.store index) = none := by
  simp [resolve, atIndex, mismatch]

omit [DecidableEq T] in
theorem shared_fact_at_distinct_keys (n : Inventory S T) (first second : Edge S) (fact : FactRow T)
    (distinct : (first.occurrence, first.slot) ≠ (second.occurrence, second.slot))
    (firstOnly : candidates n first.occurrence first.slot = [first])
    (secondOnly : candidates n second.occurrence second.slot = [second])
    (shared : first.fact = second.fact) (owned : resolve n first.fact = some fact) :
    (first.occurrence, first.slot) ≠ (second.occurrence, second.slot) ∧
    readAt n first.occurrence first.slot = some ⟨first, fact⟩ ∧
    readAt n second.occurrence second.slot = some ⟨second, fact⟩ := by
  exact ⟨distinct, (readAt_iff _ _ _ _).mpr ⟨firstOnly, owned⟩,
    (readAt_iff _ _ _ _).mpr ⟨secondOnly, shared ▸ owned⟩⟩

theorem selected_endpoint_mismatch_rejected (n : Inventory S T) (occurrence : S) (slot : Nat)
    (found : Read S T) (selected : FactRow T) (read : readAt n occurrence slot = some found)
    (different : found.fact.identity ≠ selected.identity ∨ found.fact.lower ≠ selected.lower ∨
      found.fact.upper ≠ selected.upper ∨ found.fact.rawLower ≠ selected.rawLower ∨
      found.fact.rawUpper ≠ selected.rawUpper ∨ found.fact.canonicalLower ≠ selected.canonicalLower ∨
      found.fact.canonicalUpper ≠ selected.canonicalUpper) :
    readSelectedAt n occurrence slot selected = none := by
  have unequal : found.fact ≠ selected := by
    intro equal
    subst selected
    rcases different with h | h | h | h | h | h | h <;> exact h rfl
  simp [readSelectedAt, read, unequal]

def sourceFact (n : Inventory S T) (key : Key S T × Nat) : Option Fact :=
  match key.1 with
  | .source occurrence => (readAt n occurrence key.2).map (fun read => read.fact.identity)
  | _ => none

/-- The selected use coordinate is captured before the FactId is checked. -/
def routeFact (n : Inventory S T) (occurrence : Key S T) (id : Fact) : Option (Key S T × T × T) :=
  match occurrence with
  | .source occurrence => do
      let read ← readAt n occurrence 0
      if read.fact.identity = id then some (.source occurrence, read.fact.lower, read.fact.upper) else none
  | _ => none

def lambdaFact (n : Inventory S T) (occurrence : Key S T) : Option (T × T) :=
  match occurrence with
  | .source occurrence => (readAt n occurrence 2).map (fun read => (read.fact.lower, read.fact.upper))
  | _ => none

omit [DecidableEq T] in
theorem route_read_iff (n : Inventory S T) (occurrence : S) (id : Fact) (lower upper : T) :
    routeFact n (.source occurrence) id = some (.source occurrence, lower, upper) ↔
      ∃ out, readAt n occurrence 0 = some out ∧ out.fact.identity = id ∧
        out.fact.lower = lower ∧ out.fact.upper = upper := by
  unfold routeFact
  cases read : readAt n occurrence 0 with
  | none => simp [read]
  | some out =>
      by_cases identity : out.fact.identity = id
      · simp [read, identity]
      · simp [read, identity]

omit [DecidableEq T] in
theorem lambda_read_iff (n : Inventory S T) (occurrence : S) (lower upper : T) :
    lambdaFact n (.source occurrence) = some (lower, upper) ↔
      ∃ out, readAt n occurrence 2 = some out ∧ out.fact.lower = lower ∧ out.fact.upper = upper := by
  simp [lambdaFact, Option.map_eq_some_iff]

def internalInputs (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)
    (n : Inventory S T) (useOccurrence : Key S T) : InternalPermissionIncidenceR45.Inputs Nat (Key S T) T Fact :=
  { SourceInternalContextR55.internalInputs source with
    routeFact := routeFact n useOccurrence
    lambdaFact := lambdaFact n }

theorem route_input_agreement (source : SourceInternalContextR55.Native Nat (Key S T) T Fact)
    (n : Inventory S T) (occurrence : S) (out : Read S T)
    (read : readAt n occurrence 0 = some out) :
    (internalInputs source n (.source occurrence)).routeFact out.fact.identity =
      some (.source occurrence, out.fact.lower, out.fact.upper) ∧
    sourceFact n (.source occurrence, 0) = some out.fact.identity := by
  simp [internalInputs, routeFact, sourceFact, read]

def rootTask (native : Native S T) (n : Inventory S T) (relation : Nat) : Option Fact :=
  if n.store = native.store then do
    let drain ← ProviderNativeContextR57.rootDrain native relation
    let read ← readAt n drain.cause drain.slot
    if drain.taskLower = read.fact.canonicalLower ∧ drain.taskUpper = read.fact.canonicalUpper then
      some read.fact.identity else none
  else none

def rootCandidates (native : Native S T) (n : Inventory S T)
    (use : InternalPermissionIncidenceR45.UseId Nat (Key S T)) (id : Fact) : List Nat :=
  match use.occurrence with
  | .source occurrence =>
      match readAt n occurrence 0 with
      | some read => if n.store = native.store ∧ use.artifact = native.artifact ∧ read.fact.identity = id then
          (native.origins.filter (fun origin =>
            decide (origin.state = native.state ∧ origin.occurrence = occurrence ∧ origin.slot = 0) &&
            match ProviderNativeContextR57.relationRead native origin.relation with
            | some relation => decide (relation.lower = read.fact.canonicalLower ∧ relation.upper = read.fact.canonicalUpper)
            | none => false)).map Origin.relation
        else []
      | none => []
  | _ => []

def current (native : Native S T) (n : Inventory S T) : CurrentEmissionOwnershipR47.Inputs Nat (Key S T) Fact :=
  { ProviderNativeContextR57.current native with
    sourceFact := fun key => if key.2 = 51 then ProviderNativeContextR57.sourceFact native key
      else if n.store = native.store then sourceFact n key else none
    rootTask := rootTask native n
    rootCandidates := rootCandidates native n }

theorem root_task_agreement (native : Native S T) (n : Inventory S T) (relation : Nat)
    (drain : Drain S T) (out : Read S T)
    (owner : n.store = native.store)
    (semanticSlot : drain.slot ≠ 51)
    (drained : ProviderNativeContextR57.rootDrain native relation = some drain)
    (read : readAt n drain.cause drain.slot = some out)
    (endpoints : drain.taskLower = out.fact.canonicalLower ∧ drain.taskUpper = out.fact.canonicalUpper) :
    (current native n).rootTask relation = some out.fact.identity ∧
      (current native n).sourceFact (.source drain.cause, drain.slot) = some out.fact.identity := by
  simp [current, rootTask, sourceFact, owner, semanticSlot, drained, read, endpoints]

theorem root_candidate_agreement (native : Native S T) (n : Inventory S T)
    (occurrence : S) (out : Read S T) (owner : n.store = native.store)
    (read : readAt n occurrence 0 = some out) :
    (current native n).rootCandidates ⟨native.artifact, .source occurrence⟩ out.fact.identity =
      (native.origins.filter (fun origin =>
        decide (origin.state = native.state ∧ origin.occurrence = occurrence ∧ origin.slot = 0) &&
        match ProviderNativeContextR57.relationRead native origin.relation with
        | some relation => decide (relation.lower = out.fact.canonicalLower ∧ relation.upper = out.fact.canonicalUpper)
        | none => false)).map Origin.relation := by
  simp [current, rootCandidates, owner, read]

theorem foreign_native_store_rejected (native : Native S T) (n : Inventory S T)
    (foreign : n.store ≠ native.store) (key : Key S T × Nat) (semanticSlot : key.2 ≠ 51) (relation : Nat)
    (use : InternalPermissionIncidenceR45.UseId Nat (Key S T)) (id : Fact) :
    (current native n).sourceFact key = none ∧
    (current native n).rootTask relation = none ∧
    (current native n).rootCandidates use id = [] := by
  constructor
  · simp [current, foreign, semanticSlot]
  constructor
  · simp [current, rootTask, foreign]
  · simp only [current, rootCandidates]
    cases use.occurrence <;> simp
    rename_i occurrence
    cases readAt n occurrence 0 <;> simp [foreign]

theorem collected_source_reader_retained (native : Native S T) (n : Inventory S T) (occurrence : Key S T) :
    (current native n).sourceFact (occurrence, 51) = ProviderNativeContextR57.sourceFact native (occurrence, 51) := rfl

theorem qualified_internal_extract
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact) (n : Inventory S T)
    (q : InternalPermissionIncidenceR45.Query Nat (Key S T))
    (p : InternalPermissionIncidenceR45.Probe Nat (Key S T) T Fact)
    (reads : InternalPermissionIncidenceR45.OwnerReads (internalInputs source n q.use.occurrence) q p)
    (identity : InternalPermissionIncidenceR45.Identity (internalInputs source n q.use.occurrence) q p) :
    InternalPermissionIncidenceR45.extract (internalInputs source n q.use.occurrence) q p =
      some (InternalPermissionIncidenceR45.certificate q p) ∧
    (InternalPermissionIncidenceR45.certificate q p).use = q.use ∧
    (InternalPermissionIncidenceR45.certificate q p).fact = p.fact ∧
    (InternalPermissionIncidenceR45.certificate q p).permission = p.permission := by
  exact ⟨(InternalPermissionIncidenceR45.accepted_iff _ _ _ _).mpr ⟨reads, identity, rfl⟩, rfl, rfl, rfl⟩

theorem qualified_internal_source_facts
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact) (n : Inventory S T)
    (q : InternalPermissionIncidenceR45.Query Nat (Key S T))
    (p : InternalPermissionIncidenceR45.Probe Nat (Key S T) T Fact)
    (out : InternalPermissionIncidenceR45.Certificate Nat (Key S T) T Fact)
    (accepted : InternalPermissionIncidenceR45.extract (internalInputs source n q.use.occurrence) q p = some out)
    (occurrence lambda : S) (useCoordinate : q.use.occurrence = .source occurrence)
    (lambdaCoordinate : q.lambda = .source lambda) :
    ∃ route construction,
      readAt n occurrence 0 = some route ∧ route.fact.identity = out.fact ∧
      route.fact.lower = out.originalRoot ∧ route.fact.upper = out.useValue ∧
      readAt n lambda 2 = some construction ∧
      construction.fact.lower = out.function ∧ construction.fact.upper = out.originalRoot := by
  have endpoints := InternalPermissionIncidenceR45.accepted_constructor_and_endpoints
    (internalInputs source n q.use.occurrence) q p out accepted
  obtain ⟨_, _, same⟩ := (InternalPermissionIncidenceR45.accepted_iff _ _ _ _).mp accepted
  subst out
  have route := endpoints.2.2.2.1
  have constructorRead := endpoints.1
  change routeFact n q.use.occurrence p.fact = some (q.use.occurrence, p.registeredRoot, p.plan.useValue) at route
  change lambdaFact n q.lambda = some (p.construction.function, p.registeredRoot) at constructorRead
  rw [useCoordinate] at route
  rw [lambdaCoordinate] at constructorRead
  obtain ⟨route, routeRead, identity, lower, upper⟩ := (route_read_iff _ _ _ _ _).mp route
  obtain ⟨construction, constructionRead, function, root⟩ := (lambda_read_iff _ _ _ _).mp constructorRead
  exact ⟨route, construction, routeRead, identity, lower, upper, constructionRead, function, root⟩

def rootQuery (internal : InternalPermissionIncidenceR45.Certificate Nat (Key S T) T Fact)
    (relation : Nat) : CurrentEmissionOwnershipR47.Query Nat (Key S T) Fact :=
  ⟨internal.use, internal.fact, internal.permission.entry, relation⟩

theorem qualified_root_extract
    (source : SourceInternalContextR55.Native Nat (Key S T) T Fact) (n : Inventory S T) (native : Native S T)
    (q : InternalPermissionIncidenceR45.Query Nat (Key S T))
    (p : InternalPermissionIncidenceR45.Probe Nat (Key S T) T Fact)
    (internal : InternalPermissionIncidenceR45.Certificate Nat (Key S T) T Fact)
    (internalAccepted : InternalPermissionIncidenceR45.extract (internalInputs source n q.use.occurrence) q p = some internal)
    (relation : Nat) (physical : CurrentEmissionOwnershipR47.Probe (Key S T))
    (matched : CurrentEmissionOwnershipR47.Matches (current native n) (rootQuery internal relation) physical) :
    ∃ out, CurrentEmissionOwnershipR47.extract (current native n) (rootQuery internal relation) physical = some out ∧
      out.query.use = internal.use ∧ out.query.internalFact = internal.fact ∧
      internal.permission = p.permission ∧ internal.permission.concrete = p.permission.concrete ∧
      CurrentEmissionOwnershipR47.currentBound (current native n) out.evidence.emission.physical =
        some out.evidence.admission.bound ∧
      out.evidence.emission.physical.owner = .effect internal.permission.entry ∧
      CurrentEmissionOwnershipR47.RelationPath (current native n) out.query.rootRelation out.evidence.relation := by
  let out : CurrentEmissionOwnershipR47.Certificate Nat (Key S T) Fact := ⟨rootQuery internal relation, physical⟩
  have accepted : CurrentEmissionOwnershipR47.extract (current native n) (rootQuery internal relation) physical = some out :=
    (CurrentEmissionOwnershipR47.accepted_iff _ _ _ _).mpr ⟨matched, rfl⟩
  exact ⟨out, accepted, CurrentEmissionOwnershipR47.apply_to_internal
    (internalInputs source n q.use.occurrence) q p internal internalAccepted
    (current native n) (rootQuery internal relation) physical out accepted rfl rfl rfl⟩

/-! Successful finite mathematical witnesses. These are not source-qualified
native counterexamples, runtime multiplicity observations, or outer Run receipts. -/
def fixtureRoute : FactRow Nat :=
  ⟨.semantic 2 0, 300, 400, .value (.positiveFunction 300), .value (.negativeFunction 400),
    .value (.positiveFunction 300), .value (.negativeFunction 400)⟩
def fixtureLambda : FactRow Nat :=
  ⟨.semantic 2 1, 200, 300, .value (.positiveFunction 200), .value (.positiveFunction 300),
    .value (.positiveFunction 200), .value (.positiveFunction 300)⟩
def fixtureFirst : Edge Nat := ⟨0, .semantic 2 0, 100, 0⟩
def fixtureSecond : Edge Nat := ⟨1, .semantic 2 0, 101, 0⟩
def fixtureLambdaEdge : Edge Nat := ⟨2, .semantic 2 1, 17, 2⟩
def fixtureInventory : Inventory Nat Nat :=
  ⟨2, [fixtureRoute, fixtureLambda], [fixtureFirst, fixtureSecond, fixtureLambdaEdge]⟩

theorem shared_fact_distinct_occurrences_succeed :
    fixtureFirst.fact = fixtureSecond.fact ∧ fixtureFirst.occurrence ≠ fixtureSecond.occurrence ∧
    readAt fixtureInventory 100 0 = some ⟨fixtureFirst, fixtureRoute⟩ ∧
    readAt fixtureInventory 101 0 = some ⟨fixtureSecond, fixtureRoute⟩ ∧
    readSelectedAt fixtureInventory 100 0 fixtureRoute = some ⟨fixtureFirst, fixtureRoute⟩ ∧
    readSelectedAt fixtureInventory 101 0 fixtureRoute = some ⟨fixtureSecond, fixtureRoute⟩ := by decide

def fixtureSource : SourceInternalContextR55.Native Nat (Key Nat Nat) Nat Fact :=
  { ProviderNativeContextR57.fixtureInternal with
    receipts := [{ ProviderNativeContextR57.fixtureReceipt with fact := some (.semantic 2 0) }] }
def fixtureInternalQuery : InternalPermissionIncidenceR45.Query Nat (Key Nat Nat) :=
  SourceInternalContextR55.query ProviderNativeContextR57.fixtureQuery
def fixtureInternalProbe : InternalPermissionIncidenceR45.Probe Nat (Key Nat Nat) Nat Fact :=
  SourceInternalContextR55.probe
    { ProviderNativeContextR57.fixtureProbe with
      fact := .semantic 2 0
      receipt := { ProviderNativeContextR57.fixtureReceipt with fact := some (.semantic 2 0) } }
def fixtureInternalCertificate : InternalPermissionIncidenceR45.Certificate Nat (Key Nat Nat) Nat Fact :=
  InternalPermissionIncidenceR45.certificate fixtureInternalQuery fixtureInternalProbe
def fixtureInternalInputs := internalInputs fixtureSource fixtureInventory fixtureInternalQuery.use.occurrence
def fixtureCurrent := current ProviderNativeContextR57.fixtureNative fixtureInventory
def fixtureRootQuery := rootQuery fixtureInternalCertificate 2
def fixtureRootProbe : CurrentEmissionOwnershipR47.Probe (Key Nat Nat) :=
  ProviderNativeContextR57.physical (ProviderNativeContextR57.fixturePhysical 4 0 0 [0])

theorem finite_qualified_internal_and_root :
    InternalPermissionIncidenceR45.extract fixtureInternalInputs fixtureInternalQuery fixtureInternalProbe =
      some fixtureInternalCertificate ∧
    CurrentEmissionOwnershipR47.extract fixtureCurrent fixtureRootQuery fixtureRootProbe =
      some ⟨fixtureRootQuery, fixtureRootProbe⟩ ∧
    fixtureRootQuery.use = fixtureInternalCertificate.use ∧
    fixtureRootQuery.internalFact = fixtureInternalCertificate.fact ∧
    fixtureRootQuery.rawEntry = fixtureInternalCertificate.permission.entry ∧
    fixtureInternalCertificate.permission.concrete = [.source 7, .source 7, .source 11] := by decide

theorem finite_ambiguity_dangling_owner_and_endpoints_rejected :
    readAt { fixtureInventory with edges := fixtureInventory.edges ++ [fixtureFirst] } 100 0 = none ∧
    readAt { fixtureInventory with edges := [⟨0, .semantic 2 9, 100, 0⟩] } 100 0 = none ∧
    readAt { fixtureInventory with edges := [⟨0, .semantic 3 0, 100, 0⟩] } 100 0 = none ∧
    readSelectedAt fixtureInventory 100 0 { fixtureRoute with upper := 401 } = none ∧
    readSelectedAt fixtureInventory 100 0 { fixtureRoute with canonicalUpper := .value (.negativeFunction 401) } = none := by decide

end YulangClosure.OccurrenceQualifiedFactReadersR65
