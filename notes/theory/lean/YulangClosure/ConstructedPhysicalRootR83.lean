import YulangClosure.ConstructedSourceIncidenceR81
import YulangClosure.DistinctSourceEmissionRootR75

/-!
R82 finite current-record construction of the original R66 Root. The source
incidence comes from R81; raw indexed admissions/emissions and unique source
Origin/drain records are read and checked. No Root, BeforeAncestry, readRoot
success, ownership aggregate or ancestry success is an input. Authentication of
these inventories as an actual Rust execution remains a separate obligation.
-/
namespace YulangClosure.ConstructedPhysicalRootR83

open ProviderNativeContextR57 SourceInternalChoiceR77

variable {S T : Type} [DecidableEq S] [DecidableEq T]

deriving instance DecidableEq for ProviderNativeContextR57.Drain
deriving instance DecidableEq for ProviderNativeContextR57.Origin

def valueEndpoint : Endpoint T → Bool
  | .value _ => true
  | .effect _ => false

def effectEndpoint : Endpoint T → Bool
  | .value _ => false
  | .effect _ => true

theorem value_endpoint_typed (state : Nat) (e : Endpoint T)
    (typed : valueEndpoint e = true) : DistinctSourceEmissionRootR75.IsValue (endpoint (S := S) state e) := by
  cases e with
  | value v => cases v <;> trivial
  | effect e => cases typed

theorem effect_endpoint_typed (state : Nat) (e : Endpoint T)
    (typed : effectEndpoint e = true) : DistinctSourceEmissionRootR75.IsEffect (endpoint (S := S) state e) := by
  cases e with
  | effect e => cases e <;> trivial
  | value v => cases typed

structure Records (S T : Type) where
  occurrence : S
  emission : Emission T
  admission : Admission T
  relation : Nat
  route : OccurrenceQualifiedFactReadersR65.Read S T
  origin : Origin S T
  drain : Drain S T
  sourceRelation : Relation T
  emissionRelation : Relation T

def originCandidates (n : Native S T) (occurrence : S)
    (route : OccurrenceQualifiedFactReadersR65.Read S T) : List (Origin S T) :=
  n.origins.filter (fun o =>
    decide (o.state = n.state ∧ o.occurrence = occurrence ∧ o.slot = 0) &&
    match relationRead n o.relation with
    | some r => decide (r.lower = route.fact.canonicalLower ∧ r.upper = route.fact.canonicalUpper)
    | none => false)

/-- Read one physical emission, its exact indexed admission, then the entire
same-use candidate set before selecting a source Origin. No ancestry search. -/
def readRecords (n : Native S T) (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T) (index : Nat) : Option (Records S T) := do
  let e ← n.emissions[index]?
  let a ← n.admissions[e.admission]?
  let relation ← a.relation
  let occurrence ← match q.use.occurrence with | .source occurrence => some occurrence | _ => none
  let route ← OccurrenceQualifiedFactReadersR65.readAt inventory occurrence 0
  let o ← unique (fun _ => true) (originCandidates n occurrence route)
  let d ← o.drain
  let sourceRelation ← relationRead n o.relation
  let emissionRelation ← relationRead n relation
  pure ⟨occurrence, e, a, relation, route, o, d, sourceRelation, emissionRelation⟩

def physicalValue (index : Nat) (d : Records S T) : Physical T :=
  ⟨d.emission.admission, index, d.admission, d.emission, d.relation, []⟩

/-- Independently executable finite reads/field equations. currentBound is the
existing eight-lane indexed row reader; all other checks retain native records.
There is no successful aggregate certificate among these inputs. -/
def Primitive (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat) (d : Records S T) : Prop :=
  s.artifact = n.artifact ∧
  i.probe.permission.entry = .effectRow n.state n.entryRow ∧
  q.use.artifact = n.artifact ∧ q.use.occurrence = .source d.occurrence ∧
  inventory.store = n.store ∧
  n.emissions[index]? = some d.emission ∧
  n.admissions[d.emission.admission]? = some d.admission ∧
  (n.emissions.map (emission (S := S))).filter
    (fun e => e.physical == (emission (S := S) d.emission).physical) = [emission d.emission] ∧
  d.emission.bound = d.admission.bound ∧ d.emission.state = d.admission.state ∧
  d.emission.readbackSlot = d.emission.physical ∧ d.emission.readbackBound = d.admission.bound ∧
  CurrentEmissionOwnershipR47.currentBound (OccurrenceQualifiedFactReadersR65.current n inventory)
    (slot d.emission.state d.emission.physical) = some (bound d.admission.state d.admission.bound) ∧
  d.admission.relation = some d.relation ∧
  relationRead n d.relation = some d.emissionRelation ∧
  (endpoint (S := S) n.state d.emissionRelation.lower, endpoint n.state d.emissionRelation.upper) =
    CurrentEmissionOwnershipR47.boundPair (bound d.admission.state d.admission.bound) ∧
  d.emission.state = n.state ∧ d.admission.state = n.state ∧
  d.emission.physical.owner = .effect n.entryRow ∧
  d.admission.bound.owner = .effect n.entryRow ∧ d.admission.bound.polarity = .positive ∧
  effectEndpoint d.admission.bound.item = true ∧
  OccurrenceQualifiedFactReadersR65.readAt inventory d.occurrence 0 = some d.route ∧
  d.route.fact.identity = i.probe.fact ∧
  originCandidates n d.occurrence d.route = [d.origin] ∧
  n.origins.filter (fun o => decide (o.state = n.state ∧ o.relation = d.origin.relation)) = [d.origin] ∧
  d.origin.state = n.state ∧ d.origin.occurrence = d.occurrence ∧ d.origin.slot = 0 ∧
  d.origin.drain = some d.drain ∧
  n.origins[d.drain.originIndex]? = some d.origin ∧
  d.drain.state = n.state ∧ d.drain.createdSeed = d.origin.relation ∧
  d.drain.selectedRelation = d.origin.relation ∧ d.drain.incoming = none ∧
  d.drain.replay = false ∧ d.drain.cause = d.occurrence ∧ d.drain.slot = 0 ∧ d.drain.completed = true ∧
  d.drain.taskLower = d.route.fact.canonicalLower ∧ d.drain.taskUpper = d.route.fact.canonicalUpper ∧
  relationRead n d.origin.relation = some d.sourceRelation ∧
  d.sourceRelation.lower = d.route.fact.canonicalLower ∧
  d.sourceRelation.upper = d.route.fact.canonicalUpper ∧
  valueEndpoint d.sourceRelation.lower = true ∧ valueEndpoint d.sourceRelation.upper = true

set_option synthInstance.maxSize 2048 in
instance (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat) (d : Records S T) :
    Decidable (Primitive s inventory n q i index d) := by
  unfold Primitive
  infer_instance

/-- Derive the exact R47 source-root projection from raw Origin/drain checks
and the occurrence-qualified R65 fact reader, including completed task identity. -/
theorem primitive_derive_root_matches
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat) (d : Records S T)
    (h : Primitive s inventory n q i index d) :
    CurrentEmissionOwnershipR47.RootMatches (OccurrenceQualifiedFactReadersR65.current n inventory)
      (OccurrenceQualifiedConsumerR66.rootQuery n q i d.origin.relation) := by
  rcases h with ⟨hs, he, hu, hocc, hstore, hem, ha, hunique, hb, hstate, hslot, hback,
    hcurrent, har, her, hpair, hestate, hastate, heowner, haowner, hpol, heffect,
    hread, hid, hcandidates, horigins, hostate, hoocc, hoslot, hdrain, hindexed,
    hdstate, hseed, hselected, hincoming, hreplay, hcause, hdslot, hdone,
    hlower, hupper, hsource, hslower, hsupper, hv1, hv2⟩
  have origin : originRead n d.origin.relation = some d.origin := by
    simp [originRead, unique, SourceInternalContextR55.unique, horigins]
  have drain : rootDrain n d.origin.relation = some d.drain := by
    simp [rootDrain, origin, hdrain]
  refine ⟨hu, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [OccurrenceQualifiedConsumerR66.rootQuery, OccurrenceQualifiedFactReadersR65.current,
      OccurrenceQualifiedFactReadersR65.rootCandidates, hocc, hread, hstore, hu, hid,
      ← originCandidates, hcandidates]
  · simp [OccurrenceQualifiedConsumerR66.rootQuery, OccurrenceQualifiedFactReadersR65.current,
      ProviderNativeContextR57.current, origin, hocc, hoocc, hoslot]
  · simp [OccurrenceQualifiedConsumerR66.rootQuery, OccurrenceQualifiedFactReadersR65.current,
      ProviderNativeContextR57.current, drain, hocc, hcause, hdslot]
  · simp [OccurrenceQualifiedConsumerR66.rootQuery, OccurrenceQualifiedFactReadersR65.current,
      OccurrenceQualifiedFactReadersR65.rootTask, hstore, drain, hcause, hdslot,
      hread, hlower, hupper, hid]
  · simp [OccurrenceQualifiedConsumerR66.rootQuery, OccurrenceQualifiedFactReadersR65.current,
      ProviderNativeContextR57.current, completed, origin, drain, hdstate, hindexed,
      hseed, hselected, hincoming, hreplay, hcause, hoocc, hdslot, hoslot, hdone]
  · simp [OccurrenceQualifiedConsumerR66.rootQuery, OccurrenceQualifiedFactReadersR65.current,
      OccurrenceQualifiedFactReadersR65.sourceFact, hocc, hstore, hread, hid]

/-- All fourteen original BeforeAncestry conjuncts follow on the same source
incidence, native emission and admission. No ancestry premise is used. -/
theorem primitive_derive_before_ancestry
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat) (d : Records S T)
    (h : Primitive s inventory n q i index d) :
    OccurrenceQualifiedConsumerR66.BeforeAncestry inventory n
      (OccurrenceQualifiedConsumerR66.rootQuery n q i d.origin.relation) (physical (physicalValue index d)) := by
  have root := primitive_derive_root_matches s inventory n q i index d h
  rcases h with ⟨hs, he, hu, hocc, hstore, hem, ha, hunique, hb, hstate, hslot, hback,
    hcurrent, har, her, hpair, hestate, hastate, heowner, haowner, hpol, heffect, rest⟩
  refine ⟨?_, ?_, rfl, hunique, ?_, ?_, ?_, hcurrent, har, ?_, root, ?_, ?_, ?_⟩
  · simpa [OccurrenceQualifiedFactReadersR65.current, ProviderNativeContextR57.current,
      physicalValue, physical, List.getElem?_map] using congrArg (Option.map (admission (S := S))) ha
  · simpa [OccurrenceQualifiedFactReadersR65.current, ProviderNativeContextR57.current,
      physicalValue, physical, List.getElem?_map] using congrArg (Option.map (emission (S := S))) hem
  · simp [physicalValue, physical, emission, admission, hb, hstate]
  · simp [physicalValue, physical, emission, hslot]
  · simp [physicalValue, physical, emission, admission, hback, hstate]
  · simpa [OccurrenceQualifiedFactReadersR65.current, ProviderNativeContextR57.current,
      physicalValue, physical, her] using hpair
  · simp [physicalValue, physical, emission, slot, row, heowner, hestate,
      OccurrenceQualifiedConsumerR66.rootQuery, he]
  · simp [physicalValue, physical, admission, bound, row, haowner, hastate,
      OccurrenceQualifiedConsumerR66.rootQuery, he]
  · simp [physicalValue, physical, admission, bound, polarity, hpol]

def assemble (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat) (d : Records S T)
    (h : Primitive s inventory n q i index d) : OccurrenceQualifiedConsumerR66.Root s inventory n q :=
  ⟨i, h.1, h.2.1, physicalValue index d, d.origin.relation,
    primitive_derive_before_ancestry s inventory n q i index d h⟩

/-- Source and emission relation IDs are derived distinct through the original
functional relation reader and endpoint constructor disjointness, not assumed. -/
theorem primitive_distinct_relation_roles
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (i : OccurrenceQualifiedConsumerR66.Incidence s inventory q) (index : Nat) (d : Records S T)
    (h : Primitive s inventory n q i index d) : d.origin.relation ≠ d.relation := by
  rcases h with ⟨hs, he, hu, hocc, hstore, hem, ha, hunique, hb, hstate, hslot, hback,
    hcurrent, har, her, hpair, hestate, hastate, heowner, haowner, hpol, heffect,
    hread, hid, hcandidates, horigins, hostate, hoocc, hoslot, hdrain, hindexed,
    hdstate, hseed, hselected, hincoming, hreplay, hcause, hdslot, hdone,
    hlower, hupper, hsource, hslower, hsupper, hv1, hv2⟩
  apply DistinctSourceEmissionRootR75.typed_relation_ids_distinct
    (OccurrenceQualifiedFactReadersR65.current n inventory).relationPair
    d.origin.relation d.relation
    (endpoint n.state d.sourceRelation.lower, endpoint n.state d.sourceRelation.upper)
    (CurrentEmissionOwnershipR47.boundPair (bound d.admission.state d.admission.bound))
  · simp [OccurrenceQualifiedFactReadersR65.current, ProviderNativeContextR57.current, hsource]
  · simpa [OccurrenceQualifiedFactReadersR65.current, ProviderNativeContextR57.current, her] using hpair
  · exact ⟨value_endpoint_typed n.state d.sourceRelation.lower hv1,
      value_endpoint_typed n.state d.sourceRelation.upper hv2⟩
  · change DistinctSourceEmissionRootR75.EffectPair
      (CurrentEmissionOwnershipR47.boundPair (bound d.admission.state d.admission.bound))
    unfold CurrentEmissionOwnershipR47.boundPair bound polarity
    rw [hpol]
    change DistinctSourceEmissionRootR75.IsEffect (endpoint d.admission.state d.admission.bound.item) ∧ _
    refine ⟨effect_endpoint_typed _ _ heffect, ?_⟩
    simp [CurrentEmissionOwnershipR47.rowEndpoint, row, haowner,
      DistinctSourceEmissionRootR75.IsEffect]

structure Constructed (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (u : SourceInternalContextR55.Use Nat (Key S T)) (receiving target annotation row : Key S T) where
  sourceOutput : ConstructedSourceIncidenceR81.Constructed s inventory source calls u receiving target annotation row
  root : OccurrenceQualifiedConsumerR66.Root s inventory n
    (ConstructedSourceIncidenceR81.request u receiving target sourceOutput.aligned.choice annotation row)
  sameIncidence : root.incidence = sourceOutput.incidence
  distinctRoles : root.root ≠ root.value.relation

/-- Original external inputs are finite source/native tables and coordinates.
The R81 constructor runs first; its same incidence is retained in the R66 Root. -/
def construct (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (u : SourceInternalContextR55.Use Nat (Key S T)) (receiving target annotation row : Key S T)
    (index : Nat) : Option (Constructed s inventory n source calls u receiving target annotation row) := do
  let sourceOutput ← ConstructedSourceIncidenceR81.construct s inventory source calls u receiving target annotation row
  let q := ConstructedSourceIncidenceR81.request u receiving target sourceOutput.aligned.choice annotation row
  let d ← readRecords n inventory q index
  if h : Primitive s inventory n q sourceOutput.incidence index d then
    pure ⟨sourceOutput, assemble s inventory n q sourceOutput.incidence index d h, rfl,
      primitive_distinct_relation_roles s inventory n q sourceOutput.incidence index d h⟩
  else none

theorem constructed_applies_parent
    (s : OccurrenceQualifiedConsumerR66.Source S T)
    (inventory : OccurrenceQualifiedFactReadersR65.Inventory S T) (n : Native S T)
    (source : OwnerSource (Key S T)) (calls : List (SourceCall (Key S T)))
    (u : SourceInternalContextR55.Use Nat (Key S T)) (receiving target annotation row : Key S T)
    (out : Constructed s inventory n source calls u receiving target annotation row) :
    out.root.incidence = out.sourceOutput.incidence ∧
    InternalPermissionIncidenceR45.extract
      (OccurrenceQualifiedFactReadersR65.internalInputs s inventory u.occurrence)
      (ConstructedSourceIncidenceR81.request u receiving target out.sourceOutput.aligned.choice annotation row)
      out.root.incidence.probe = some (InternalPermissionIncidenceR45.certificate
        (ConstructedSourceIncidenceR81.request u receiving target out.sourceOutput.aligned.choice annotation row)
        out.root.incidence.probe) ∧ out.root.root ≠ out.root.value.relation :=
  ⟨out.sameIncidence,
    OccurrenceQualifiedConsumerR66.source_incidence_checked s inventory _ out.root.incidence,
    out.distinctRoles⟩

abbrev fixtureSource := ConstructedSourceIncidenceR81.fixture
abbrev fixtureInventory := ConstructedSourceIncidenceR81.fixtureInventory
abbrev fixtureOwner := ConstructedSourceIncidenceR81.fixtureSource
abbrev fixtureCalls := ConstructedSourceIncidenceR81.fixtureCalls
abbrev fixtureUse := SourceInternalChoiceR77.fixtureUse
abbrev fixtureNative := ProviderNativeContextR57.fixtureNative
abbrev fixtureIncidence := ConstructedSourceIncidenceR81.fixtureOutput.incidence
abbrev fixtureQuery := ConstructedSourceIncidenceR81.request fixtureUse (.source 10) (.source 1)
  ConstructedSourceIncidenceR81.fixtureOutput.aligned.choice (.source 6) (.source 5)

def fixtureRecords : Records Nat Nat :=
  ⟨100, fixtureEmission 4 0, fixtureAdmission 4 0, 0,
    ⟨OccurrenceQualifiedFactReadersR65.fixtureFirst, OccurrenceQualifiedFactReadersR65.fixtureRoute⟩,
    ⟨1, 2, 100, 0, some ⟨1, 0, 2, 2, 100, 0,
      .value (.positiveFunction 300), .value (.negativeFunction 400), none, false, true⟩⟩,
    ⟨1, 0, 2, 2, 100, 0,
      .value (.positiveFunction 300), .value (.negativeFunction 400), none, false, true⟩,
    ⟨1, 2, .value (.positiveFunction 300), .value (.negativeFunction 400)⟩,
    ⟨1, 0, .effect (.annotationMember 0 0), .effect (.row 4)⟩⟩

theorem finite_reads : readRecords fixtureNative fixtureInventory fixtureQuery 0 = some fixtureRecords := by rfl

theorem finite_primitive : Primitive fixtureSource fixtureInventory fixtureNative fixtureQuery fixtureIncidence 0 fixtureRecords := by decide

def fixtureRoot := assemble fixtureSource fixtureInventory fixtureNative fixtureQuery fixtureIncidence 0 fixtureRecords finite_primitive

def fixtureOutput : Constructed fixtureSource fixtureInventory fixtureNative fixtureOwner fixtureCalls
    fixtureUse (.source 10) (.source 1) (.source 6) (.source 5) :=
  ⟨ConstructedSourceIncidenceR81.fixtureOutput, fixtureRoot, rfl,
    primitive_distinct_relation_roles fixtureSource fixtureInventory fixtureNative fixtureQuery fixtureIncidence 0 fixtureRecords finite_primitive⟩

def fixtureResult := construct fixtureSource fixtureInventory fixtureNative fixtureOwner fixtureCalls
  fixtureUse (.source 10) (.source 1) (.source 6) (.source 5) 0

theorem finite_constructs_root : fixtureResult = some fixtureOutput := by
  unfold fixtureResult construct
  rw [ConstructedSourceIncidenceR81.finite_constructs_output]
  change (do
    let d ← readRecords fixtureNative fixtureInventory fixtureQuery 0
    if h : Primitive fixtureSource fixtureInventory fixtureNative fixtureQuery fixtureIncidence 0 d then
      pure ⟨ConstructedSourceIncidenceR81.fixtureOutput,
        assemble fixtureSource fixtureInventory fixtureNative fixtureQuery fixtureIncidence 0 d h, rfl,
        primitive_distinct_relation_roles fixtureSource fixtureInventory fixtureNative fixtureQuery fixtureIncidence 0 d h⟩
    else none) = some fixtureOutput
  rw [finite_reads]
  exact dif_pos finite_primitive

theorem finite_nonempty_mixed_witness :
    fixtureResult.isSome = true ∧ fixtureRoot.root = 2 ∧ fixtureRoot.value.relation = 0 ∧
    fixtureRoot.incidence.probe.permission.concrete = [.source 7, .source 7, .source 11] ∧
    fixtureRoot.incidence.probe.registeredRoot = 300 ∧
    fixtureRoot.incidence.probe.registeredRoot ≠ 700 := by
  rw [finite_constructs_root]
  exact ⟨rfl, rfl, rfl, rfl, rfl, by decide⟩

/-- Check adversaries through the same executable constructor, retaining the
source fixture and changing only the named native owner record. -/
def runNative (n : Native Nat Nat) := (construct fixtureSource fixtureInventory n fixtureOwner fixtureCalls
  fixtureUse (.source 10) (.source 1) (.source 6) (.source 5) 0).isSome

def mapDrain (f : Drain Nat Nat → Drain Nat Nat) (n : Native Nat Nat) : Native Nat Nat :=
  {n with origins := n.origins.map (fun o => {o with drain := o.drain.map f})}

theorem duplicate_stale_and_substituted_rejected :
    runNative {fixtureNative with emissions := fixtureNative.emissions ++ [fixtureEmission 4 0]} = false ∧
    runNative {fixtureNative with effectRows := []} = false ∧
    runNative {fixtureNative with admissions := [fixtureAdmission 6 0, fixtureAdmission 6 1]} = false ∧
    runNative {fixtureNative with emissions := [{fixtureEmission 4 0 with readbackSlot := fixtureSlot 6}]} = false := by decide

theorem incomplete_foreign_and_wrong_task_rejected :
    runNative (mapDrain (fun d => {d with completed := false}) fixtureNative) = false ∧
    runNative (mapDrain (fun d => {d with state := 999}) fixtureNative) = false ∧
    runNative (mapDrain (fun d => {d with cause := 101}) fixtureNative) = false ∧
    runNative (mapDrain (fun d => {d with taskUpper := .value (.negativeFunction 999)}) fixtureNative) = false ∧
    runNative (mapDrain (fun d => {d with selectedRelation := 0}) fixtureNative) = false ∧
    runNative (mapDrain (fun d => {d with incoming := some 2}) fixtureNative) = false ∧
    runNative (mapDrain (fun d => {d with replay := true}) fixtureNative) = false := by decide

theorem collapsed_roles_and_parameter_substitution_rejected :
    runNative {fixtureNative with admissions := [fixtureAdmission 4 2, fixtureAdmission 6 1]} = false ∧
    runNative {fixtureNative with relations := fixtureNative.relations.map
      (fun r => if r.index = 2 then {r with lower := .value (.positiveFunction 700)} else r)} = false ∧
    runNative {fixtureNative with origins := fixtureNative.origins.map (fun o => {o with occurrence := 101})} = false := by decide

end YulangClosure.ConstructedPhysicalRootR83
