import YulangClosure.SuccessfulReificationDecodeR71

/-!
R73 finite owner-selected decoding. R72 is not a proof receipt.
This module decodes finite primitive records. Full source identities remain in distinct
Term, ComponentId and occurrence tables; a token is never a full identity.
Only successful executable checks publish a constructed R71 Package.
Native allocation/runtime correspondence and the genuine R66 Root remain open.
-/
namespace YulangClosure.OwnerExactCompletedInstanceR73
open ProviderNativeContextR57 OccurrenceQualifiedFactReadersR65
open SemanticFactEndpointInterpretationR68
open EncodedOwnerObservationsR70
open SuccessfulReificationDecodeR71

variable {S T C A : Type} [DecidableEq S] [DecidableEq T]
  [DecidableEq C] [DecidableEq A]

def decodeField (terms : List T) (f : Field Nat) : Option (Field T) := do
  let t ← terms[f.value]?
  pure ⟨f.name,f.optional,t⟩

def decodeAlternative (terms : List T) (a : Alternative Nat) : Option (Alternative T) := do
  let ts ← a.payloads.mapM (fun i => terms[i]?)
  pure ⟨a.tag,ts⟩

/-- Every original structural case, including optional fields and ordered
variant payloads, is decoded rather than replaced by an outer tag. -/
def decodeView (terms : List T) (components : List C) : SourceView Nat Nat → Option (SourceView T C)
  | .leaf l => some (.leaf l)
  | .component i => (components[i]?).map SourceView.component
  | .liveVariable k p i => some (.liveVariable k p i)
  | .positiveBottom => some .positiveBottom
  | .negativeTop => some .negativeTop
  | .negativeBottom => some .negativeBottom
  | .positiveFunction a ae re r => do
      let a ← terms[a]?; let ae ← terms[ae]?; let re ← terms[re]?; let r ← terms[r]?
      pure (.positiveFunction a ae re r)
  | .negativeFunction a ae re r => do
      let a ← terms[a]?; let ae ← terms[ae]?; let re ← terms[re]?; let r ← terms[r]?
      pure (.negativeFunction a ae re r)
  | .positiveVariant xs => (xs.mapM (decodeAlternative terms)).map SourceView.positiveVariant
  | .negativeVariant xs => (xs.mapM (decodeAlternative terms)).map SourceView.negativeVariant
  | .positiveRecord xs => (xs.mapM (decodeField terms)).map SourceView.positiveRecord
  | .negativeRecord xs => (xs.mapM (decodeField terms)).map SourceView.negativeRecord
  | .positiveTuple xs => (xs.mapM (fun i => terms[i]?)).map SourceView.positiveTuple
  | .negativeTuple xs => (xs.mapM (fun i => terms[i]?)).map SourceView.negativeTuple

def decodeObservation (terms : List T) (components : List C)
    (row : Nat × SourceView Nat Nat × List (Nat × Nat)) : Option (Observation T C) := do
  let term ← terms[row.1]?
  let view ← decodeView terms components row.2.1
  let children ← row.2.2.mapM fun child => do
    let t ← terms[child.2]?
    pure (child.1,t)
  pure ⟨term,view,children⟩

def decodeComponent (terms : List T) (components : List C)
    (row : Nat × Nat × Coordinate) : Option (ComponentRow T C) := do
  let term ← terms[row.1]?
  let component ← components[row.2.1]?
  pure ⟨term,component,row.2.2⟩

def decodePosition (terms : List T) (row : Nat × Nat) : Option (T × Nat) := do
  let term ← terms[row.1]?
  pure (term,row.2)

theorem term_coordinate (terms : List T) (i : Nat) (t : T)
    (found : terms[i]? = some t) : t ∈ terms := List.mem_of_getElem? found

theorem namespace_identity (terms : List T) (components : List C) (a b : T) (c d : C)
    (termMember : a ∈ terms) (componentMember : c ∈ components) :
    (token terms a = token terms b ↔ a = b) ∧
    (token components c = token components d ↔ c = d) :=
  ⟨token_reflect terms a b termMember,token_reflect components c d componentMember⟩

/-- Opaque receiving-experiment identity, separate from view and artifact. -/
structure ExperimentId where
  identity : Nat
  deriving DecidableEq

structure CompletedViewId where
  identity : Nat
  deriving DecidableEq

/-- Full HIR artifact identity and local ordinal remain paired. -/
structure Occurrence (A : Type) where
  artifact : A
  ordinal : Nat
  deriving DecidableEq

/-- Internal finite rows, constructed by owner selection below. This low-level
carrier alone does not establish source ownership. -/
structure Projection (T C A : Type) where
  owner : ExperimentId
  admittedArtifacts : List A
  store : Nat
  terms : List T
  views : List (SourceView Nat Nat)
  components : List C
  componentPositions : List (Nat × Nat)
  componentRows : List (Nat × Nat × Coordinate)
  liveComponents : List (Nat × Coordinate)
  currentValues : List Nat
  currentEffects : List Nat
  facts : List (Nat × Fact × T × T)
  provenance : List (Edge (Occurrence A))
  interpretedFacts : List (Nat × FactRow T)
  occurrences : List (Nat × Occurrence A)
  edges : List (Edge Nat)

def primitiveObservations (v : Projection T C A) :
    List (Nat × SourceView Nat Nat × List (Nat × Nat)) :=
  v.views.zipIdx.map fun row =>
    (row.2,row.1,(sourceChildren row.1).map (fun i => (i,i)))

def buildTables (v : Projection T C A) : Option (SourceTables T C) := do
  let observations ← (primitiveObservations v).mapM (decodeObservation v.terms v.components)
  let positions ← v.componentPositions.mapM (decodePosition v.terms)
  let components ← v.componentRows.mapM (decodeComponent v.terms v.components)
  pure ⟨v.store,observations,positions,components,v.currentValues,v.currentEffects⟩

def buildPackage (v : Projection T C A) : Option (Package (Occurrence A) T C ExperimentId) := do
  let tables ← buildTables v
  pure ⟨v.owner,tables,v.facts.map (fun f => (f.1,⟨f.2.1,f.2.2.1,f.2.2.2⟩)),
    v.provenance,v.occurrences.map (fun entry => (entry.2,v.owner))⟩

/-- Every input is finite primitive data. Each conjunct is actually decided
below before a successful result can be constructed. -/
def InputChecks (v : Projection T C A) (p : Package (Occurrence A) T C ExperimentId) : Prop :=
  v.componentPositions = v.componentRows.zipIdx.map (fun row => (row.1.1,row.2)) ∧
  terms p.tables = v.terms ∧ components p.tables = v.components ∧
  v.terms.length = v.views.length ∧
  v.liveComponents = v.componentRows.zipIdx.map (fun row => (row.2,row.1.2.2)) ∧
  v.interpretedFacts.map Prod.fst = List.range v.facts.length ∧
  v.occurrences.map Prod.fst = List.range v.occurrences.length ∧
  (∀ entry ∈ v.occurrences, entry.2.artifact ∈ v.admittedArtifacts)

instance (v : Projection T C A) (p : Package (Occurrence A) T C ExperimentId) :
    Decidable (InputChecks v p) := by unfold InputChecks; infer_instance

def OutputChecks (v : Projection T C A) (r : Returned (Occurrence A) T C ExperimentId) : Prop :=
  r.sourceRows = v.interpretedFacts.map Prod.snd ∧
  r.occurrenceTable = v.occurrences.map Prod.snd ∧ r.edges = v.edges

instance (v : Projection T C A) (r : Returned (Occurrence A) T C ExperimentId) :
    Decidable (OutputChecks v r) := by unfold OutputChecks; infer_instance

/-- Evidence is an OUTPUT of finite decoding and the actual R71 reifier. -/
structure Decoded (resource : Resources) (kind : C → Kind) (v : Projection T C A) where
  package : Package (Occurrence A) T C ExperimentId
  result : Returned (Occurrence A) T C ExperimentId
  constructed : buildPackage v = some package
  checked : InputChecks v package
  replay : reify resource kind package = .ok result
  exactRows : OutputChecks v result

def decode (resource : Resources) (kind : C → Kind) (v : Projection T C A) :
    Except Gap (Decoded resource kind v) :=
  match built : buildPackage v with
  | none => .error .boundMismatch
  | some p =>
    if checked : InputChecks v p then
      match replay : reify resource kind p with
      | .error gap => .error gap
      | .ok r => if exactRows : OutputChecks v r then
          .ok ⟨p,r,built,checked,replay,exactRows⟩
        else .error .boundMismatch
    else .error .boundMismatch

theorem accepted_replay (resource : Resources) (kind : C → Kind) (v : Projection T C A)
    (d : Decoded resource kind v) :
    reify resource kind d.package = .ok d.result ∧
    ReturnEquations kind d.package d.result := by
  have evidence := completed_return resource kind d.package
  rw [d.replay] at evidence
  exact ⟨d.replay,evidence⟩

/-- The top-level statement ranges over primitive projections only. -/
theorem finite_decode_replay (resource : Resources) (kind : C → Kind) (v : Projection T C A) :
    match decode resource kind v with
    | .error _ => True
    | .ok d => buildPackage v = some d.package ∧
        reify resource kind d.package = .ok d.result ∧
        ReturnEquations kind d.package d.result ∧ OutputChecks v d.result := by
  cases decode resource kind v with
  | error gap => trivial
  | ok d => exact ⟨d.constructed,d.replay,(accepted_replay resource kind v d).2,d.exactRows⟩

theorem accepted_package_fields (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (d : Decoded resource kind v) :
    d.package.owner = v.owner ∧
    d.package.facts = v.facts.map (fun f => (f.1,⟨f.2.1,f.2.2.1,f.2.2.2⟩)) ∧
    d.package.provenance = v.provenance ∧
    d.package.occurrenceOwners = v.occurrences.map (fun entry => (entry.2,v.owner)) ∧
    buildTables v = some d.package.tables := by
  have h := d.constructed
  unfold buildPackage at h
  cases tables : buildTables v with
  | none => simp [tables] at h
  | some p =>
    rw [tables] at h
    change some (⟨v.owner,p,
      v.facts.map (fun f => (f.1,⟨f.2.1,f.2.2.1,f.2.2.2⟩)),
      v.provenance,v.occurrences.map (fun entry => (entry.2,v.owner))⟩ :
        Package (Occurrence A) T C ExperimentId) = some d.package at h
    have same := Option.some.inj h
    rw [← same]
    exact ⟨rfl,rfl,rfl,rfl,rfl⟩

theorem accepted_order_and_endpoints (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (d : Decoded resource kind v) (i : Nat) :
    d.result.sourceRows[i]? = (v.interpretedFacts[i]?).map Prod.snd ∧
    d.result.occurrenceTable[i]? = (v.occurrences[i]?).map Prod.snd ∧
    d.result.edges[i]? = v.edges[i]? ∧
    v.interpretedFacts.map Prod.fst = List.range v.facts.length ∧
    v.occurrences.map Prod.fst = List.range v.occurrences.length := by
  have fields := d.exactRows
  unfold OutputChecks at fields
  rw [fields.1,fields.2.1,fields.2.2,List.getElem?_map,List.getElem?_map]
  exact ⟨rfl,rfl,rfl,d.checked.2.2.2.2.2.1,d.checked.2.2.2.2.2.2.1⟩

theorem accepted_all_return_fields (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (d : Decoded resource kind v) :
    d.result.owner = d.package.owner ∧ d.result.tables = d.package.tables ∧
    d.result.facts = d.package.facts ∧ d.result.provenance = d.package.provenance ∧
    d.result.observations = encodedTables kind d.package.tables := by
  have h := (accepted_replay resource kind v d).2.exactReturn
  exact ⟨congrArg Returned.owner h,congrArg Returned.tables h,
    congrArg Returned.facts h,congrArg Returned.provenance h,congrArg Returned.observations h⟩

theorem accepted_table_fields (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (d : Decoded resource kind v) :
    ∃ observations positions componentRows,
      (primitiveObservations v).mapM (decodeObservation v.terms v.components) = some observations ∧
      v.componentPositions.mapM (decodePosition v.terms) = some positions ∧
      v.componentRows.mapM (decodeComponent v.terms v.components) = some componentRows ∧
      d.package.tables = ⟨v.store,observations,positions,componentRows,v.currentValues,v.currentEffects⟩ := by
  have h := (accepted_package_fields resource kind v d).2.2.2.2
  unfold buildTables at h
  cases obs : (primitiveObservations v).mapM (decodeObservation v.terms v.components) with
  | none => simp [obs,bind,Option.bind] at h
  | some observations =>
    cases pos : v.componentPositions.mapM (decodePosition v.terms) with
    | none => simp [obs,pos,bind,Option.bind] at h
    | some positions =>
      cases comps : v.componentRows.mapM (decodeComponent v.terms v.components) with
      | none => simp [obs,pos,comps,bind,Option.bind] at h
      | some componentRows =>
        simp only [obs,pos,comps,bind,Option.bind] at h
        exact ⟨observations,positions,componentRows,rfl,rfl,rfl,(Option.some.inj h).symm⟩

theorem accepted_component_positions (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (d : Decoded resource kind v) :
    v.componentPositions = v.componentRows.zipIdx.map (fun row => (row.1.1,row.2)) :=
  d.checked.1

theorem positions_mismatch_rejected (resource : Resources) (kind : C → Kind)
    (v : Projection T C A)
    (mismatch : v.componentPositions ≠ v.componentRows.zipIdx.map (fun row => (row.1.1,row.2))) :
    decode resource kind v = .error .boundMismatch := by
  unfold decode
  split
  · rfl
  · split
    · rename_i checked
      exact False.elim (mismatch checked.1)
    · rfl

theorem foreign_occurrence_rejected (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (entry : Nat × Occurrence A)
    (member : entry ∈ v.occurrences) (foreign : entry.2.artifact ∉ v.admittedArtifacts) :
    decode resource kind v = .error .boundMismatch := by
  unfold decode
  split
  · rfl
  · split
    · rename_i checked
      exact False.elim (foreign (checked.2.2.2.2.2.2.2 entry member))
    · rfl

/-- Application to the SAME R66 Root and the SAME slot-0 and slot-2
witnesses. No source construction, native execution or Root is fabricated. -/
theorem accepted_r66_same_witnesses (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (d : Decoded resource kind v)
    (source : OccurrenceQualifiedConsumerR66.Source (Occurrence A) Nat)
    (native : Native (Occurrence A) Nat)
    (q : OccurrenceQualifiedConsumerR66.Request (Occurrence A) Nat)
    (root : OccurrenceQualifiedConsumerR66.Root source
      (inventory (encodedOwner kind d.package) d.result.rows d.result.provenance) native q)
    (use lambda : Occurrence A)
    (useCoordinate : q.use.occurrence = .source use)
    (lambdaCoordinate : q.lambda = .source lambda) :
    ∃ route construction,
      readAt (BorrowedQualifiedReadReificationR67.encoded
          (inventory (encodedOwner kind d.package) d.result.rows d.result.provenance))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex
          (inventory (encodedOwner kind d.package) d.result.rows d.result.provenance) use) 0 =
            some (BorrowedQualifiedReadReificationR67.encodeRead
              (inventory (encodedOwner kind d.package) d.result.rows d.result.provenance) route) ∧
      route.fact.identity = root.incidence.probe.fact ∧
      route.fact.lower = root.incidence.probe.registeredRoot ∧
      route.fact.upper = root.incidence.probe.plan.useValue ∧
      readAt (BorrowedQualifiedReadReificationR67.encoded
          (inventory (encodedOwner kind d.package) d.result.rows d.result.provenance))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex
          (inventory (encodedOwner kind d.package) d.result.rows d.result.provenance) lambda) 2 =
            some (BorrowedQualifiedReadReificationR67.encodeRead
              (inventory (encodedOwner kind d.package) d.result.rows d.result.provenance) construction) ∧
      construction.fact.lower = root.incidence.probe.construction.function ∧
      construction.fact.upper = root.incidence.probe.registeredRoot ∧
      Interpreted (encodedOwner kind d.package) route.fact ∧
      Interpreted (encodedOwner kind d.package) construction.fact := by
  have parent := completed_r66_same_witnesses resource kind d.package
  rw [d.replay] at parent
  exact parent source native q root use lambda useCoordinate lambdaCoordinate

theorem accepted_competitors (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (d : Decoded resource kind v)
    (s : Occurrence A) (slot : Nat) (id : Fact) :
    candidates (BorrowedQualifiedReadReificationR67.encoded (inventoryOf d.result))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex (inventoryOf d.result) s) slot =
      (candidates (inventoryOf d.result) s slot).map
        (BorrowedQualifiedReadReificationR67.encodeEdge (inventoryOf d.result)) ∧
    resolve (BorrowedQualifiedReadReificationR67.encoded (inventoryOf d.result)) id =
      resolve (inventoryOf d.result) id ∧
    readAt (BorrowedQualifiedReadReificationR67.encoded (inventoryOf d.result))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex (inventoryOf d.result) s) slot =
      (readAt (inventoryOf d.result) s slot).map
        (BorrowedQualifiedReadReificationR67.encodeRead (inventoryOf d.result)) :=
  complete_competitors_and_lookup d.result s slot id



/-- The selected native session/store. HIR ownership is membership in its
admitted artifact inventory, exactly the extensional semantics of require_owned:
owns_occurrence compares the full branded artifact identity, not its ordinal. -/
structure ExperimentRows (T A : Type) where
  store : Nat
  admittedArtifacts : List A
  facts : List (Nat × Fact × T × T)
  provenance : List (Edge (Occurrence A))
  currentValues : List Nat
  currentEffects : List Nat

/-- Borrowed completed contents, without an independent owner mirror. -/
structure BorrowedRows (T C A : Type) where
  store : Nat
  terms : List T
  views : List (SourceView Nat Nat)
  components : List C
  componentPositions : List (Nat × Nat)
  componentRows : List (Nat × Nat × Coordinate)
  liveComponents : List (Nat × Coordinate)
  currentValues : List Nat
  currentEffects : List Nat
  facts : List (Nat × Fact × T × T)
  provenance : List (Edge (Occurrence A))
  interpretedFacts : List (Nat × FactRow T)
  occurrences : List (Nat × Occurrence A)
  edges : List (Edge Nat)
  artifactPositions : List Nat

structure CompletedSourceView (T C A : Type) where
  experiment : ExperimentId
  rows : BorrowedRows T C A

/-- Registries interpret opaque identities. Native pointer-to-registry
correspondence is OPEN; these identities are not integer casts of pointers. -/
structure World (T C A : Type) where
  experiments : List (ExperimentId × ExperimentRows T A)
  completedViews : List (CompletedViewId × CompletedSourceView T C A)

def requireOwned (o : ExperimentRows T A) (s : Occurrence A) : Prop :=
  s.artifact ∈ o.admittedArtifacts

def materialize (id : ExperimentId) (o : ExperimentRows T A)
    (v : BorrowedRows T C A) : Projection T C A :=
  { owner := id
    admittedArtifacts := o.admittedArtifacts
    store := v.store
    terms := v.terms
    views := v.views
    components := v.components
    componentPositions := v.componentPositions
    componentRows := v.componentRows
    liveComponents := v.liveComponents
    currentValues := v.currentValues
    currentEffects := v.currentEffects
    facts := v.facts
    provenance := v.provenance
    interpretedFacts := v.interpretedFacts
    occurrences := v.occurrences
    edges := v.edges
  }

/-- All readbacks are reached through the selected view's experiment. The
complete lists preserve order, endpoints and distinct provenance occurrences. -/
def Readbacks (o : ExperimentRows T A) (v : BorrowedRows T C A) : Prop :=
  v.store = o.store ∧ v.facts = o.facts ∧ v.provenance = o.provenance ∧
  v.currentValues = o.currentValues ∧ v.currentEffects = o.currentEffects ∧
  v.artifactPositions.length = v.occurrences.length ∧
  ∀ row ∈ v.occurrences.zip v.artifactPositions,
    o.admittedArtifacts[row.2]? = some row.1.2.artifact

instance (o : ExperimentRows T A) (v : BorrowedRows T C A) : Decidable (Readbacks o v) := by
  unfold Readbacks
  infer_instance

structure OwnerDecoded (resource : Resources) (kind : C → Kind)
    (w : World T C A) (experiment : ExperimentId) (view : CompletedViewId) where
  completed : CompletedSourceView T C A
  selected : lookup w.completedViews view = some completed
  paired : completed.experiment = experiment
  ownerRows : ExperimentRows T A
  selectedOwner : lookup w.experiments completed.experiment = some ownerRows
  readbacks : Readbacks ownerRows completed.rows
  decoded : Decoded resource kind (materialize experiment ownerRows completed.rows)

/-- View and experiment selection precede every table read and the R71 replay.
No Package, faithful interpretation, assumed law or successful flag is input. -/
def decodeOwner (resource : Resources) (kind : C → Kind) (w : World T C A)
    (experiment : ExperimentId) (view : CompletedViewId) :
    Except Gap (OwnerDecoded resource kind w experiment view) :=
  match selected : lookup w.completedViews view with
  | none => .error .boundMismatch
  | some completed =>
    if paired : completed.experiment = experiment then
      match owner : lookup w.experiments completed.experiment with
      | none => .error .boundMismatch
      | some o =>
        if checks : Readbacks o completed.rows then
          match result : decode resource kind (materialize experiment o completed.rows) with
          | .error gap => .error gap
          | .ok d => .ok ⟨completed,selected,paired,o,owner,checks,d⟩
        else .error .boundMismatch
    else .error .boundMismatch

theorem owner_selected_readbacks (resource : Resources) (kind : C → Kind)
    (w : World T C A) (experiment : ExperimentId) (view : CompletedViewId)
    (d : OwnerDecoded resource kind w experiment view) :
    lookup w.completedViews view = some d.completed ∧
    d.completed.experiment = experiment ∧
    lookup w.experiments d.completed.experiment = some d.ownerRows ∧
    d.completed.rows.facts = d.ownerRows.facts ∧
    d.completed.rows.provenance = d.ownerRows.provenance ∧
    d.completed.rows.currentValues = d.ownerRows.currentValues ∧
    d.completed.rows.currentEffects = d.ownerRows.currentEffects :=
  ⟨d.selected,d.paired,d.selectedOwner,d.readbacks.2.1,d.readbacks.2.2.1,
    d.readbacks.2.2.2.1,d.readbacks.2.2.2.2.1⟩

theorem owner_replay (resource : Resources) (kind : C → Kind)
    (w : World T C A) (experiment : ExperimentId) (view : CompletedViewId)
    (d : OwnerDecoded resource kind w experiment view) :
    reify resource kind d.decoded.package = .ok d.decoded.result ∧
    ReturnEquations kind d.decoded.package d.decoded.result ∧
    d.completed.rows.componentPositions =
      d.completed.rows.componentRows.zipIdx.map (fun row => (row.1.1,row.2)) :=
  ⟨d.decoded.replay,(accepted_replay resource kind _ d.decoded).2,d.decoded.checked.1⟩

theorem foreign_view_rejected (resource : Resources) (kind : C → Kind)
    (w : World T C A) (experiment : ExperimentId) (view : CompletedViewId)
    (completed : CompletedSourceView T C A)
    (selected : lookup w.completedViews view = some completed)
    (foreign : completed.experiment ≠ experiment) :
    decodeOwner resource kind w experiment view = .error .boundMismatch := by
  unfold decodeOwner
  split
  · rfl
  · rename_i retained found
    have same : retained = completed := Option.some.inj (found.symm.trans selected)
    subst retained
    split
    · rename_i paired
      exact False.elim (foreign paired)
    · rfl

theorem substituted_readback_rejected (resource : Resources) (kind : C → Kind)
    (w : World T C A) (experiment : ExperimentId) (view : CompletedViewId)
    (completed : CompletedSourceView T C A) (o : ExperimentRows T A)
    (selected : lookup w.completedViews view = some completed)
    (paired : completed.experiment = experiment)
    (owner : lookup w.experiments completed.experiment = some o)
    (mismatch : ¬ Readbacks o completed.rows) :
    decodeOwner resource kind w experiment view = .error .boundMismatch := by
  unfold decodeOwner
  split
  · rfl
  · rename_i retained found
    have same : retained = completed := Option.some.inj (found.symm.trans selected)
    subst retained
    split
    · split
      · rfl
      · rename_i selectedRows foundOwner
        have sameOwner : selectedRows = o := Option.some.inj (foundOwner.symm.trans owner)
        subst selectedRows
        split
        · rename_i checked
          exact False.elim (mismatch checked)
        · rfl
    · rename_i notPaired
      exact False.elim (notPaired paired)

theorem admitted_occurrences (resource : Resources) (kind : C → Kind)
    (w : World T C A) (experiment : ExperimentId) (view : CompletedViewId)
    (d : OwnerDecoded resource kind w experiment view) :
    ∀ entry ∈ d.completed.rows.occurrences, requireOwned d.ownerRows entry.2 :=
  d.decoded.checked.2.2.2.2.2.2.2

/-- Two receiving experiments may admit exactly the same HIR. Artifact
membership supplies no equality or permission to pair their completed views. -/
theorem shared_artifact_does_not_identify_experiment (a : A) :
    (⟨0⟩ : ExperimentId) ≠ ⟨1⟩ ∧
    requireOwned (⟨0,[a],[],[],[],[]⟩ : ExperimentRows Nat A) ⟨a,0⟩ ∧
    requireOwned (⟨1,[a],[],[],[],[]⟩ : ExperimentRows Nat A) ⟨a,0⟩ := by
  exact ⟨by decide,by simp [requireOwned],by simp [requireOwned]⟩

theorem duplicated_positions_rejected (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (coordinate : Coordinate)
    (rows : v.componentRows = [(0,0,coordinate),(1,0,coordinate)])
    (positions : v.componentPositions = [(0,0),(0,0)]) :
    decode resource kind v = .error .boundMismatch := by
  apply positions_mismatch_rejected
  rw [rows,positions]
  change [(0,0),(0,0)] ≠ ([(0,0),(1,1)] : List (Nat × Nat))
  decide

theorem reversed_positions_rejected (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (coordinate : Coordinate)
    (rows : v.componentRows = [(0,0,coordinate),(1,0,coordinate)])
    (positions : v.componentPositions = [(1,1),(0,0)]) :
    decode resource kind v = .error .boundMismatch := by
  apply positions_mismatch_rejected
  rw [rows,positions]
  change [(1,1),(0,0)] ≠ ([(0,0),(1,1)] : List (Nat × Nat))
  decide

/-- A shared FactId never collapses provenance: these complete ordered rows
retain both occurrence identities before any reader selects a competitor. -/
theorem same_fact_distinct_occurrences (a : A) (fact : Fact) :
    let s : Occurrence A := ⟨a,0⟩
    let t : Occurrence A := ⟨a,1⟩
    s ≠ t ∧ ([(⟨0,fact,s,0⟩ : Edge (Occurrence A)),⟨1,fact,t,0⟩]).length = 2 := by
  dsimp
  constructor
  · intro eq
    have ord := congrArg Occurrence.ordinal eq
    cases ord
  · rfl



theorem finite_owner_decode_replay (resource : Resources) (kind : C → Kind)
    (w : World T C A) (experiment : ExperimentId) (view : CompletedViewId) :
    match decodeOwner resource kind w experiment view with
    | .error _ => True
    | .ok d =>
      lookup w.completedViews view = some d.completed ∧
      d.completed.experiment = experiment ∧
      lookup w.experiments d.completed.experiment = some d.ownerRows ∧
      Readbacks d.ownerRows d.completed.rows ∧
      reify resource kind d.decoded.package = .ok d.decoded.result ∧
      ReturnEquations kind d.decoded.package d.decoded.result := by
  cases decodeOwner resource kind w experiment view with
  | error gap => trivial
  | ok d => exact ⟨d.selected,d.paired,d.selectedOwner,d.readbacks,
      d.decoded.replay,(accepted_replay resource kind _ d.decoded).2⟩

theorem owner_r66_same_witnesses (resource : Resources) (kind : C → Kind)
    (w : World T C A) (experiment : ExperimentId) (view : CompletedViewId)
    (d : OwnerDecoded resource kind w experiment view)
    (source : OccurrenceQualifiedConsumerR66.Source (Occurrence A) Nat)
    (native : Native (Occurrence A) Nat)
    (q : OccurrenceQualifiedConsumerR66.Request (Occurrence A) Nat)
    (root : OccurrenceQualifiedConsumerR66.Root source
      (inventory (encodedOwner kind d.decoded.package) d.decoded.result.rows d.decoded.result.provenance) native q)
    (use lambda : Occurrence A)
    (useCoordinate : q.use.occurrence = .source use)
    (lambdaCoordinate : q.lambda = .source lambda) :
    ∃ route construction,
      readAt (BorrowedQualifiedReadReificationR67.encoded
          (inventory (encodedOwner kind d.decoded.package) d.decoded.result.rows d.decoded.result.provenance))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex
          (inventory (encodedOwner kind d.decoded.package) d.decoded.result.rows d.decoded.result.provenance) use) 0 =
            some (BorrowedQualifiedReadReificationR67.encodeRead
              (inventory (encodedOwner kind d.decoded.package) d.decoded.result.rows d.decoded.result.provenance) route) ∧
      route.fact.identity = root.incidence.probe.fact ∧
      route.fact.lower = root.incidence.probe.registeredRoot ∧
      route.fact.upper = root.incidence.probe.plan.useValue ∧
      readAt (BorrowedQualifiedReadReificationR67.encoded
          (inventory (encodedOwner kind d.decoded.package) d.decoded.result.rows d.decoded.result.provenance))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex
          (inventory (encodedOwner kind d.decoded.package) d.decoded.result.rows d.decoded.result.provenance) lambda) 2 =
            some (BorrowedQualifiedReadReificationR67.encodeRead
              (inventory (encodedOwner kind d.decoded.package) d.decoded.result.rows d.decoded.result.provenance) construction) ∧
      construction.fact.lower = root.incidence.probe.construction.function ∧
      construction.fact.upper = root.incidence.probe.registeredRoot ∧
      Interpreted (encodedOwner kind d.decoded.package) route.fact ∧
      Interpreted (encodedOwner kind d.decoded.package) construction.fact := by
  exact accepted_r66_same_witnesses resource kind
    (materialize experiment d.ownerRows d.completed.rows) d.decoded
    source native q root use lambda useCoordinate lambdaCoordinate

theorem duplicate_component_rows_rejected (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (coordinate : Coordinate)
    (rows : v.componentRows = [(0,0,coordinate),(0,0,coordinate)])
    (positions : v.componentPositions = [(0,0),(1,1)]) :
    decode resource kind v = .error .boundMismatch := by
  apply positions_mismatch_rejected
  rw [rows,positions]
  change [(0,0),(1,1)] ≠ ([(0,0),(0,1)] : List (Nat × Nat))
  decide

theorem reversed_component_rows_rejected (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (coordinate : Coordinate)
    (rows : v.componentRows = [(1,0,coordinate),(0,0,coordinate)])
    (positions : v.componentPositions = [(0,0),(1,1)]) :
    decode resource kind v = .error .boundMismatch := by
  apply positions_mismatch_rejected
  rw [rows,positions]
  change [(0,0),(1,1)] ≠ ([(1,0),(0,1)] : List (Nat × Nat))
  decide

def emptyRows : BorrowedRows Nat Nat Nat :=
  ⟨0,[],[],[],[],[],[],[],[],[],[],[],[],[],[]⟩

def sharedArtifactWorld : World Nat Nat Nat :=
  ⟨[(⟨0⟩,⟨0,[7],[],[],[],[]⟩),(⟨1⟩,⟨1,[7],[],[],[],[]⟩)],
    [(⟨0⟩,⟨⟨0⟩,emptyRows⟩)]⟩

/-- Foreign pairing rejects even with no provenance to expose a foreign edge,
and even though both experiments admit the very same HIR artifact. -/
theorem empty_provenance_shared_artifact_foreign_view_rejected
    (resource : Resources) (kind : Nat → Kind) :
    emptyRows.provenance = [] ∧
    decodeOwner resource kind sharedArtifactWorld ⟨1⟩ ⟨0⟩ = .error .boundMismatch := by
  refine ⟨rfl,?_⟩
  exact foreign_view_rejected resource kind sharedArtifactWorld ⟨1⟩ ⟨0⟩
    ⟨⟨0⟩,emptyRows⟩ rfl (by decide)

/-- A substituted complete ordered readback fails independently of whether
its replacement is internally consistent. -/
theorem any_substituted_owner_readback_rejected (resource : Resources) (kind : C → Kind)
    (w : World T C A) (experiment : ExperimentId) (view : CompletedViewId)
    (completed : CompletedSourceView T C A) (o : ExperimentRows T A)
    (selected : lookup w.completedViews view = some completed)
    (paired : completed.experiment = experiment)
    (owner : lookup w.experiments completed.experiment = some o)
    (changed : completed.rows.facts ≠ o.facts ∨
      completed.rows.provenance ≠ o.provenance ∨
      completed.rows.currentValues ≠ o.currentValues ∨
      completed.rows.currentEffects ≠ o.currentEffects) :
    decodeOwner resource kind w experiment view = .error .boundMismatch := by
  apply substituted_readback_rejected resource kind w experiment view completed o selected paired owner
  intro h
  rcases changed with facts | provenance | values | effects
  · exact facts h.2.1
  · exact provenance h.2.2.1
  · exact values h.2.2.2.1
  · exact effects h.2.2.2.2.1


/-- Exact complete returned readbacks, including all same-FactId provenance
rows. Reordering or dropping any source edge breaks this ordered equation. -/
theorem owner_complete_returned_readbacks (resource : Resources) (kind : C → Kind)
    (w : World T C A) (experiment : ExperimentId) (view : CompletedViewId)
    (d : OwnerDecoded resource kind w experiment view) :
    d.decoded.result.owner = experiment ∧
    d.decoded.result.facts = d.ownerRows.facts.map
      (fun f => (f.1,⟨f.2.1,f.2.2.1,f.2.2.2⟩)) ∧
    d.decoded.result.provenance = d.ownerRows.provenance ∧
    d.decoded.result.tables.currentValues = d.ownerRows.currentValues ∧
    d.decoded.result.tables.currentEffects = d.ownerRows.currentEffects := by
  have returned := accepted_all_return_fields resource kind _ d.decoded
  have packaged := accepted_package_fields resource kind _ d.decoded
  rcases accepted_table_fields resource kind _ d.decoded with
    ⟨observations,positions,componentRows,_,_,_,table⟩
  refine ⟨returned.1.trans packaged.1,?_,?_,?_,?_⟩
  · rw [returned.2.2.1,packaged.2.1]
    change d.completed.rows.facts.map
      (fun f => (f.1,(⟨f.2.1,f.2.2.1,f.2.2.2⟩ : PrimitiveFact T))) = _
    rw [d.readbacks.2.1]
  · exact returned.2.2.2.1.trans (packaged.2.2.1.trans d.readbacks.2.2.1)
  · rw [returned.2.1,table]
    exact d.readbacks.2.2.2.1
  · rw [returned.2.1,table]
    exact d.readbacks.2.2.2.2.1

end YulangClosure.OwnerExactCompletedInstanceR73
