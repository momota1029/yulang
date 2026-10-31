import YulangClosure.SuccessfulReificationDecodeR71

/-!
R72 decodes finite primitive records. Full source identities remain in distinct
Term, ComponentId and occurrence tables; a token is never a full identity.
Only successful executable checks publish a constructed R71 Package.
Native allocation/runtime correspondence and the genuine R66 Root remain open.
-/
namespace YulangClosure.CompletedNativeInstanceR72
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

/-- The full HIR identity contains its artifact; equal local ordinals from
different artifacts remain different identities. This is identity data. -/
structure Occurrence (A : Type) where
  artifact : A
  ordinal : Nat
  deriving DecidableEq

/-- Primitive reads of the borrowed view, together with the source-store
readbacks performed by its owner validation. The latter are borrowed reads,
not a supplied Package, success flag, or faithfulness proposition. -/
structure Projection (T C A : Type) where
  owner : A
  store : Nat
  terms : List T
  views : List (SourceView Nat Nat)
  components : List C
  componentPositions : List (Nat × Nat)
  componentRows : List (Nat × Nat × Coordinate)
  liveComponents : List (Nat × Coordinate)
  currentValues : List Nat
  currentEffects : List Nat
  ownerCurrentValues : List Nat
  ownerCurrentEffects : List Nat
  facts : List (Nat × Fact × T × T)
  ownerFacts : List (Nat × Fact × T × T)
  provenance : List (Edge (Occurrence A))
  ownerProvenance : List (Edge (Occurrence A))
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

def buildPackage (v : Projection T C A) : Option (Package (Occurrence A) T C A) := do
  let tables ← buildTables v
  pure ⟨v.owner,tables,v.facts.map (fun f => (f.1,⟨f.2.1,f.2.2.1,f.2.2.2⟩)),
    v.provenance,v.occurrences.map (fun entry => (entry.2,entry.2.artifact))⟩

/-- Every input is finite primitive data. Each conjunct is actually decided
below before a successful result can be constructed. -/
def InputChecks (v : Projection T C A) (p : Package (Occurrence A) T C A) : Prop :=
  v.facts = v.ownerFacts ∧ v.provenance = v.ownerProvenance ∧
  v.currentValues = v.ownerCurrentValues ∧ v.currentEffects = v.ownerCurrentEffects ∧
  terms p.tables = v.terms ∧ components p.tables = v.components ∧
  v.terms.length = v.views.length ∧
  v.liveComponents = v.componentRows.zipIdx.map (fun row => (row.2,row.1.2.2)) ∧
  v.interpretedFacts.map Prod.fst = List.range v.facts.length ∧
  v.occurrences.map Prod.fst = List.range v.occurrences.length ∧
  (∀ entry ∈ v.occurrences, entry.2.artifact = v.owner)

instance (v : Projection T C A) (p : Package (Occurrence A) T C A) :
    Decidable (InputChecks v p) := by unfold InputChecks; infer_instance

def OutputChecks (v : Projection T C A) (r : Returned (Occurrence A) T C A) : Prop :=
  r.sourceRows = v.interpretedFacts.map Prod.snd ∧
  r.occurrenceTable = v.occurrences.map Prod.snd ∧ r.edges = v.edges

instance (v : Projection T C A) (r : Returned (Occurrence A) T C A) :
    Decidable (OutputChecks v r) := by unfold OutputChecks; infer_instance

/-- Evidence is an OUTPUT of finite decoding and the actual R71 reifier. -/
structure Decoded (resource : Resources) (kind : C → Kind) (v : Projection T C A) where
  package : Package (Occurrence A) T C A
  result : Returned (Occurrence A) T C A
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
    d.package.occurrenceOwners = v.occurrences.map (fun entry => (entry.2,entry.2.artifact)) ∧
    buildTables v = some d.package.tables := by
  have h := d.constructed
  unfold buildPackage at h
  cases tables : buildTables v with
  | none => simp [tables] at h
  | some p =>
    rw [tables] at h
    change some (⟨v.owner,p,
      v.facts.map (fun f => (f.1,⟨f.2.1,f.2.2.1,f.2.2.2⟩)),
      v.provenance,v.occurrences.map (fun entry => (entry.2,entry.2.artifact))⟩ :
        Package (Occurrence A) T C A) = some d.package at h
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
  exact ⟨rfl,rfl,rfl,d.checked.2.2.2.2.2.2.2.2.1,d.checked.2.2.2.2.2.2.2.2.2.1⟩

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

theorem accepted_owner_and_readbacks (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (d : Decoded resource kind v) :
    v.facts = v.ownerFacts ∧ v.provenance = v.ownerProvenance ∧
    v.currentValues = v.ownerCurrentValues ∧ v.currentEffects = v.ownerCurrentEffects ∧
    ∀ entry ∈ v.occurrences, entry.2.artifact = v.owner :=
  ⟨d.checked.1,d.checked.2.1,d.checked.2.2.1,d.checked.2.2.2.1,
    d.checked.2.2.2.2.2.2.2.2.2.2⟩

theorem foreign_occurrence_rejected (resource : Resources) (kind : C → Kind)
    (v : Projection T C A) (entry : Nat × Occurrence A)
    (member : entry ∈ v.occurrences) (foreign : entry.2.artifact ≠ v.owner) :
    decode resource kind v = .error .boundMismatch := by
  unfold decode
  split
  · rfl
  · split
    · rename_i checked
      exact False.elim (foreign (checked.2.2.2.2.2.2.2.2.2.2 entry member))
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

end YulangClosure.CompletedNativeInstanceR72
