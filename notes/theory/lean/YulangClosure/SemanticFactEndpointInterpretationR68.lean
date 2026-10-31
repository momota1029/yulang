import YulangClosure.BorrowedQualifiedReadReificationR67

/-!
R68 finite endpoint decoder from primitive owner records. No interpreted fact
inventory, FaithfulExtraction law or endpoint-completeness axiom is an input.
`T` equality must retain the complete arena-branded Term identity. `views` is
the finite checked term-view observation; authenticating it and the other
owner records against Rust is a separate, OPEN source correspondence premise.
All TermView payloads are retained, although endpoint discrimination inspects
only the outer constructor and tuple arity. Optional fields are not erased.
Native allocation/conversion failures are not modeled by mathematical Option.
-/
namespace YulangClosure.SemanticFactEndpointInterpretationR68
open ProviderNativeContextR57 OccurrenceQualifiedFactReadersR65

inductive Kind where | value | effect deriving DecidableEq
inductive Leaf where
  | intPositive | unitPositive | boolPositive | strPositive
  | intNegative | unitNegative | boolNegative | strNegative
  | effectBottomPositive | emptyEffectNegative
  deriving DecidableEq

/-- Opaque collected-component identity, including its namespace. -/
structure Component where
  identity : Nat
  kind : Kind
  deriving DecidableEq
structure Coordinate where
  kind : Kind
  ordinal : Nat
  deriving DecidableEq
structure Field (T : Type) where
  name : String
  optional : Bool
  value : T
structure Alternative (T : Type) where
  tag : String
  payloads : List T

/-- Exact observable cases of term.rs:198; children are the same Term handles. -/
inductive View (T : Type) where
  | leaf (item : Leaf)
  | component (id : Component)
  | liveVariable (kind : Kind) (polarity : Polarity) (ordinal : Nat)
  | positiveBottom | negativeTop | negativeBottom
  | positiveFunction (argument argumentEffect resultEffect result : T)
  | negativeFunction (argument argumentEffect resultEffect result : T)
  | positiveVariant (alternatives : List (Alternative T))
  | negativeVariant (alternatives : List (Alternative T))
  | positiveRecord (fields : List (Field T))
  | negativeRecord (fields : List (Field T))
  | positiveTuple (elements : List T)
  | negativeTuple (elements : List T)

/-- Read-only finite observations of ONE current InferenceSession. Rep-table
lengths are the corresponding live-row bounds, including nontrivial reps.
No row/value/effect interpretation function is supplied by the caller. -/
structure Owner (T : Type) where
  store : Nat
  views : List (T × View T)
  componentPositions : List (T × Nat)
  componentTerms : List T
  components : List Component
  liveComponents : List Coordinate
  valueRepresentatives : List Nat
  effectRepresentatives : List Nat

variable {T S : Type}

def lookup [DecidableEq T] {A : Type} (table : List (T × A)) (term : T) : Option A :=
  (table.find? (fun entry => entry.1 == term)).map Prod.snd

def checkedRow (o : Owner T) (kind : Kind) (ordinal : Nat) : Option (Endpoint T) :=
  match kind with
  | .value => if ordinal < o.valueRepresentatives.length then some (.value (.row ordinal)) else none
  | .effect => if ordinal < o.effectRepresentatives.length then some (.effect (.row ordinal)) else none

def componentCoordinate [DecidableEq T] (o : Owner T) (t : T) (c : Component) : Option Coordinate := do
  let position ← lookup o.componentPositions t
  if o.componentTerms[position]? ≠ some t ∨ o.components[position]? ≠ some c then none else do
    let coordinate ← o.liveComponents[position]?
    if coordinate.kind = c.kind then some coordinate else none

def leafEndpoint : Leaf → Endpoint T
  | .intPositive => .value .intPositive
  | .unitPositive => .value .unitPositive
  | .boolPositive => .value .boolPositive
  | .strPositive => .value .strPositive
  | .intNegative => .value .intNegative
  | .unitNegative => .value .unitNegative
  | .boolNegative => .value .boolNegative
  | .strNegative => .value .strNegative
  | .effectBottomPositive => .effect .bottomPositive
  | .emptyEffectNegative => .effect .emptyNegative

/-- Raw means before current representative canonicalization. Component and
live-variable rows retain their raw ordinals. Structural polarity is checked;
leaf tags carry their own polarity, as in the existing owner translations. -/
def interpretView [DecidableEq T] (o : Owner T) (t : T) (p : Polarity) : View T → Option (Endpoint T)
  | .leaf item => some (leafEndpoint item)
  | .component c => do
      let coordinate ← componentCoordinate o t c
      checkedRow o coordinate.kind coordinate.ordinal
  | .liveVariable kind actual ordinal => if actual = p then checkedRow o kind ordinal else none
  | .positiveBottom => some (.value .bottomPositive)
  | .negativeTop => some (.value .topNegative)
  | .negativeBottom => some (.value .bottomNegative)
  | .positiveFunction _ _ _ _ => if p = .positive then some (.value (.positiveFunction t)) else none
  | .negativeFunction _ _ _ _ => if p = .negative then some (.value (.negativeFunction t)) else none
  | .positiveVariant _ => if p = .positive then some (.value (.positiveVariant t)) else none
  | .negativeVariant _ => if p = .negative then some (.value (.negativeVariant t)) else none
  | .positiveRecord _ => if p = .positive then some (.value (.positiveRecord t)) else none
  | .negativeRecord _ => if p = .negative then some (.value (.negativeRecord t)) else none
  | .positiveTuple elements => if p = .positive then some (.value (.positiveTuple t elements.length)) else none
  | .negativeTuple elements => if p = .negative then some (.value (.negativeTuple t elements.length)) else none

def raw [DecidableEq T] (o : Owner T) (t : T) (p : Polarity) : Option (Endpoint T) := do
  let view ← lookup o.views t
  interpretView o t p view

def canonical (o : Owner T) : Endpoint T → Option (Endpoint T)
  | .value (.row ordinal) => do
      let representative ← o.valueRepresentatives[ordinal]?
      checkedRow o .value representative
  | .effect (.row ordinal) => do
      let representative ← o.effectRepresentatives[ordinal]?
      checkedRow o .effect representative
  | item => some item

theorem branch_equation [DecidableEq T] (o : Owner T) (t : T) (p : Polarity) (v : View T)
    (observed : lookup o.views t = some v) : raw o t p = interpretView o t p v := by
  simp [raw, observed]

theorem unavailable_rejected [DecidableEq T] (o : Owner T) (t : T) (p : Polarity)
    (unavailable : lookup o.views t = none) : raw o t p = none := by simp [raw, unavailable]

theorem component_coordinate_equation [DecidableEq T] (o : Owner T) (t : T) (c : Component)
    (position : Nat) (coordinate : Coordinate)
    (located : lookup o.componentPositions t = some position)
    (term : o.componentTerms[position]? = some t)
    (component : o.components[position]? = some c)
    (live : o.liveComponents[position]? = some coordinate)
    (kind : coordinate.kind = c.kind) : componentCoordinate o t c = some coordinate := by
  simp [componentCoordinate, located, term, component, live, kind]

theorem component_coordinate_required [DecidableEq T] (o : Owner T) (t : T) (c : Component)
    (coordinate : Coordinate) (accepted : componentCoordinate o t c = some coordinate) :
    ∃ position, lookup o.componentPositions t = some position ∧
      o.componentTerms[position]? = some t ∧ o.components[position]? = some c ∧
      o.liveComponents[position]? = some coordinate ∧ coordinate.kind = c.kind := by
  unfold componentCoordinate at accepted
  cases located : lookup o.componentPositions t with
  | none => simp [located] at accepted
  | some position =>
    simp only [located, Option.bind_eq_bind, Option.bind_some] at accepted
    split at accepted
    · contradiction
    · rename_i correct
      cases live : o.liveComponents[position]? with
      | none => simp [live] at accepted
      | some found =>
        simp only [live, Option.bind_some] at accepted
        split at accepted
        · rename_i kind
          cases accepted
          exact ⟨position, rfl, Decidable.of_not_not (not_or.mp correct).1,
            Decidable.of_not_not (not_or.mp correct).2, live, kind⟩
        · contradiction

theorem wrong_live_polarity_rejected [DecidableEq T] (o : Owner T) (t : T)
    (requested actual : Polarity) (kind : Kind) (ordinal : Nat) (wrong : actual ≠ requested) :
    interpretView o t requested (.liveVariable kind actual ordinal) = none := by
  simp [interpretView, wrong]

theorem component_branch_equation [DecidableEq T] (o : Owner T) (t : T) (p : Polarity)
    (c : Component) (coordinate : Coordinate)
    (located : componentCoordinate o t c = some coordinate) :
    interpretView o t p (.component c) = checkedRow o coordinate.kind coordinate.ordinal := by
  simp [interpretView, located]

theorem missing_component_position_rejected [DecidableEq T] (o : Owner T) (t : T) (c : Component)
    (missing : lookup o.componentPositions t = none) : componentCoordinate o t c = none := by
  simp [componentCoordinate, missing]

theorem component_roundtrip_mismatch_rejected [DecidableEq T] (o : Owner T) (t : T)
    (c : Component) (position : Nat) (located : lookup o.componentPositions t = some position)
    (mismatch : o.componentTerms[position]? ≠ some t ∨ o.components[position]? ≠ some c) :
    componentCoordinate o t c = none := by simp [componentCoordinate, located, mismatch]

theorem unavailable_live_coordinate_rejected [DecidableEq T] (o : Owner T) (t : T)
    (c : Component) (position : Nat) (located : lookup o.componentPositions t = some position)
    (missing : o.liveComponents[position]? = none) : componentCoordinate o t c = none := by
  simp [componentCoordinate, located, missing]

theorem live_branch_equation [DecidableEq T] (o : Owner T) (t : T) (p : Polarity)
    (kind : Kind) (ordinal : Nat) :
    interpretView o t p (.liveVariable kind p ordinal) = checkedRow o kind ordinal := by
  simp [interpretView]

/-- Includes all ten leaf cases; no polarity filtering is silently added. -/
theorem leaf_branch_equation [DecidableEq T] (o : Owner T) (t : T) (p : Polarity) (l : Leaf) :
    interpretView o t p (.leaf l) = some (leafEndpoint l) := rfl

theorem structural_branch_equations [DecidableEq T] (o : Owner T) (t a ae re r : T)
    (fields : List (Field T)) (alternatives : List (Alternative T)) (elements : List T) :
    interpretView o t .positive (.positiveFunction a ae re r) = some (.value (.positiveFunction t)) ∧
    interpretView o t .negative (.negativeFunction a ae re r) = some (.value (.negativeFunction t)) ∧
    interpretView o t .positive (.positiveRecord fields) = some (.value (.positiveRecord t)) ∧
    interpretView o t .negative (.negativeRecord fields) = some (.value (.negativeRecord t)) ∧
    interpretView o t .positive (.positiveVariant alternatives) = some (.value (.positiveVariant t)) ∧
    interpretView o t .negative (.negativeVariant alternatives) = some (.value (.negativeVariant t)) ∧
    interpretView o t .positive (.positiveTuple elements) = some (.value (.positiveTuple t elements.length)) ∧
    interpretView o t .negative (.negativeTuple elements) = some (.value (.negativeTuple t elements.length)) := by
  simp [interpretView]

theorem wrong_structural_polarities_rejected [DecidableEq T] (o : Owner T) (t a ae re r : T)
    (fields : List (Field T)) (alternatives : List (Alternative T)) (elements : List T) :
    interpretView o t .negative (.positiveFunction a ae re r) = none ∧
    interpretView o t .positive (.negativeFunction a ae re r) = none ∧
    interpretView o t .negative (.positiveRecord fields) = none ∧
    interpretView o t .positive (.negativeRecord fields) = none ∧
    interpretView o t .negative (.positiveVariant alternatives) = none ∧
    interpretView o t .positive (.negativeVariant alternatives) = none ∧
    interpretView o t .negative (.positiveTuple elements) = none ∧
    interpretView o t .positive (.negativeTuple elements) = none := by simp [interpretView]

theorem canonical_value_equation (o : Owner T) (row representative : Nat)
    (read : o.valueRepresentatives[row]? = some representative)
    (inBounds : representative < o.valueRepresentatives.length) :
    canonical o (.value (.row row)) = some (.value (.row representative)) := by
  simp [canonical, read, checkedRow, inBounds]

theorem canonical_effect_equation (o : Owner T) (row representative : Nat)
    (read : o.effectRepresentatives[row]? = some representative)
    (inBounds : representative < o.effectRepresentatives.length) :
    canonical o (.effect (.row row)) = some (.effect (.row representative)) := by
  simp [canonical, read, checkedRow, inBounds]

theorem missing_representatives_rejected (o : Owner T) (row : Nat)
    (valueMissing : o.valueRepresentatives[row]? = none)
    (effectMissing : o.effectRepresentatives[row]? = none) :
    canonical o (.value (.row row)) = none ∧ canonical o (.effect (.row row)) = none := by
  simp [canonical, valueMissing, effectMissing]

theorem out_of_bounds_rows_rejected (o : Owner T) (row : Nat)
    (valueMissing : ¬ row < o.valueRepresentatives.length)
    (effectMissing : ¬ row < o.effectRepresentatives.length) :
    checkedRow o .value row = none ∧ checkedRow o .effect row = none := by
  simp [checkedRow, valueMissing, effectMissing]

theorem extremes_and_effect_leaves [DecidableEq T] (o : Owner T) (t : T) (p : Polarity) :
    interpretView o t p .positiveBottom = some (.value .bottomPositive) ∧
    interpretView o t p .negativeBottom = some (.value .bottomNegative) ∧
    interpretView o t p .negativeTop = some (.value .topNegative) ∧
    interpretView o t p (.leaf .effectBottomPositive) = some (.effect .bottomPositive) ∧
    interpretView o t p (.leaf .emptyEffectNegative) = some (.effect .emptyNegative) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem namespaces_distinct (value effect : Nat) :
    (Endpoint.value (.row value) : Endpoint T) ≠ .effect (.row effect) := by intro h; cases h

structure PrimitiveFact (T : Type) where
  identity : Fact
  lower : T
  upper : T

def decodeFact [DecidableEq T] (o : Owner T) (index : Nat) (f : PrimitiveFact T) : Option (FactRow T) := do
  if f.identity ≠ .semantic o.store index then none else do
    let lower ← raw o f.lower .positive
    let upper ← raw o f.upper .negative
    let canonicalLower ← canonical o lower
    let canonicalUpper ← canonical o upper
    some ⟨f.identity, f.lower, f.upper, lower, upper, canonicalLower, canonicalUpper⟩

def Interpreted [DecidableEq T] (o : Owner T) (row : FactRow T) : Prop :=
  raw o row.lower .positive = some row.rawLower ∧
  raw o row.upper .negative = some row.rawUpper ∧
  canonical o row.rawLower = some row.canonicalLower ∧
  canonical o row.rawUpper = some row.canonicalUpper

theorem decoded_fact_equations [DecidableEq T] (o : Owner T) (index : Nat)
    (f : PrimitiveFact T) (row : FactRow T) (accepted : decodeFact o index f = some row) :
    row.identity = .semantic o.store index ∧ row.lower = f.lower ∧ row.upper = f.upper ∧
      Interpreted o row := by
  unfold decodeFact at accepted
  split at accepted
  · contradiction
  · rename_i identity
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨lo, lower, hi, upper, clo, canonicalLower, chi, canonicalUpper, same⟩ := accepted
    have sameRow := Option.some.inj same
    subst row
    exact ⟨Decidable.of_not_not identity, rfl, rfl, lower, upper, canonicalLower, canonicalUpper⟩

/-- Every input row is decoded once in its original position. One unavailable
row rejects the complete table; there is no filterMap or fallback inventory. -/
def decodeRows [DecidableEq T] (o : Owner T) (start : Nat) : List (PrimitiveFact T) → Option (List (FactRow T))
  | [] => some []
  | f :: fs => do
      let row ← decodeFact o start f
      let rows ← decodeRows o (start + 1) fs
      some (row :: rows)

theorem decoded_rows_length [DecidableEq T] (o : Owner T) (fs : List (PrimitiveFact T))
    (start : Nat) (rows : List (FactRow T)) (accepted : decodeRows o start fs = some rows) :
    rows.length = fs.length := by
  induction fs generalizing start rows with
  | nil => simp [decodeRows] at accepted; subst rows; rfl
  | cons f fs ih =>
    simp only [decodeRows, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨head, _, rest, tail, same⟩ := accepted
    have sameRows := Option.some.inj same
    subst rows
    exact congrArg Nat.succ (ih (start + 1) rest tail)

theorem decoded_rows_index [DecidableEq T] (o : Owner T) (fs : List (PrimitiveFact T))
    (start : Nat) (rows : List (FactRow T)) (accepted : decodeRows o start fs = some rows)
    (index : Nat) (row : FactRow T) (atIndex : rows[index]? = some row) :
    ∃ f, fs[index]? = some f ∧ decodeFact o (start + index) f = some row := by
  induction fs generalizing start rows index with
  | nil => simp [decodeRows] at accepted; subst rows; simp at atIndex
  | cons f fs ih =>
    simp only [decodeRows, Option.bind_eq_bind, Option.bind_eq_some_iff] at accepted
    obtain ⟨head, first, rest, tail, same⟩ := accepted
    have sameRows := Option.some.inj same
    subst rows
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at atIndex
              subst row; exact ⟨f, rfl, by simpa using first⟩
    | succ i =>
      obtain ⟨source, position, decoded⟩ := ih (start + 1) rest tail i atIndex
      exact ⟨source, position, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using decoded⟩

def inventory (o : Owner T) (rows : List (FactRow T)) (edges : List (Edge S)) : Inventory S T :=
  ⟨o.store, rows, edges⟩

theorem decoded_table_preserves_all_provenance (o : Owner T) (rows : List (FactRow T))
    (edges : List (Edge S)) : (inventory o rows edges).edges = edges ∧
    (inventory o rows edges).facts = rows ∧ (inventory o rows edges).store = o.store := ⟨rfl,rfl,rfl⟩

theorem decoded_read_interpreted [DecidableEq S] [DecidableEq T] (o : Owner T)
    (fs : List (PrimitiveFact T)) (rows : List (FactRow T)) (edges : List (Edge S))
    (accepted : decodeRows o 0 fs = some rows) (s : S) (slot : Nat) (out : Read S T)
    (read : readAt (inventory o rows edges) s slot = some out) :
    ∃ index f, fs[index]? = some f ∧ decodeFact o index f = some out.fact ∧
      out.fact.identity = .semantic o.store index ∧ out.fact.lower = f.lower ∧
      out.fact.upper = f.upper ∧ Interpreted o out.fact := by
  have resolved := ((readAt_iff _ _ _ _).mp read).2
  obtain ⟨index, _, atIndex, _⟩ := (resolve_iff _ _ _).mp resolved
  obtain ⟨f, source, decoded⟩ := decoded_rows_index o fs 0 rows accepted index out.fact atIndex
  have decoded' : decodeFact o index f = some out.fact := by simpa using decoded
  exact ⟨index, f, source, decoded', decoded_fact_equations o index f out.fact decoded'⟩

/-- Application to R67 and the SAME actual R66 route/construction witnesses.
All R66 source/native/root premises remain explicit. Endpoint interpretation
now follows from decoding primitive rows, rather than from an input Inventory.
Authenticating these primitive observations against Rust remains OPEN. -/
theorem r66_selected_decoded_endpoints [DecidableEq S] [DecidableEq T]
    (o : Owner T) (fs : List (PrimitiveFact T)) (rows : List (FactRow T)) (edges : List (Edge S))
    (decoded : decodeRows o 0 fs = some rows)
    (source : OccurrenceQualifiedConsumerR66.Source S T) (native : Native S T)
    (q : OccurrenceQualifiedConsumerR66.Request S T)
    (root : OccurrenceQualifiedConsumerR66.Root source (inventory o rows edges) native q)
    (use lambda : S) (useCoordinate : q.use.occurrence = .source use)
    (lambdaCoordinate : q.lambda = .source lambda) :
    ∃ route construction,
      readAt (BorrowedQualifiedReadReificationR67.encoded (inventory o rows edges))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex (inventory o rows edges) use) 0 =
          some (BorrowedQualifiedReadReificationR67.encodeRead (inventory o rows edges) route) ∧
      route.fact.identity = root.incidence.probe.fact ∧
      route.fact.lower = root.incidence.probe.registeredRoot ∧
      route.fact.upper = root.incidence.probe.plan.useValue ∧
      readAt (BorrowedQualifiedReadReificationR67.encoded (inventory o rows edges))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex (inventory o rows edges) lambda) 2 =
          some (BorrowedQualifiedReadReificationR67.encodeRead (inventory o rows edges) construction) ∧
      construction.fact.lower = root.incidence.probe.construction.function ∧
      construction.fact.upper = root.incidence.probe.registeredRoot ∧
      Interpreted o route.fact ∧ Interpreted o construction.fact := by
  obtain ⟨route, construction, routeRead, fact, lower, upper, lambdaRead, function, registered⟩ :=
    OccurrenceQualifiedConsumerR66.selected_root_has_qualified_source_reads source
      (inventory o rows edges) native q root use lambda useCoordinate lambdaCoordinate
  have routeDecoded := decoded_read_interpreted o fs rows edges decoded use 0 route routeRead
  have lambdaDecoded := decoded_read_interpreted o fs rows edges decoded lambda 2 construction lambdaRead
  obtain ⟨_, _, _, _, _, _, _, routeEquations⟩ := routeDecoded
  obtain ⟨_, _, _, _, _, _, _, lambdaEquations⟩ := lambdaDecoded
  refine ⟨route, construction, ?_, fact, lower, upper, ?_, function, registered,
    routeEquations, lambdaEquations⟩
  · rw [BorrowedQualifiedReadReificationR67.lookup_commutes, routeRead]; rfl
  · rw [BorrowedQualifiedReadReificationR67.lookup_commutes, lambdaRead]; rfl

/-! A finite mathematical discriminator, not a native/source execution receipt.
The two namespaces intentionally use the SAME ordinals and nontrivial reps.
The Lambda Function remains a value atom; its upper component is a value row.
-/
def fixtureOwner : Owner Nat :=
  { store := 2
    views := [(200, .positiveFunction 1 2 3 4), (300, .component ⟨9,.value⟩),
      (400, .negativeFunction 5 6 7 8)]
    componentPositions := [(300,0)]
    componentTerms := [300]
    components := [⟨9,.value⟩]
    liveComponents := [⟨.value,0⟩]
    valueRepresentatives := [1,1]
    effectRepresentatives := [1,1] }
def fixtureFacts : List (PrimitiveFact Nat) :=
  [⟨.semantic 2 0,300,400⟩, ⟨.semantic 2 1,200,300⟩]
def fixtureRows : List (FactRow Nat) :=
  [⟨.semantic 2 0,300,400,.value (.row 0),.value (.negativeFunction 400),
      .value (.row 1),.value (.negativeFunction 400)⟩,
   ⟨.semantic 2 1,200,300,.value (.positiveFunction 200),.value (.row 0),
      .value (.positiveFunction 200),.value (.row 1)⟩]
def fixtureEdges : List (Edge Nat) :=
  [⟨0,.semantic 2 0,100,0⟩,⟨1,.semantic 2 0,101,0⟩,⟨2,.semantic 2 1,17,2⟩]

theorem finite_nontrivial_representatives_and_lambda :
    decodeRows fixtureOwner 0 fixtureFacts = some fixtureRows ∧
    canonical fixtureOwner (.value (.row 0)) = some (.value (.row 1)) ∧
    canonical fixtureOwner (.effect (.row 0)) = some (.effect (.row 1)) ∧
    raw fixtureOwner 200 .positive = some (.value (.positiveFunction 200)) ∧
    raw fixtureOwner 200 .negative = none := by decide

theorem finite_qualified_reads_and_competitors :
    (readAt (inventory fixtureOwner fixtureRows fixtureEdges) 100 0).map (fun r => r.fact.identity) =
      some (.semantic 2 0) ∧
    (readAt (inventory fixtureOwner fixtureRows fixtureEdges) 101 0).map (fun r => r.fact.identity) =
      some (.semantic 2 0) ∧
    (readAt (inventory fixtureOwner fixtureRows fixtureEdges) 17 2).map (fun r => r.fact.lower) = some 200 ∧
    readAt (inventory fixtureOwner fixtureRows (fixtureEdges ++ [⟨3,.semantic 2 0,100,0⟩])) 100 0 = none ∧
    readAt (inventory fixtureOwner fixtureRows fixtureEdges) 102 0 = none := by decide

end YulangClosure.SemanticFactEndpointInterpretationR68
