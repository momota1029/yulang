import YulangClosure.EncodedOwnerObservationsR70

/-!
R71 models the finite successful-return branch of `reify_qualified_facts`.
Inputs are primitive borrowed rows, never an interpreted inventory or a success
flag. Allocation capacities model resource outcomes; they do not certify native
allocation. Full opaque owner/Term/occurrence identity must be authenticated by
the source/native bridge, which remains open. No theorem here asserts compiled
Rust execution. The R70 finite observation checks are executed, not assumed.
-/
namespace YulangClosure.SuccessfulReificationDecodeR71
open ProviderNativeContextR57 OccurrenceQualifiedFactReadersR65
open SemanticFactEndpointInterpretationR68

inductive Gap where
  | searchLimit | boundMismatch
  deriving DecidableEq

/- Mathematical resource inputs, not precomputed semantic success flags. -/
structure Resources where
  observationCapacity : Nat
  factCapacity : Nat
  occurrenceCapacity : Nat
  edgeCapacity : Nat
  coordinateMax : Nat

structure Package (S T C A : Type) where
  owner : A
  tables : EncodedOwnerObservationsR70.SourceTables T C
  facts : List (Nat × PrimitiveFact T)
  provenance : List (Edge S)
  occurrenceOwners : List (S × A)

structure Returned (S T C A : Type) where
  owner : A
  tables : EncodedOwnerObservationsR70.SourceTables T C
  facts : List (Nat × PrimitiveFact T)
  provenance : List (Edge S)
  observations : OwnerEndpointObservationsR69.Tables Nat
  sourceRows : List (FactRow T)
  rows : List (FactRow Nat)
  occurrenceTable : List S
  edges : List (Edge Nat)

variable {S T C A : Type} [DecidableEq S] [DecidableEq T]
  [DecidableEq C] [DecidableEq A]

def primitives (p : Package S T C A) : List (PrimitiveFact T) := p.facts.map Prod.snd
def owner (kind : C → Kind) (p : Package S T C A) : Owner T :=
  OwnerEndpointObservationsR69.assemble (EncodedOwnerObservationsR70.sourceTables kind p.tables)
def encodedOwner (kind : C → Kind) (p : Package S T C A) : Owner Nat :=
  OwnerEndpointObservationsR69.assemble (EncodedOwnerObservationsR70.encodedTables kind p.tables)

def requireSome (x : Option T) : Except Gap T :=
  match x with | none => .error .boundMismatch | some t => .ok t

def observe (resource : Resources) (kind : C → Kind) (p : Package S T C A) :
    Except Gap (OwnerEndpointObservationsR69.Tables Nat) :=
  if p.tables.observations.length > resource.observationCapacity then .error .searchLimit
  else if EncodedOwnerObservationsR70.References p.tables (primitives p) then
    if OwnerEndpointObservationsR69.Valid (EncodedOwnerObservationsR70.encodedTables kind p.tables)
        ((primitives p).map (EncodedOwnerObservationsR70.encodeFact p.tables)) then
      .ok (EncodedOwnerObservationsR70.encodedTables kind p.tables)
    else .error .boundMismatch
  else .error .boundMismatch

/- Index conversion, primitive identity and the four endpoint operations are
checked sequentially. Neither decodeFact nor decodeRows is called as an oracle. -/
def factStep (resource : Resources) (o : Owner T) (position : Nat)
    (entry : Nat × PrimitiveFact T) : Except Gap (FactRow T) := do
  if position > resource.coordinateMax then .error .searchLimit else do
  if entry.1 ≠ position ∨ entry.2.identity ≠ .semantic o.store position then
    .error .boundMismatch else do
  let lower ← requireSome (raw o entry.2.lower .positive)
  let canonicalLower ← requireSome (canonical o lower)
  let upper ← requireSome (raw o entry.2.upper .negative)
  let canonicalUpper ← requireSome (canonical o upper)
  pure ⟨entry.2.identity,entry.2.lower,entry.2.upper,lower,upper,canonicalLower,canonicalUpper⟩

def factLoop (resource : Resources) (o : Owner T) (position : Nat) :
    List (Nat × PrimitiveFact T) → Except Gap (List (FactRow T))
  | [] => .ok []
  | entry :: entries => do
      let row ← factStep resource o position entry
      let rest ← factLoop resource o (position + 1) entries
      pure (row :: rest)

/- A complete prefix determines occurrence coordinates. Recomputing its
first-appearance enumeration is a finite mathematical presentation of the
Rust vector lookup/append; computational-cost equivalence is not claimed. -/
def prefixInventory (p : Package S T C A) (rows : List (FactRow Nat))
    (priorEdges : List (Edge S)) : Inventory S Nat := ⟨p.tables.store,rows,priorEdges⟩

def edgeStep (resource : Resources) (p : Package S T C A)
    (rows : List (FactRow Nat)) (position : Nat) (priorEdges : List (Edge S))
    (edge : Edge S) : Except Gap Unit := do
  if edge.edgeIndex ≠ position ∨ lookup p.occurrenceOwners edge.occurrence ≠ some p.owner then
    .error .boundMismatch else do
  let prior := prefixInventory p rows priorEdges
  if edge.occurrence ∉ BorrowedQualifiedReadReificationR67.occurrences prior ∧
      (BorrowedQualifiedReadReificationR67.occurrences prior).length > resource.coordinateMax then
    .error .searchLimit else do
  if candidates prior edge.occurrence edge.slot ≠ [] then .error .boundMismatch else do
  match edge.fact with
  | .collected _ _ => .error .boundMismatch
  | .semantic store index => do
    if index > resource.coordinateMax then .error .searchLimit else do
    if store ≠ p.tables.store then .error .boundMismatch else do
    let primitive ← requireSome (p.facts[index]?)
    let interpreted ← requireSome (rows[index]?)
    if primitive.1 ≠ index ∨ primitive.2.identity ≠ edge.fact ∨
        interpreted.identity ≠ edge.fact ∨
        interpreted.lower ≠ EncodedOwnerObservationsR70.termToken p.tables primitive.2.lower ∨
        interpreted.upper ≠ EncodedOwnerObservationsR70.termToken p.tables primitive.2.upper then
      .error .boundMismatch else .ok ()

def edgeLoop (resource : Resources) (p : Package S T C A)
    (rows : List (FactRow Nat)) (position : Nat) (priorEdges : List (Edge S)) :
    List (Edge S) → Except Gap Unit
  | [] => .ok ()
  | edge :: rest => do
      edgeStep resource p rows position priorEdges edge
      edgeLoop resource p rows (position + 1) (priorEdges ++ [edge]) rest

def returned (kind : C → Kind) (p : Package S T C A) (rows : List (FactRow T)) :
    Returned S T C A :=
  let n := prefixInventory p (rows.map (EncodedOwnerObservationsR70.mapFactRow (EncodedOwnerObservationsR70.termToken p.tables))) p.provenance
  ⟨p.owner,p.tables,p.facts,p.provenance,EncodedOwnerObservationsR70.encodedTables kind p.tables,rows,n.facts,
    BorrowedQualifiedReadReificationR67.occurrences n,(BorrowedQualifiedReadReificationR67.encoded n).edges⟩

def reify (resource : Resources) (kind : C → Kind) (p : Package S T C A) :
    Except Gap (Returned S T C A) := do
  let observations ← observe resource kind p
  if p.facts.length > resource.factCapacity ∨
      p.provenance.length > resource.occurrenceCapacity ∨
      p.provenance.length > resource.edgeCapacity then .error .searchLimit else do
  let rows ← factLoop resource (owner kind p) 0 p.facts
  let encodedRows := rows.map (EncodedOwnerObservationsR70.mapFactRow (EncodedOwnerObservationsR70.termToken p.tables))
  edgeLoop resource p encodedRows 0 [] p.provenance
  pure { returned kind p rows with observations := observations }

def inventoryOf (r : Returned S T C A) : Inventory S Nat :=
  ⟨r.tables.store,r.rows,r.provenance⟩

omit [DecidableEq T] in
theorem require_some_equation (x : Option T) (t : T)
    (accepted : requireSome x = .ok t) : x = some t := by
  cases x <;> simp_all [requireSome]

theorem fact_step_decode (resource : Resources) (o : Owner T) (position : Nat)
    (entry : Nat × PrimitiveFact T) (row : FactRow T)
    (accepted : factStep resource o position entry = .ok row) :
    entry.1 = position ∧ decodeFact o position entry.2 = some row := by
  unfold factStep at accepted
  split at accepted
  · contradiction
  · split at accepted
    · contradiction
    · rename_i checked
      have identity := (not_or.mp checked).2
      have coordinate := (not_or.mp checked).1
      cases lo : raw o entry.2.lower .positive <;>
        simp [lo, requireSome, Except.bind, Except.pure, bind, pure] at accepted
      case some lower =>
        cases clo : canonical o lower <;>
          simp [clo] at accepted
        case some canonicalLower =>
          cases hi : raw o entry.2.upper .negative <;>
            simp [hi] at accepted
          case some upper =>
            cases chi : canonical o upper <;>
              simp [chi] at accepted
            case some canonicalUpper =>
              cases accepted
              exact ⟨Decidable.of_not_not coordinate,by
                simp [decodeFact, identity, lo, hi, clo, chi]⟩

theorem fact_loop_decode (resource : Resources) (o : Owner T) (position : Nat)
    (entries : List (Nat × PrimitiveFact T)) (rows : List (FactRow T))
    (accepted : factLoop resource o position entries = .ok rows) :
    decodeRows o position (entries.map Prod.snd) = some rows := by
  induction entries generalizing position rows with
  | nil => simp only [factLoop, Except.ok.injEq] at accepted; subst rows; rfl
  | cons entry entries ih =>
    cases head : factStep resource o position entry <;>
      simp [factLoop, head, Except.bind, Except.pure, bind, pure] at accepted
    case ok row =>
      cases tail : factLoop resource o (position + 1) entries <;>
        simp [tail] at accepted
      case ok rest =>
        cases accepted
        simp [decodeRows, (fact_step_decode resource o position entry row head).2,
          ih (position + 1) rest tail]

omit [DecidableEq S] [DecidableEq A] in
theorem observation_checks (resource : Resources) (kind : C → Kind) (p : Package S T C A)
    (observations : OwnerEndpointObservationsR69.Tables Nat)
    (accepted : observe resource kind p = .ok observations) :
    observations = EncodedOwnerObservationsR70.encodedTables kind p.tables ∧
    EncodedOwnerObservationsR70.construct kind p.tables (primitives p) = some (encodedOwner kind p) := by
  unfold observe at accepted
  split at accepted
  · contradiction
  · split at accepted
    · rename_i references
      split at accepted
      · rename_i valid
        cases accepted
        exact ⟨rfl,(EncodedOwnerObservationsR70.construction_iff kind p.tables (primitives p)).mpr ⟨references,valid⟩⟩
      · contradiction
    · contradiction

omit [DecidableEq C] in
theorem edge_step_owner_coordinate (resource : Resources) (p : Package S T C A)
    (rows : List (FactRow Nat)) (position : Nat) (priorEdges : List (Edge S))
    (edge : Edge S) (accepted : edgeStep resource p rows position priorEdges edge = .ok ()) :
    edge.edgeIndex = position ∧ lookup p.occurrenceOwners edge.occurrence = some p.owner := by
  unfold edgeStep at accepted
  split at accepted
  · contradiction
  · rename_i checked
    exact ⟨Decidable.of_not_not (not_or.mp checked).1,
      Decidable.of_not_not (not_or.mp checked).2⟩

omit [DecidableEq C] in
theorem edge_loop_owner_coordinates (resource : Resources) (p : Package S T C A)
    (rows : List (FactRow Nat)) (position : Nat) (priorEdges remaining : List (Edge S))
    (accepted : edgeLoop resource p rows position priorEdges remaining = .ok ()) :
    ∀ i edge, remaining[i]? = some edge →
      edge.edgeIndex = position + i ∧
      lookup p.occurrenceOwners edge.occurrence = some p.owner := by
  induction remaining generalizing position priorEdges with
  | nil => intro i edge atIndex; simp at atIndex
  | cons head rest ih =>
    cases step : edgeStep resource p rows position priorEdges head with
    | error gap => simp [edgeLoop,step,bind,Except.bind] at accepted
    | ok done =>
      cases done
      simp only [edgeLoop,step,bind,Except.bind] at accepted
      intro i edge atIndex
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero,Option.some.injEq] at atIndex
        subst edge
        simpa using edge_step_owner_coordinate resource p rows position priorEdges head step
      | succ i =>
        have later := ih (position + 1) (priorEdges ++ [head]) accepted i edge atIndex
        exact ⟨by omega,later.2⟩

/- This record is a conclusion of the executable branch theorem below. It is
not an input law or a proposed replacement for source typing. -/
structure ReturnEquations (kind : C → Kind) (p : Package S T C A)
    (r : Returned S T C A) : Prop where
  exactReturn : r = returned kind p r.sourceRows
  construction : EncodedOwnerObservationsR70.construct kind p.tables (primitives p) =
    some (encodedOwner kind p)
  sourceDecoded : decodeRows (owner kind p) 0 (primitives p) = some r.sourceRows
  provenanceOwned : ∀ (i : Nat) (edge : Edge S), p.provenance[i]? = some edge →
    edge.edgeIndex = i ∧ lookup p.occurrenceOwners edge.occurrence = some p.owner
  encodedDecoded : decodeRows (encodedOwner kind p) 0
    ((primitives p).map (EncodedOwnerObservationsR70.encodeFact p.tables)) = some r.rows

/- No success equation, decoding equation, Valid law or faithfulness flag is
assumed. Case analysis follows the actual completed/error return branches. -/
theorem completed_return (resource : Resources) (kind : C → Kind) (p : Package S T C A) :
    match reify resource kind p with
    | .error _ => True
    | .ok r => ReturnEquations kind p r := by
  cases completed : reify resource kind p with
  | error gap => trivial
  | ok r =>
    unfold reify at completed
    cases observed : observe resource kind p with
    | error gap => simp [observed, bind, Except.bind] at completed
    | ok observations =>
      have checked := observation_checks resource kind p observations observed
      simp only [observed, bind, Except.bind] at completed
      split at completed
      · contradiction
      · cases facts : factLoop resource (owner kind p) 0 p.facts with
        | error gap => simp [facts] at completed
        | ok rows =>
          simp only [facts] at completed
          cases edges : edgeLoop resource p
              (rows.map (EncodedOwnerObservationsR70.mapFactRow
                (EncodedOwnerObservationsR70.termToken p.tables))) 0 [] p.provenance with
          | error gap => simp [edges] at completed
          | ok done =>
            cases done
            simp only [edges, pure, Except.pure, Except.ok.injEq] at completed
            rw [checked.1] at completed
            have sameReturn : returned kind p rows = r := completed
            subst r
            have construction := checked.2
            have decoded := fact_loop_decode resource (owner kind p) 0 p.facts rows facts
            have commute := EncodedOwnerObservationsR70.decode_rows_commutes kind p.tables
              (primitives p)
              ((EncodedOwnerObservationsR70.construction_iff kind p.tables (primitives p)).mp
                construction).1.2.1 0
            refine ⟨rfl,construction,decoded,?_,?_⟩
            · simpa using edge_loop_owner_coordinates resource p
                (rows.map (EncodedOwnerObservationsR70.mapFactRow
                  (EncodedOwnerObservationsR70.termToken p.tables))) 0 [] p.provenance edges
            · change decodeRows (encodedOwner kind p) 0
                ((primitives p).map (EncodedOwnerObservationsR70.encodeFact p.tables)) =
                  some (rows.map (EncodedOwnerObservationsR70.mapFactRow
                    (EncodedOwnerObservationsR70.termToken p.tables)))
              change decodeRows (encodedOwner kind p) 0
                ((primitives p).map (EncodedOwnerObservationsR70.encodeFact p.tables)) =
                  ((decodeRows (owner kind p) 0 (primitives p)).map
                    (List.map (EncodedOwnerObservationsR70.mapFactRow
                      (EncodedOwnerObservationsR70.termToken p.tables)))) at commute
              have decodedSource : decodeRows (owner kind p) 0 (primitives p) = some rows := decoded
              rw [decodedSource] at commute
              exact commute

/- All borrowed tables and every provenance row retain order and coordinates.
Repeated provenance FactIds are retained; no uniqueness-by-FactId is assumed. -/
omit [DecidableEq A] in
theorem ordered_return_fields (kind : C → Kind) (p : Package S T C A)
    (rows : List (FactRow T)) (i : Nat) :
    (returned kind p rows).owner = p.owner ∧
    (returned kind p rows).tables = p.tables ∧
    (returned kind p rows).facts = p.facts ∧
    (returned kind p rows).provenance = p.provenance ∧
    (returned kind p rows).observations = EncodedOwnerObservationsR70.encodedTables kind p.tables ∧
    (returned kind p rows).rows[i]? = (rows[i]?).map
      (EncodedOwnerObservationsR70.mapFactRow (EncodedOwnerObservationsR70.termToken p.tables)) ∧
    (returned kind p rows).occurrenceTable =
      BorrowedQualifiedReadReificationR67.occurrences (inventoryOf (returned kind p rows)) ∧
    (returned kind p rows).edges =
      (BorrowedQualifiedReadReificationR67.encoded (inventoryOf (returned kind p rows))).edges ∧
    (returned kind p rows).edges[i]? = (p.provenance[i]?).map
      (BorrowedQualifiedReadReificationR67.encodeEdge (inventoryOf (returned kind p rows))) := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,List.getElem?_map,rfl,rfl,List.getElem?_map⟩

/- Every decoded row retains all four endpoint fields; length and original
index jointly rule out dropping or reordering a successful fact sequence. -/
theorem completed_ordered_endpoints (resource : Resources) (kind : C → Kind)
    (p : Package S T C A) :
    match reify resource kind p with
    | .error _ => True
    | .ok r => r.rows.length = p.facts.length ∧
        ∀ index row, r.rows[index]? = some row →
          ∃ f, (primitives p)[index]? = some f ∧
            row.identity = f.identity ∧
            row.lower = EncodedOwnerObservationsR70.termToken p.tables f.lower ∧
            row.upper = EncodedOwnerObservationsR70.termToken p.tables f.upper ∧
            row.identity = .semantic p.tables.store index ∧
            Interpreted (encodedOwner kind p) row := by
  have evidence := completed_return resource kind p
  cases completed : reify resource kind p with
  | error gap => trivial
  | ok r =>
    rw [completed] at evidence
    constructor
    · have length := decoded_rows_length (encodedOwner kind p)
        ((primitives p).map (EncodedOwnerObservationsR70.encodeFact p.tables)) 0 r.rows
        evidence.encodedDecoded
      simpa [primitives] using length
    · intro index row atIndex
      obtain ⟨encoded,atPrimitive,decoded⟩ := decoded_rows_index (encodedOwner kind p)
        ((primitives p).map (EncodedOwnerObservationsR70.encodeFact p.tables)) 0 r.rows
        evidence.encodedDecoded index row atIndex
      rw [List.getElem?_map] at atPrimitive
      obtain ⟨f,atSource,same⟩ := Option.map_eq_some_iff.mp atPrimitive
      subst encoded
      have equations := decoded_fact_equations (encodedOwner kind p) index
        (EncodedOwnerObservationsR70.encodeFact p.tables f) row (by simpa using decoded)
      have originalIdentity : row.identity = f.identity := by
        unfold decodeFact at decoded
        split at decoded
        · contradiction
        · rename_i identity
          exact equations.1.trans (by simpa [EncodedOwnerObservationsR70.encodeFact] using (Decidable.of_not_not identity).symm)
      exact ⟨f,atSource,originalIdentity,equations.2.1,equations.2.2.1,
        equations.1,equations.2.2.2⟩

omit [DecidableEq T] [DecidableEq C] [DecidableEq A] in
theorem complete_competitors_and_lookup (r : Returned S T C A) (s : S) (slot : Nat)
    (id : Fact) :
    candidates (BorrowedQualifiedReadReificationR67.encoded (inventoryOf r))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex (inventoryOf r) s) slot =
      (candidates (inventoryOf r) s slot).map
        (BorrowedQualifiedReadReificationR67.encodeEdge (inventoryOf r)) ∧
    resolve (BorrowedQualifiedReadReificationR67.encoded (inventoryOf r)) id =
      resolve (inventoryOf r) id ∧
    readAt (BorrowedQualifiedReadReificationR67.encoded (inventoryOf r))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex (inventoryOf r) s) slot =
      (readAt (inventoryOf r) s slot).map
        (BorrowedQualifiedReadReificationR67.encodeRead (inventoryOf r)) :=
  ⟨BorrowedQualifiedReadReificationR67.complete_competitors _ _ _,
    BorrowedQualifiedReadReificationR67.resolve_commutes _ _,
    BorrowedQualifiedReadReificationR67.lookup_commutes _ _ _⟩

omit [DecidableEq T] [DecidableEq C] [DecidableEq A] in
theorem selected_lookup (r : Returned S T C A) (s : S) (slot : Nat) (selected : FactRow Nat) :
    readSelectedAt (BorrowedQualifiedReadReificationR67.encoded (inventoryOf r))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex (inventoryOf r) s) slot selected =
      (readSelectedAt (inventoryOf r) s slot selected).map
        (BorrowedQualifiedReadReificationR67.encodeRead (inventoryOf r)) :=
  BorrowedQualifiedReadReificationR67.selected_lookup_commutes _ _ _ _

/- Explicit equality with each source row's four endpoint fields, in source
order. This uses the same sourceRows produced by the fact loop. -/
theorem completed_four_endpoint_fields (resource : Resources) (kind : C → Kind)
    (p : Package S T C A) :
    match reify resource kind p with
    | .error _ => True
    | .ok r => ∀ (i : Nat) (sourceRow : FactRow T), r.sourceRows[i]? = some sourceRow →
        ∃ row, r.rows[i]? = some row ∧ row.identity = sourceRow.identity ∧
          row.rawLower = EncodedOwnerObservationsR70.mapEndpoint
            (EncodedOwnerObservationsR70.termToken p.tables) sourceRow.rawLower ∧
          row.rawUpper = EncodedOwnerObservationsR70.mapEndpoint
            (EncodedOwnerObservationsR70.termToken p.tables) sourceRow.rawUpper ∧
          row.canonicalLower = EncodedOwnerObservationsR70.mapEndpoint
            (EncodedOwnerObservationsR70.termToken p.tables) sourceRow.canonicalLower ∧
          row.canonicalUpper = EncodedOwnerObservationsR70.mapEndpoint
            (EncodedOwnerObservationsR70.termToken p.tables) sourceRow.canonicalUpper := by
  have evidence := completed_return resource kind p
  cases completed : reify resource kind p with
  | error gap => trivial
  | ok r =>
    rw [completed] at evidence
    intro i sourceRow atIndex
    have rows : r.rows = r.sourceRows.map
        (EncodedOwnerObservationsR70.mapFactRow (EncodedOwnerObservationsR70.termToken p.tables)) :=
      congrArg Returned.rows evidence.exactReturn
    refine ⟨EncodedOwnerObservationsR70.mapFactRow
      (EncodedOwnerObservationsR70.termToken p.tables) sourceRow,?_,rfl,rfl,rfl,rfl,rfl⟩
    rw [rows,List.getElem?_map,atIndex]
    rfl

omit [DecidableEq T] [DecidableEq C] [DecidableEq A] in
theorem occurrence_prefix_coordinates (earlier later : List S) (s : S) (member : s ∈ earlier) :
    ((earlier ++ later).eraseDups).idxOf s = (earlier.eraseDups).idxOf s := by
  cases shape : earlier with
  | nil => simp [shape] at member
  | cons head tail =>
    rw [shape] at member
    rw [List.cons_append,List.eraseDups_cons,List.eraseDups_cons,List.filter_append]
    by_cases same : head = s
    · subst s
      simp
    · have inTail : s ∈ tail := (List.mem_cons.mp member).resolve_left (Ne.symm same)
      have retained : s ∈ tail.filter (fun other => !other == head) := by
        simp [inTail,Ne.symm same]
      have laterIndex := occurrence_prefix_coordinates
        (tail.filter (fun other => !other == head))
        (later.filter (fun other => !other == head)) s retained
      simpa only [List.idxOf_cons,beq_iff_eq,ite_eq_right same] using
        congrArg (fun i => i + 1) laterIndex
termination_by earlier.length
 decreasing_by
  have bound := List.length_filter_le (fun other => !other == head) tail
  simp only [shape,List.length_cons]
  omega

/- Same original Root, slot-0 route and slot-2 lambda construction. The source,
native, request, full Root, and exact use/lambda coordinates remain genuine
premises. Construction and endpoint interpretation are derived from this run. -/
theorem completed_r66_same_witnesses (resource : Resources) (kind : C → Kind)
    (p : Package S T C A) :
    match reify resource kind p with
    | .error _ => True
    | .ok r => ∀ (source : OccurrenceQualifiedConsumerR66.Source S Nat)
        (native : Native S Nat) (q : OccurrenceQualifiedConsumerR66.Request S Nat)
        (root : OccurrenceQualifiedConsumerR66.Root source
          (inventory (encodedOwner kind p) r.rows r.provenance) native q)
        (use lambda : S), q.use.occurrence = .source use → q.lambda = .source lambda →
        ∃ route construction,
          readAt (BorrowedQualifiedReadReificationR67.encoded
              (inventory (encodedOwner kind p) r.rows r.provenance))
            (BorrowedQualifiedReadReificationR67.occurrenceIndex
              (inventory (encodedOwner kind p) r.rows r.provenance) use) 0 =
                some (BorrowedQualifiedReadReificationR67.encodeRead
                  (inventory (encodedOwner kind p) r.rows r.provenance) route) ∧
          route.fact.identity = root.incidence.probe.fact ∧
          route.fact.lower = root.incidence.probe.registeredRoot ∧
          route.fact.upper = root.incidence.probe.plan.useValue ∧
          readAt (BorrowedQualifiedReadReificationR67.encoded
              (inventory (encodedOwner kind p) r.rows r.provenance))
            (BorrowedQualifiedReadReificationR67.occurrenceIndex
              (inventory (encodedOwner kind p) r.rows r.provenance) lambda) 2 =
                some (BorrowedQualifiedReadReificationR67.encodeRead
                  (inventory (encodedOwner kind p) r.rows r.provenance) construction) ∧
          construction.fact.lower = root.incidence.probe.construction.function ∧
          construction.fact.upper = root.incidence.probe.registeredRoot ∧
          Interpreted (encodedOwner kind p) route.fact ∧
          Interpreted (encodedOwner kind p) construction.fact := by
  have evidence := completed_return resource kind p
  cases completed : reify resource kind p with
  | error gap => trivial
  | ok r =>
    rw [completed] at evidence
    intro source native q root use lambda useCoordinate lambdaCoordinate
    exact r66_selected_decoded_endpoints (encodedOwner kind p)
      ((primitives p).map (EncodedOwnerObservationsR70.encodeFact p.tables)) r.rows r.provenance
      evidence.encodedDecoded source native q root use lambda useCoordinate lambdaCoordinate

/- Reification errors propagate before any later root-structure mismatch. -/
def internalRootView {X : Type} (resource : Resources) (kind : C → Kind)
    (p : Package S T C A) (rootRead : Returned S T C A → Option X) : Except Gap X := do
  let completed ← reify resource kind p
  match rootRead completed with
  | none => .error .boundMismatch
  | some root => .ok root

theorem reifier_error_propagates {X : Type} (resource : Resources) (kind : C → Kind)
    (p : Package S T C A) (rootRead : Returned S T C A → Option X) (gap : Gap)
    (failed : reify resource kind p = .error gap) :
    internalRootView resource kind p rootRead = .error gap := by
  simp [internalRootView, failed, bind, Except.bind]

omit [DecidableEq S] [DecidableEq T] [DecidableEq C] [DecidableEq A] in
theorem distinct_errors_and_no_partial_return (r : Returned S T C A) :
    (Except.error Gap.searchLimit : Except Gap (Returned S T C A)) ≠ .error .boundMismatch ∧
    (Except.error Gap.searchLimit : Except Gap (Returned S T C A)) ≠ .ok r ∧
    (Except.error Gap.boundMismatch : Except Gap (Returned S T C A)) ≠ .ok r := by
  constructor
  · intro same
    cases same
  · constructor <;> intro same <;> cases same

end YulangClosure.SuccessfulReificationDecodeR71
