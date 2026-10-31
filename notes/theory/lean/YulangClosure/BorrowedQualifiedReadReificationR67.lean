import YulangClosure.OccurrenceQualifiedConsumerR66

/-!
R67 finite owner-scoped enumeration of complete fact/provenance records.
The input is the R65 record interpretation, NOT a second mirrored package.
Rust SemanticFact contains only id/lower/upper Terms: constructing its four
raw/canonical Endpoint fields remains an OPEN source-owner obligation. Thus
these theorems establish finite record algebra, not that Rust interpretation.
Opaque owner equality must be instantiated by authentic package/store equality,
never by equality of owner-local ordinals. Allocation/overflow are not modeled.
-/
namespace YulangClosure.BorrowedQualifiedReadReificationR67
open ProviderNativeContextR57 OccurrenceQualifiedFactReadersR65

variable {S T O C : Type} [DecidableEq S] [DecidableEq O]

/-- Exact source-call/schema coordinates are retained, without normalization. -/
structure Borrowed (S T O C : Type) where
  owner : O
  inventory : Inventory S T
  sourceCalls : List C
  schemaCoordinates : List C

/-- First appearance in the COMPLETE provenance list, using exact equality. -/
def occurrences (n : Inventory S T) : List S := (n.edges.map Edge.occurrence).eraseDups

def occurrenceIndex (n : Inventory S T) (s : S) : Nat := (occurrences n).idxOf s

theorem occurrence_member (n : Inventory S T) (e : Edge S) (member : e ∈ n.edges) :
    e.occurrence ∈ occurrences n := by
  simp only [occurrences, List.mem_eraseDups]
  exact List.mem_map.mpr ⟨e, member, rfl⟩

theorem occurrence_index_reflect (n : Inventory S T) (a b : S)
    (member : a ∈ occurrences n) : occurrenceIndex n a = occurrenceIndex n b ↔ a = b := by
  constructor
  · intro equal
    have ha := List.idxOf_lt_length_of_mem member
    change (occurrences n).idxOf a = (occurrences n).idxOf b at equal
    have hb : (occurrences n).idxOf b < (occurrences n).length := equal ▸ ha
    have ra : (occurrences n)[(occurrences n).idxOf a]? = some a := by
      rw [List.getElem?_eq_getElem ha, List.getElem_idxOf ha]
    have rb : (occurrences n)[(occurrences n).idxOf b]? = some b := by
      rw [List.getElem?_eq_getElem hb, List.getElem_idxOf hb]
    rw [equal, rb] at ra
    exact (Option.some.inj ra).symm
  · intro equal; subst b; rfl

theorem occurrence_index_finite (n : Inventory S T) (s : S) (member : s ∈ occurrences n) :
    occurrenceIndex n s < (occurrences n).length := List.idxOf_lt_length_of_mem member

def encodeEdge (n : Inventory S T) (e : Edge S) : Edge Nat :=
  ⟨e.edgeIndex, e.fact, occurrenceIndex n e.occurrence, e.slot⟩

def encodeRead (n : Inventory S T) (r : Read S T) : Read Nat T := ⟨encodeEdge n r.edge, r.fact⟩

def encoded (n : Inventory S T) : Inventory Nat T :=
  ⟨n.store, n.facts, n.edges.map (encodeEdge n)⟩

/-- No row is filtered, sorted, coalesced or reconstructed. Includes endpoints. -/
theorem complete_ordered_tables (n : Inventory S T) :
    (encoded n).store = n.store ∧ (encoded n).facts = n.facts ∧
    (encoded n).edges = n.edges.map (encodeEdge n) ∧
    (encoded n).edges.length = n.edges.length ∧
    ∀ index : Nat, (encoded n).edges[index]? = (n.edges[index]?).map (encodeEdge n) := by
  exact ⟨rfl, rfl, rfl, List.length_map (encodeEdge n), fun _ => List.getElem?_map⟩

theorem edge_fields_preserved (n : Inventory S T) (e : Edge S) :
    (encodeEdge n e).edgeIndex = e.edgeIndex ∧ (encodeEdge n e).fact = e.fact ∧
    (encodeEdge n e).slot = e.slot := ⟨rfl, rfl, rfl⟩

theorem complete_competitors (n : Inventory S T) (s : S) (slot : Nat) :
    candidates (encoded n) (occurrenceIndex n s) slot =
      (candidates n s slot).map (encodeEdge n) := by
  unfold candidates encoded
  simp only [List.filter_map]
  congr 1
  apply List.filter_congr
  intro edge member
  change decide (occurrenceIndex n edge.occurrence = occurrenceIndex n s ∧ edge.slot = slot) =
    decide (edge.occurrence = s ∧ edge.slot = slot)
  simp only [occurrence_index_reflect n edge.occurrence s (occurrence_member n edge member)]

theorem resolve_commutes (n : Inventory S T) (id : Fact) :
    resolve (encoded n) id = resolve n id := by
  cases id <;> rfl

theorem lookup_commutes (n : Inventory S T) (s : S) (slot : Nat) :
    readAt (encoded n) (occurrenceIndex n s) slot = (readAt n s slot).map (encodeRead n) := by
  unfold readAt
  rw [complete_competitors]
  cases chosen : candidates n s slot with
  | nil => rfl
  | cons e rest =>
    cases rest with
    | cons second tail => rfl
    | nil =>
      simp only [List.map_cons, List.map_nil]
      rw [show (encodeEdge n e).fact = e.fact from rfl, resolve_commutes]
      cases resolve n e.fact <;> rfl

theorem selected_lookup_commutes [DecidableEq T] (n : Inventory S T) (s : S) (slot : Nat) (selected : FactRow T) :
    readSelectedAt (encoded n) (occurrenceIndex n s) slot selected =
      (readSelectedAt n s slot selected).map (encodeRead n) := by
  unfold readSelectedAt
  rw [lookup_commutes]
  cases chosen : readAt n s slot with
  | none => rfl
  | some out =>
    by_cases same : out.fact = selected
    · simp [same, encodeRead]
    · simp [same, encodeRead]

/-- Full selected-row equality: identity, Terms, raw and canonical endpoints. -/
theorem selected_fact_agreement [DecidableEq T] (n : Inventory S T) (s : S) (slot : Nat)
    (selected : FactRow T) (out : Read Nat T)
    (accepted : readSelectedAt (encoded n) (occurrenceIndex n s) slot selected = some out) :
    out.fact.identity = selected.identity ∧ out.fact.lower = selected.lower ∧
    out.fact.upper = selected.upper ∧ out.fact.rawLower = selected.rawLower ∧
    out.fact.rawUpper = selected.rawUpper ∧ out.fact.canonicalLower = selected.canonicalLower ∧
    out.fact.canonicalUpper = selected.canonicalUpper := by
  have same := ((readSelectedAt_iff _ _ _ _ _).mp accepted).2
  rw [same]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- These validations are computed, not supplied as a FaithfulExtraction law. -/
def valid (n : Inventory S T) : Bool :=
  (n.facts.zipIdx).all (fun (f,i) => decide (f.identity = .semantic n.store i)) &&
  ((n.edges.zipIdx).all (fun (e,i) => decide (e.edgeIndex = i)) &&
   n.edges.all (fun e => (resolve n e.fact).isSome && decide (candidates n e.occurrence e.slot = [e])))

structure Reified (S T O C : Type) where
  owner : O
  occurrenceTable : List S
  inventory : Inventory Nat T
  sourceCalls : List C
  schemaCoordinates : List C

/-- Owner comparison precedes interpreting every owner-local index. Failure is
none, never a successful empty inventory. Native resource errors remain OPEN. -/
def reify (expected : O) (p : Borrowed S T O C) : Option (Reified S T O C) :=
  if expected = p.owner then
    if valid p.inventory then some ⟨p.owner, occurrences p.inventory, encoded p.inventory,
      p.sourceCalls, p.schemaCoordinates⟩ else none
  else none

theorem foreign_owner_rejected (expected : O) (p : Borrowed S T O C)
    (foreign : expected ≠ p.owner) : reify expected p = none := by simp [reify, foreign]

theorem accepted_reification (expected : O) (p : Borrowed S T O C) (r : Reified S T O C)
    (accepted : reify expected p = some r) :
    expected = p.owner ∧ valid p.inventory = true ∧ r.owner = p.owner ∧
    r.occurrenceTable = occurrences p.inventory ∧ r.inventory = encoded p.inventory ∧
    r.sourceCalls = p.sourceCalls ∧ r.schemaCoordinates = p.schemaCoordinates := by
  unfold reify at accepted
  split at accepted
  · rename_i owner
    split at accepted
    · rename_i good
      cases accepted
      exact ⟨owner,good,rfl,rfl,rfl,rfl,rfl⟩
    · contradiction
  · contradiction

theorem accepted_lookup_commutes (expected : O) (p : Borrowed S T O C) (r : Reified S T O C)
    (accepted : reify expected p = some r) (s : S) (slot : Nat) :
    readAt r.inventory (occurrenceIndex p.inventory s) slot =
      (readAt p.inventory s slot).map (encodeRead p.inventory) := by
  rw [(accepted_reification expected p r accepted).2.2.2.2.1]
  exact lookup_commutes p.inventory s slot

/-- A dangling or competing row anywhere in the complete table rejects the
whole reification, even when a different selected key would read successfully. -/
theorem invalid_edge_rejected (expected : O) (p : Borrowed S T O C) (e : Edge S)
    (member : e ∈ p.inventory.edges)
    (bad : resolve p.inventory e.fact = none ∨ candidates p.inventory e.occurrence e.slot ≠ [e]) :
    reify expected p = none := by
  have invalid : valid p.inventory = false := by
    apply Bool.eq_false_iff.mpr
    intro good
    have allEdges := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp good).2).2
    have checked := List.all_eq_true.mp allEdges e member
    rcases bad with dangling | competing
    · simp [dangling] at checked
    · have single := of_decide_eq_true (Bool.and_eq_true_iff.mp checked).2
      exact competing single
  simp [reify, invalid]

/-- This is a checked owner-local condition over every indexed fact row,
not a global FactId uniqueness hypothesis. -/
theorem invalid_fact_rejected (expected : O) (p : Borrowed S T O C)
    (row : FactRow T) (index : Nat) (member : (row,index) ∈ p.inventory.facts.zipIdx)
    (wrong : row.identity ≠ .semantic p.inventory.store index) : reify expected p = none := by
  have invalid : valid p.inventory = false := by
    apply Bool.eq_false_iff.mpr
    intro good
    have allFacts := (Bool.and_eq_true_iff.mp good).1
    have checked := List.all_eq_true.mp allFacts (row,index) member
    exact wrong (of_decide_eq_true checked)
  simp [reify, invalid]

theorem invalid_edge_index_rejected (expected : O) (p : Borrowed S T O C)
    (edge : Edge S) (index : Nat) (member : (edge,index) ∈ p.inventory.edges.zipIdx)
    (wrong : edge.edgeIndex ≠ index) : reify expected p = none := by
  have invalid : valid p.inventory = false := by
    apply Bool.eq_false_iff.mpr
    intro good
    have allIndices := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp good).2).1
    have checked := List.all_eq_true.mp allIndices (edge,index) member
    exact wrong (of_decide_eq_true checked)
  simp [reify, invalid]

def readBorrowed (expected : O) (p : Borrowed S T O C) (s : S) (slot : Nat) : Option (Read Nat T) := do
  let r ← reify expected p
  readAt r.inventory (occurrenceIndex p.inventory s) slot

theorem foreign_lookup_rejected (expected : O) (p : Borrowed S T O C)
    (foreign : expected ≠ p.owner) (s : S) (slot : Nat) : readBorrowed expected p s slot = none := by
  simp [readBorrowed, foreign_owner_rejected expected p foreign]

theorem checked_lookup_commutes (expected : O) (p : Borrowed S T O C)
    (owner : expected = p.owner) (checked : valid p.inventory = true) (s : S) (slot : Nat) :
    readBorrowed expected p s slot = (readAt p.inventory s slot).map (encodeRead p.inventory) := by
  simp only [readBorrowed, reify, owner, ite_true, checked]
  exact lookup_commutes p.inventory s slot

/-- Application to R66 uses its actual Root, with its existing premises. The
same route/construction witnesses are encoded; no alternate Context is assumed. -/
theorem r66_selected_reads [DecidableEq T]
    (source : OccurrenceQualifiedConsumerR66.Source S T) (n : Inventory S T)
    (native : Native S T) (q : OccurrenceQualifiedConsumerR66.Request S T)
    (root : OccurrenceQualifiedConsumerR66.Root source n native q) (use lambda : S)
    (useCoordinate : q.use.occurrence = .source use) (lambdaCoordinate : q.lambda = .source lambda) :
    ∃ route construction,
      readAt (encoded n) (occurrenceIndex n use) 0 = some (encodeRead n route) ∧
      route.fact.identity = root.incidence.probe.fact ∧
      route.fact.lower = root.incidence.probe.registeredRoot ∧
      route.fact.upper = root.incidence.probe.plan.useValue ∧
      readAt (encoded n) (occurrenceIndex n lambda) 2 = some (encodeRead n construction) ∧
      construction.fact.lower = root.incidence.probe.construction.function ∧
      construction.fact.upper = root.incidence.probe.registeredRoot := by
  obtain ⟨route, construction, routeRead, fact, lower, upper, lambdaRead, function, registered⟩ :=
    OccurrenceQualifiedConsumerR66.selected_root_has_qualified_source_reads source n native q root
      use lambda useCoordinate lambdaCoordinate
  refine ⟨route,construction,?_,fact,lower,upper,?_,function,registered⟩
  · rw [lookup_commutes, routeRead]; rfl
  · rw [lookup_commutes, lambdaRead]; rfl

end YulangClosure.BorrowedQualifiedReadReificationR67
