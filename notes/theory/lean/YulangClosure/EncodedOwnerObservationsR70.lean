import YulangClosure.OwnerEndpointObservationsR69

/-!
R70 finite encoding of primitive observations. `T` and `C` range over complete,
equality-decided source identities, not their local ordinals. Terms use the
existing unique observation order; components use first occurrence in owner
component rows. No alternate encoded inventory or extraction law is supplied.
Actual Rust identity authentication, allocation and the original R66 Root remain
separate source/native obligations.
-/
namespace YulangClosure.EncodedOwnerObservationsR70
open ProviderNativeContextR57 OccurrenceQualifiedFactReadersR65
open SemanticFactEndpointInterpretationR68

variable {T C U : Type}

/-- Left-to-right insertion, retaining the first occurrence of every full ID. -/
def firstOccurrences [DecidableEq T] (xs : List T) : List T := xs.eraseDups

def token [DecidableEq T] (table : List T) (t : T) : Nat := table.idxOf t

def encodeRef [DecidableEq T] (table : List T) (t : T) : Option Nat :=
  if t ∈ table then some (token table t) else none

theorem first_occurrences_member [DecidableEq T] (xs : List T) (t : T) :
    t ∈ firstOccurrences xs ↔ t ∈ xs := List.mem_eraseDups

theorem first_occurrences_unique [DecidableEq T] (xs : List T) :
    (firstOccurrences xs).Nodup := by
  cases xs with
  | nil => simp [firstOccurrences]
  | cons a rest =>
    change ((a :: rest).eraseDups).Nodup
    rw [List.eraseDups_cons, List.nodup_cons]
    constructor
    · simp [List.mem_eraseDups]
    · exact first_occurrences_unique (rest.filter (fun b => !b == a))
termination_by xs.length
 decreasing_by
  have bound := List.length_filter_le (fun b => !b == a) rest
  simp only [List.length_cons]
  omega

theorem first_occurrences_order [DecidableEq T] (head : T) (tail : List T) :
    firstOccurrences (head :: tail) =
      head :: firstOccurrences (tail.filter (fun other => !other == head)) :=
  List.eraseDups_cons

theorem token_roundtrip [DecidableEq T] (table : List T) (t : T)
    (member : t ∈ table) : table[token table t]? = some t := by
  unfold token
  have bound := List.idxOf_lt_length_of_mem member
  rw [List.getElem?_eq_getElem bound, List.getElem_idxOf bound]

theorem token_reflect [DecidableEq T] (table : List T) (a b : T)
    (member : a ∈ table) : token table a = token table b ↔ a = b := by
  constructor
  · intro same
    change table.idxOf a = table.idxOf b at same
    have ha := List.idxOf_lt_length_of_mem member
    have hb : table.idxOf b < table.length := same ▸ ha
    have ra := token_roundtrip table a member
    have rb : table[token table b]? = some b := by
      unfold token
      rw [List.getElem?_eq_getElem hb, List.getElem_idxOf hb]
    change table[table.idxOf a]? = some a at ra
    change table[table.idxOf b]? = some b at rb
    rw [same, rb] at ra
    exact (Option.some.inj ra).symm
  · intro same; subst b; rfl

theorem encode_ref_roundtrip [DecidableEq T] (table : List T) (t : T) :
    encodeRef table t = some (token table t) ↔ t ∈ table := by
  simp [encodeRef]

theorem encode_ref_missing [DecidableEq T] (table : List T) (t : T)
    (missing : t ∉ table) : encodeRef table t = none := by simp [encodeRef, missing]

/-- Every TermView constructor, including complete ordered nested payloads. -/
inductive SourceView (T C : Type) where
  | leaf (item : Leaf)
  | component (id : C)
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

def mapField (e : T → U) (f : Field T) : Field U := ⟨f.name, f.optional, e f.value⟩
def mapAlternative (e : T → U) (a : Alternative T) : Alternative U :=
  ⟨a.tag, a.payloads.map e⟩

def encodeView (e : T → U) (c : C → Component) : SourceView T C → SemanticFactEndpointInterpretationR68.View U
  | .leaf l => .leaf l
  | .component id => .component (c id)
  | .liveVariable k p i => .liveVariable k p i
  | .positiveBottom => .positiveBottom
  | .negativeTop => .negativeTop
  | .negativeBottom => .negativeBottom
  | .positiveFunction a ae re r => .positiveFunction (e a) (e ae) (e re) (e r)
  | .negativeFunction a ae re r => .negativeFunction (e a) (e ae) (e re) (e r)
  | .positiveVariant alternatives => .positiveVariant (alternatives.map (mapAlternative e))
  | .negativeVariant alternatives => .negativeVariant (alternatives.map (mapAlternative e))
  | .positiveRecord fields => .positiveRecord (fields.map (mapField e))
  | .negativeRecord fields => .negativeRecord (fields.map (mapField e))
  | .positiveTuple elements => .positiveTuple (elements.map e)
  | .negativeTuple elements => .negativeTuple (elements.map e)

def sourceChildren : SourceView T C → List T
  | .positiveFunction a ae re r | .negativeFunction a ae re r => [a,ae,re,r]
  | .positiveVariant alternatives | .negativeVariant alternatives =>
      alternatives.flatMap Alternative.payloads
  | .positiveRecord fields | .negativeRecord fields => fields.map Field.value
  | .positiveTuple elements | .negativeTuple elements => elements
  | _ => []

def sourceComponents : SourceView T C → List C
  | .component c => [c]
  | _ => []

theorem nested_children_commute (e : T → U) (c : C → Component) (v : SourceView T C) :
    OwnerEndpointObservationsR69.children (encodeView e c v) = (sourceChildren v).map e := by
  cases v <;> simp [encodeView, OwnerEndpointObservationsR69.children, sourceChildren, mapAlternative, mapField,
    List.map_flatMap, List.flatMap_map, List.map_map, Function.comp_def]

theorem nested_metadata_and_order (e : T → U) (fields : List (Field T))
    (alternatives : List (Alternative T)) (elements : List T) (i : Nat) :
    (fields.map (mapField e))[i]? = (fields[i]?).map (mapField e) ∧
    (fields.map (mapField e)).map (fun f => (f.name,f.optional)) =
      fields.map (fun f => (f.name,f.optional)) ∧
    (alternatives.map (mapAlternative e))[i]? = (alternatives[i]?).map (mapAlternative e) ∧
    (alternatives.map (mapAlternative e)).map Alternative.tag = alternatives.map Alternative.tag ∧
    (alternatives.map (mapAlternative e)).map (fun a => a.payloads.length) =
      alternatives.map (fun a => a.payloads.length) ∧
    (elements.map e)[i]? = (elements[i]?).map e ∧ (elements.map e).length = elements.length := by
  simp [List.getElem?_map, List.map_map, Function.comp_def, mapField, mapAlternative]

structure Observation (T C : Type) where
  term : T
  view : SourceView T C
  children : List (Nat × T)
structure ComponentRow (T C : Type) where
  term : T
  component : C
  live : Coordinate
structure SourceTables (T C : Type) where
  store : Nat
  observations : List (Observation T C)
  componentPositions : List (T × Nat)
  componentRows : List (ComponentRow T C)
  currentValues : List Nat
  currentEffects : List Nat

variable [DecidableEq T] [DecidableEq C]

def terms (p : SourceTables T C) : List T := p.observations.map Observation.term
def components (p : SourceTables T C) : List C :=
  firstOccurrences (p.componentRows.map ComponentRow.component)
def termToken (p : SourceTables T C) : T → Nat := token (terms p)
def componentToken (kind : C → Kind) (p : SourceTables T C) (c : C) : Component :=
  ⟨token (components p) c, kind c⟩

def encodeObservation (kind : C → Kind) (p : SourceTables T C) (row : Observation T C) :
    OwnerEndpointObservationsR69.Observation Nat :=
  ⟨termToken p row.term, encodeView (termToken p) (componentToken kind p) row.view,
    row.children.map (fun child => (child.1, termToken p child.2))⟩

def encodedTables (kind : C → Kind) (p : SourceTables T C) : OwnerEndpointObservationsR69.Tables Nat :=
  { store := p.store
    observations := p.observations.map (encodeObservation kind p)
    componentPositions := p.componentPositions.map (fun entry => (termToken p entry.1,entry.2))
    componentRows := p.componentRows.map (fun row =>
      ⟨termToken p row.term,componentToken kind p row.component,row.live⟩)
    currentValues := p.currentValues
    currentEffects := p.currentEffects }

def encodeFact (p : SourceTables T C) (f : PrimitiveFact T) : PrimitiveFact Nat :=
  ⟨f.identity,termToken p f.lower,termToken p f.upper⟩

/-- Explicit finite reference checks precede any externally visible token.
Repeated equal ComponentIds must agree on full term and live coordinate. -/
def References (p : SourceTables T C) (fs : List (PrimitiveFact T)) : Prop :=
  (terms p).Nodup ∧
  (∀ f ∈ fs, f.lower ∈ terms p ∧ f.upper ∈ terms p) ∧
  (∀ row ∈ p.observations,
    (∀ t ∈ sourceChildren row.view, t ∈ terms p) ∧
    (∀ c ∈ sourceComponents row.view, c ∈ components p) ∧
    (∀ child ∈ row.children, child.2 ∈ terms p)) ∧
  (∀ row ∈ p.componentRows, row.term ∈ terms p) ∧
  (∀ entry ∈ p.componentPositions, entry.1 ∈ terms p) ∧
  (∀ a ∈ p.componentRows, ∀ b ∈ p.componentRows,
    a.component = b.component → a.term = b.term ∧ a.live = b.live)

instance (p : SourceTables T C) (fs : List (PrimitiveFact T)) : Decidable (References p fs) := by
  unfold References; infer_instance

/-- The encoded tables and facts are constructed here, then checked by OwnerEndpointObservationsR69. -/
def construct (kind : C → Kind) (p : SourceTables T C) (fs : List (PrimitiveFact T)) :
    Option (Owner Nat) :=
  if References p fs then OwnerEndpointObservationsR69.construct (encodedTables kind p) (fs.map (encodeFact p)) else none

theorem construction_iff (kind : C → Kind) (p : SourceTables T C) (fs : List (PrimitiveFact T)) :
    construct kind p fs = some (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) ↔
      References p fs ∧ OwnerEndpointObservationsR69.Valid (encodedTables kind p) (fs.map (encodeFact p)) := by
  simp [construct, OwnerEndpointObservationsR69.construct]

omit [DecidableEq C] in
theorem term_identity_reflect (p : SourceTables T C) (a b : T) (member : a ∈ terms p) :
    termToken p a = termToken p b ↔ a = b := token_reflect (terms p) a b member

omit [DecidableEq T] in
theorem component_identity_reflect (kind : C → Kind) (p : SourceTables T C)
    (a b : C) (member : a ∈ components p) :
    componentToken kind p a = componentToken kind p b ↔ a = b := by
  constructor
  · intro same
    exact (token_reflect (components p) a b member).mp (congrArg Component.identity same)
  · intro same; subst b; rfl

omit [DecidableEq C] in
theorem term_index_roundtrip (p : SourceTables T C) (t : T) (member : t ∈ terms p) :
    (terms p)[termToken p t]? = some t := token_roundtrip (terms p) t member

omit [DecidableEq T] in
theorem component_index_roundtrip (p : SourceTables T C) (c : C) (member : c ∈ components p) :
    (components p)[token (components p) c]? = some c := token_roundtrip (components p) c member


omit [DecidableEq C] in
theorem lookup_rekey [DecidableEq U] {A B : Type} (table : List (T × A)) (e : T → U) (g : A → B)
    (t : T) (reflect : ∀ x, e x = e t ↔ x = t) :
    lookup (table.map (fun entry => (e entry.1,g entry.2))) (e t) =
      (lookup table t).map g := by
  induction table with
  | nil => rfl
  | cons head tail ih =>
    by_cases same : head.1 = t
    · simp [lookup, same]
    · have encodedDifferent : e head.1 ≠ e t := fun h => same ((reflect head.1).mp h)
      simpa [lookup, same, encodedDifferent] using ih

omit [DecidableEq C] in
theorem token_point_reflect (table : List T) (t : T) (member : t ∈ table) (x : T) :
    token table x = token table t ↔ x = t := by
  simpa only [eq_comm] using token_reflect table t x member

/-- The source-valued table is constructed from the SAME primitive rows and
component tokens. It is used only to state term-encoding commutation. -/
def sourceTables (kind : C → Kind) (p : SourceTables T C) : OwnerEndpointObservationsR69.Tables T :=
  { store := p.store
    observations := p.observations.map (fun row =>
      ⟨row.term, encodeView id (componentToken kind p) row.view, row.children⟩)
    componentPositions := p.componentPositions
    componentRows := p.componentRows.map (fun row =>
      ⟨row.term, componentToken kind p row.component, row.live⟩)
    currentValues := p.currentValues
    currentEffects := p.currentEffects }

theorem observation_lookup_commutes (kind : C → Kind) (p : SourceTables T C)
    (t : T) (member : t ∈ terms p) :
    lookup (OwnerEndpointObservationsR69.viewTable (encodedTables kind p)) (termToken p t) =
      (lookup (p.observations.map (fun row => (row.term,row.view))) t).map
        (encodeView (termToken p) (componentToken kind p)) := by
  have h := lookup_rekey (p.observations.map (fun row => (row.term,row.view)))
    (termToken p) (encodeView (termToken p) (componentToken kind p)) t
    (token_point_reflect (terms p) t member)
  simpa only [encodedTables, OwnerEndpointObservationsR69.viewTable, List.map_map,
    Function.comp_def, encodeObservation] using h

theorem source_observation_lookup (kind : C → Kind) (p : SourceTables T C) (t : T) :
    lookup (OwnerEndpointObservationsR69.viewTable (sourceTables kind p)) t =
      (lookup (p.observations.map (fun row => (row.term,row.view))) t).map
        (encodeView id (componentToken kind p)) := by
  have h := lookup_rekey (p.observations.map (fun row => (row.term,row.view)))
    (fun t => t) (encodeView id (componentToken kind p)) t (fun _ => Iff.rfl)
  simpa only [sourceTables, OwnerEndpointObservationsR69.viewTable, List.map_map,
    Function.comp_def] using h

omit [DecidableEq C] in
theorem position_lookup_commutes (p : SourceTables T C) (t : T) (member : t ∈ terms p) :
    lookup (p.componentPositions.map (fun entry => (termToken p entry.1,entry.2))) (termToken p t) =
      lookup p.componentPositions t := by
  simpa using lookup_rekey p.componentPositions (termToken p) id t
    (token_point_reflect (terms p) t member)

omit [DecidableEq C] in
theorem optional_token_reflect (table : List T) (t : T) (member : t ∈ table) (item : Option T) :
    item.map (token table) = some (token table t) ↔ item = some t := by
  cases item with
  | none => simp
  | some x => simpa using token_point_reflect table t member x

theorem component_coordinate_commutes (kind : C → Kind) (p : SourceTables T C)
    (t : T) (member : t ∈ terms p) (c : Component) :
    componentCoordinate (OwnerEndpointObservationsR69.assemble (encodedTables kind p))
      (termToken p t) c =
    componentCoordinate (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) t c := by
  unfold componentCoordinate
  simp only [OwnerEndpointObservationsR69.assemble, encodedTables, sourceTables,
    position_lookup_commutes p t member, List.getElem?_map, List.map_map, Function.comp_def]
  congr 1
  funext position
  have eq : ((p.componentRows[position]?).map (fun row => termToken p row.term)) =
      some (termToken p t) ↔ (p.componentRows[position]?).map ComponentRow.term = some t := by
    simpa only [termToken, Option.map_map, Function.comp_def] using
      optional_token_reflect (terms p) t member ((p.componentRows[position]?).map ComponentRow.term)
  by_cases same : (p.componentRows[position]?).map ComponentRow.term = some t
  · have encodedSame := eq.mpr same
    simp only [encodedSame, same, ne_eq, not_true_eq_false, false_or]
  · have encodedDifferent := mt eq.mp same
    simp only [encodedDifferent, same, ne_eq, not_false_eq_true, true_or, ite_true]


/-- All endpoint constructors retain their metadata; only full Term handles
inside structural atoms change to the checked term-table token. -/
def mapValue (e : T → U) : ValueEndpoint T → ValueEndpoint U
  | .bottomPositive => .bottomPositive
  | .bottomNegative => .bottomNegative
  | .topNegative => .topNegative
  | .intPositive => .intPositive
  | .intNegative => .intNegative
  | .unitPositive => .unitPositive
  | .boolPositive => .boolPositive
  | .strPositive => .strPositive
  | .unitNegative => .unitNegative
  | .boolNegative => .boolNegative
  | .strNegative => .strNegative
  | .row i => .row i
  | .positiveFunction t => .positiveFunction (e t)
  | .negativeFunction t => .negativeFunction (e t)
  | .positiveVariant t => .positiveVariant (e t)
  | .negativeVariant t => .negativeVariant (e t)
  | .positiveRecord t => .positiveRecord (e t)
  | .negativeRecord t => .negativeRecord (e t)
  | .positiveTuple t n => .positiveTuple (e t) n
  | .negativeTuple t n => .negativeTuple (e t) n

def mapEndpoint (e : T → U) : Endpoint T → Endpoint U
  | .value v => .value (mapValue e v)
  | .effect v => .effect v

theorem view_interpretation_commutes (kind : C → Kind) (p : SourceTables T C)
    (t : T) (member : t ∈ terms p) (polarity : Polarity) (v : SourceView T C) :
    interpretView (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) (termToken p t)
        polarity (encodeView (termToken p) (componentToken kind p) v) =
      (interpretView (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) t
        polarity (encodeView id (componentToken kind p) v)).map (mapEndpoint (termToken p)) := by
  cases v
  case leaf item => cases item <;> rfl
  case component c =>
    simp only [encodeView, interpretView, component_coordinate_commutes kind p t member]
    cases located : componentCoordinate
      (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) t (componentToken kind p c) with
    | none => rfl
    | some coordinate =>
      cases k : coordinate.kind <;>
        simp [k, checkedRow, OwnerEndpointObservationsR69.assemble, encodedTables, sourceTables,
          mapEndpoint, mapValue]
  case liveVariable k actual i =>
    cases k <;> by_cases same : actual = polarity <;>
      simp [encodeView, interpretView, same, checkedRow, OwnerEndpointObservationsR69.assemble,
        encodedTables, sourceTables, mapEndpoint, mapValue]
  all_goals simp [encodeView, interpretView, mapEndpoint, mapValue]


theorem raw_commutes (kind : C → Kind) (p : SourceTables T C)
    (t : T) (member : t ∈ terms p) (polarity : Polarity) :
    raw (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) (termToken p t) polarity =
      (raw (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) t polarity).map
        (mapEndpoint (termToken p)) := by
  unfold raw
  change (lookup (OwnerEndpointObservationsR69.viewTable (encodedTables kind p))
      (termToken p t)).bind _ =
    ((lookup (OwnerEndpointObservationsR69.viewTable (sourceTables kind p)) t).bind _).map _
  rw [observation_lookup_commutes kind p t member, source_observation_lookup kind p t]
  cases observed : lookup (p.observations.map (fun row => (row.term,row.view))) t with
  | none => rfl
  | some v =>
    simpa only [Option.map_some, Option.bind_some] using
      view_interpretation_commutes kind p t member polarity v

theorem canonical_commutes (kind : C → Kind) (p : SourceTables T C) (endpoint : Endpoint T) :
    canonical (OwnerEndpointObservationsR69.assemble (encodedTables kind p))
        (mapEndpoint (termToken p) endpoint) =
      (canonical (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) endpoint).map
        (mapEndpoint (termToken p)) := by
  cases endpoint with
  | value v =>
    cases v <;> simp [canonical, checkedRow, OwnerEndpointObservationsR69.assemble,
      encodedTables, sourceTables, mapEndpoint, mapValue]
    rename_i i
    cases p.currentValues[i]? <;> simp [mapEndpoint, mapValue]
  | effect v =>
    cases v <;> simp [canonical, checkedRow, OwnerEndpointObservationsR69.assemble,
      encodedTables, sourceTables, mapEndpoint]
    rename_i i
    cases p.currentEffects[i]? <;> simp [mapEndpoint]

def mapFactRow (e : T → U) (row : FactRow T) : FactRow U :=
  ⟨row.identity,e row.lower,e row.upper,mapEndpoint e row.rawLower,mapEndpoint e row.rawUpper,
    mapEndpoint e row.canonicalLower,mapEndpoint e row.canonicalUpper⟩

theorem decode_fact_commutes (kind : C → Kind) (p : SourceTables T C) (f : PrimitiveFact T)
    (lower : f.lower ∈ terms p) (upper : f.upper ∈ terms p) (index : Nat) :
    decodeFact (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) index (encodeFact p f) =
      (decodeFact (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) index f).map
        (mapFactRow (termToken p)) := by
  unfold decodeFact
  have encodedStore : (OwnerEndpointObservationsR69.assemble (encodedTables kind p)).store = p.store := rfl
  have sourceStore : (OwnerEndpointObservationsR69.assemble (sourceTables kind p)).store = p.store := rfl
  by_cases identity : f.identity = .semantic p.store index
  · simp only [encodeFact, encodedStore, sourceStore, identity, ne_eq, not_true_eq_false, ite_false]
    rw [raw_commutes kind p f.lower lower .positive, raw_commutes kind p f.upper upper .negative]
    cases lo : raw (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) f.lower .positive with
    | none => rfl
    | some l =>
      cases hi : raw (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) f.upper .negative with
      | none => rfl
      | some u =>
        simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some]
        rw [canonical_commutes kind p l, canonical_commutes kind p u]
        cases canonical (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) l <;>
          cases canonical (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) u <;> rfl
  · simp only [encodeFact, encodedStore, sourceStore, identity, ne_eq, not_false_eq_true, ite_true,
      Option.map_none]

theorem decode_rows_commutes (kind : C → Kind) (p : SourceTables T C)
    (fs : List (PrimitiveFact T))
    (seeds : ∀ f ∈ fs, f.lower ∈ terms p ∧ f.upper ∈ terms p) (start : Nat) :
    decodeRows (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) start (fs.map (encodeFact p)) =
      (decodeRows (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) start fs).map
        (List.map (mapFactRow (termToken p))) := by
  induction fs generalizing start with
  | nil => rfl
  | cons f fs ih =>
    have head := seeds f (by simp)
    simp only [List.map_cons, decodeRows, decode_fact_commutes kind p f head.1 head.2]
    rw [ih (fun f member => seeds f (by simp [member])) (start + 1)]
    cases decodeFact (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) start f <;>
      cases decodeRows (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) (start + 1) fs <;> rfl

theorem nested_reference_roundtrip (p : SourceTables T C) (v : SourceView T C)
    (covered : ∀ t ∈ sourceChildren v, t ∈ terms p) (kind : C → Kind) :
    (OwnerEndpointObservationsR69.children (encodeView (termToken p) (componentToken kind p) v)).map
      (fun index => (terms p)[index]?) = (sourceChildren v).map some := by
  rw [nested_children_commute]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro t member
  exact term_index_roundtrip p t (covered t member)


variable {S : Type}

def mapRead (e : T → U) (out : Read S T) : Read S U := ⟨out.edge,mapFactRow e out.fact⟩
def mapInventory (e : T → U) (n : Inventory S T) : Inventory S U :=
  ⟨n.store,n.facts.map (mapFactRow e),n.edges⟩

omit [DecidableEq T] [DecidableEq C] in
theorem resolve_commutes (e : T → U) (n : Inventory S T) (id : Fact) :
    resolve (mapInventory e n) id = (resolve n id).map (mapFactRow e) := by
  cases id with
  | collected owner index => rfl
  | semantic owner index =>
    by_cases ownerSame : owner = n.store
    · simp only [resolve, mapInventory, ownerSame, ite_true, List.getElem?_map]
      cases atIndex : n.facts[index]? with
      | none => rfl
      | some row =>
        by_cases identity : row.identity = .semantic n.store index <;>
          simp [mapFactRow, identity]
    · simp [resolve, mapInventory, ownerSame]

omit [DecidableEq T] [DecidableEq C] in
theorem qualified_read_commutes [DecidableEq S] (e : T → U) (n : Inventory S T)
    (s : S) (slot : Nat) :
    readAt (mapInventory e n) s slot = (readAt n s slot).map (mapRead e) := by
  unfold readAt
  rw [show candidates (mapInventory e n) s slot = candidates n s slot from rfl]
  cases found : candidates n s slot with
  | nil => rfl
  | cons edge tail =>
    cases tail with
    | cons second rest => rfl
    | nil =>
      change (resolve (mapInventory e n) edge.fact).map _ =
        ((resolve n edge.fact).map _).map (mapRead e)
      rw [resolve_commutes]
      cases resolve n edge.fact <;> rfl

omit [DecidableEq T] [DecidableEq C] in
theorem r67_qualified_read_commutes [DecidableEq S] (e : T → U) (n : Inventory S T)
    (s : S) (slot : Nat) :
    readAt (BorrowedQualifiedReadReificationR67.encoded (mapInventory e n))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex (mapInventory e n) s) slot =
      ((readAt n s slot).map (mapRead e)).map
        (BorrowedQualifiedReadReificationR67.encodeRead (mapInventory e n)) := by
  rw [BorrowedQualifiedReadReificationR67.lookup_commutes, qualified_read_commutes]

theorem construction_validates (kind : C → Kind) (p : SourceTables T C) (fs : List (PrimitiveFact T))
    (accepted : construct kind p fs = some (OwnerEndpointObservationsR69.assemble (encodedTables kind p))) :
    References p fs ∧ OwnerEndpointObservationsR69.Valid (encodedTables kind p) (fs.map (encodeFact p)) ∧
      OwnerEndpointObservationsR69.construct (encodedTables kind p) (fs.map (encodeFact p)) =
        some (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) := by
  have checked := (construction_iff kind p fs).mp accepted
  exact ⟨checked.1,checked.2,(OwnerEndpointObservationsR69.construction_iff _ _).mpr checked.2⟩

theorem missing_references_rejected (kind : C → Kind) (p : SourceTables T C)
    (fs : List (PrimitiveFact T)) (missing : ¬ References p fs) : construct kind p fs = none := by
  simp [construct, missing]

theorem r66_same_selected_encoded_endpoints [DecidableEq S]
    (kind : C → Kind) (p : SourceTables T C) (fs : List (PrimitiveFact T))
    (accepted : construct kind p fs = some (OwnerEndpointObservationsR69.assemble (encodedTables kind p)))
    (rows : List (FactRow Nat)) (edges : List (Edge S))
    (decoded : decodeRows (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) 0
      (fs.map (encodeFact p)) = some rows)
    (source : OccurrenceQualifiedConsumerR66.Source S Nat) (native : Native S Nat)
    (q : OccurrenceQualifiedConsumerR66.Request S Nat)
    (root : OccurrenceQualifiedConsumerR66.Root source
      (inventory (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) rows edges) native q)
    (use lambda : S) (useCoordinate : q.use.occurrence = .source use)
    (lambdaCoordinate : q.lambda = .source lambda) :
    References p fs ∧ OwnerEndpointObservationsR69.Valid (encodedTables kind p) (fs.map (encodeFact p)) ∧
    ∃ route construction,
      readAt (BorrowedQualifiedReadReificationR67.encoded
          (inventory (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) rows edges))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex
          (inventory (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) rows edges) use) 0 =
          some (BorrowedQualifiedReadReificationR67.encodeRead
            (inventory (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) rows edges) route) ∧
      route.fact.identity = root.incidence.probe.fact ∧
      route.fact.lower = root.incidence.probe.registeredRoot ∧
      route.fact.upper = root.incidence.probe.plan.useValue ∧
      readAt (BorrowedQualifiedReadReificationR67.encoded
          (inventory (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) rows edges))
        (BorrowedQualifiedReadReificationR67.occurrenceIndex
          (inventory (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) rows edges) lambda) 2 =
          some (BorrowedQualifiedReadReificationR67.encodeRead
            (inventory (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) rows edges) construction) ∧
      construction.fact.lower = root.incidence.probe.construction.function ∧
      construction.fact.upper = root.incidence.probe.registeredRoot ∧
      Interpreted (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) route.fact ∧
      Interpreted (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) construction.fact := by
  have checked := construction_validates kind p fs accepted
  have result := OwnerEndpointObservationsR69.r66_same_selected_constructed_endpoints
    (encodedTables kind p) (fs.map (encodeFact p)) checked.2.2 rows edges decoded
    source native q root use lambda useCoordinate lambdaCoordinate
  exact ⟨checked.1,result.1,result.2⟩


omit [DecidableEq C] in
theorem token_list_reflect (table : List T) (xs ys : List T)
    (covered : ∀ x ∈ xs, x ∈ table) :
    xs.map (token table) = ys.map (token table) ↔ xs = ys := by
  constructor
  · intro same
    induction xs generalizing ys with
    | nil => cases ys <;> simp_all
    | cons x rest ih =>
      cases ys with
      | nil => simp at same
      | cons y tail =>
        have parts := List.cons.inj same
        have xy := (token_reflect table x y (covered x (by simp))).mp parts.1
        subst y
        exact congrArg (List.cons x) (ih tail (fun t member => covered t (by simp [member])) parts.2)
  · intro same; subst ys; rfl

theorem source_children_reflect (kind : C → Kind) (p : SourceTables T C)
    (fs : List (PrimitiveFact T))
    (accepted : construct kind p fs = some (OwnerEndpointObservationsR69.assemble (encodedTables kind p)))
    (row : Observation T C) (member : row ∈ p.observations) :
    row.children.map Prod.snd = sourceChildren row.view ∧
    ∀ child ∈ row.children, (p.observations[child.1]?).map Observation.term = some child.2 := by
  have checked := construction_validates kind p fs accepted
  have encodedMember : encodeObservation kind p row ∈ (encodedTables kind p).observations :=
    List.mem_map.mpr ⟨row,member,rfl⟩
  have children := OwnerEndpointObservationsR69.child_coordinates_exact (encodedTables kind p)
    (fs.map (encodeFact p)) checked.2.2 (encodeObservation kind p row) encodedMember
  have refs := checked.1.2.2.1 row member
  have lists : (row.children.map Prod.snd).map (token (terms p)) =
      (sourceChildren row.view).map (token (terms p)) := by
    simpa only [encodeObservation, nested_children_commute, List.map_map, termToken,
      Function.comp_def] using children.1
  constructor
  · apply (token_list_reflect (terms p) _ _ ?_).mp lists
    intro t atChild
    obtain ⟨child,atChild,same⟩ := List.mem_map.mp atChild
    exact same ▸ refs.2.2 child atChild
  · intro child atChild
    have atEncoded := children.2 (child.1,termToken p child.2)
      (List.mem_map.mpr ⟨child,atChild,rfl⟩)
    have eq : ((p.observations[child.1]?).map Observation.term).map (token (terms p)) =
        some (token (terms p) child.2) := by
      simpa only [encodedTables, encodeObservation, List.getElem?_map, Option.map_map,
        termToken, Function.comp_def] using atEncoded
    exact (optional_token_reflect (terms p) child.2 (refs.2.2 child atChild) _).mp eq

theorem source_decode_and_qualified_read [DecidableEq S]
    (kind : C → Kind) (p : SourceTables T C) (fs : List (PrimitiveFact T))
    (accepted : construct kind p fs = some (OwnerEndpointObservationsR69.assemble (encodedTables kind p)))
    (rows : List (FactRow T)) (edges : List (Edge S))
    (decoded : decodeRows (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) 0 fs = some rows)
    (s : S) (slot : Nat) :
    decodeRows (OwnerEndpointObservationsR69.assemble (encodedTables kind p)) 0 (fs.map (encodeFact p)) =
      some (rows.map (mapFactRow (termToken p))) ∧
    readAt (BorrowedQualifiedReadReificationR67.encoded
        (inventory (OwnerEndpointObservationsR69.assemble (encodedTables kind p))
          (rows.map (mapFactRow (termToken p))) edges))
      (BorrowedQualifiedReadReificationR67.occurrenceIndex
        (inventory (OwnerEndpointObservationsR69.assemble (encodedTables kind p))
          (rows.map (mapFactRow (termToken p))) edges) s) slot =
      ((readAt (inventory (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) rows edges)
        s slot).map (mapRead (termToken p))).map
        (BorrowedQualifiedReadReificationR67.encodeRead
          (inventory (OwnerEndpointObservationsR69.assemble (encodedTables kind p))
            (rows.map (mapFactRow (termToken p))) edges)) := by
  constructor
  · rw [decode_rows_commutes kind p fs ((construction_iff kind p fs).mp accepted).1.2.1, decoded]
    rfl
  · exact r67_qualified_read_commutes (termToken p)
      (inventory (OwnerEndpointObservationsR69.assemble (sourceTables kind p)) rows edges) s slot

theorem ordered_tables_and_namespaces (kind : C → Kind) (p : SourceTables T C) (i : Nat) :
    (encodedTables kind p).store = p.store ∧
    (encodedTables kind p).observations[i]? = (p.observations[i]?).map (encodeObservation kind p) ∧
    (encodedTables kind p).observations.length = p.observations.length ∧
    (encodedTables kind p).componentPositions =
      p.componentPositions.map (fun entry => (termToken p entry.1,entry.2)) ∧
    (encodedTables kind p).componentRows[i]? = (p.componentRows[i]?).map (fun row =>
      ⟨termToken p row.term,componentToken kind p row.component,row.live⟩) ∧
    (encodedTables kind p).currentValues = p.currentValues ∧
    (encodedTables kind p).currentEffects = p.currentEffects ∧
    ∀ v e, (Endpoint.value (.row v) : Endpoint Nat) ≠ .effect (.row e) := by
  exact ⟨rfl,List.getElem?_map,List.length_map _,rfl,List.getElem?_map,rfl,rfl,
    fun v e => namespaces_distinct v e⟩


omit [DecidableEq C] in
theorem token_position (table : List T) (unique : table.Nodup) (i : Nat) (t : T)
    (read : table[i]? = some t) : token table t = i := by
  obtain ⟨bound,same⟩ := List.getElem?_eq_some_iff.mp read
  unfold token
  rw [← same]
  exact unique.idxOf_getElem i bound

theorem term_token_is_source_position (kind : C → Kind) (p : SourceTables T C)
    (fs : List (PrimitiveFact T))
    (accepted : construct kind p fs = some (OwnerEndpointObservationsR69.assemble (encodedTables kind p)))
    (i : Nat) (row : Observation T C) (read : p.observations[i]? = some row) :
    termToken p row.term = i := by
  apply token_position (terms p) ((construction_iff kind p fs).mp accepted).1.1 i row.term
  simp only [terms, List.getElem?_map, read, Option.map_some]

omit [DecidableEq T] in
theorem component_numeric_token_reflect (p : SourceTables T C) (a b : C)
    (member : a ∈ components p) :
    token (components p) a = token (components p) b ↔ a = b :=
  token_reflect (components p) a b member

theorem missing_nested_component_rejected (kind : C → Kind) (p : SourceTables T C)
    (fs : List (PrimitiveFact T)) (row : Observation T C) (member : row ∈ p.observations)
    (c : C) (nested : c ∈ sourceComponents row.view) (missing : c ∉ components p) :
    construct kind p fs = none := by
  apply missing_references_rejected
  intro references
  exact missing ((references.2.2.1 row member).2.1 c nested)

theorem inconsistent_component_rejected (kind : C → Kind) (p : SourceTables T C)
    (fs : List (PrimitiveFact T)) (a b : ComponentRow T C)
    (first : a ∈ p.componentRows) (second : b ∈ p.componentRows)
    (same : a.component = b.component) (mismatch : a.term ≠ b.term ∨ a.live ≠ b.live) :
    construct kind p fs = none := by
  apply missing_references_rejected
  intro references
  have coherent := references.2.2.2.2.2 a first b second same
  exact mismatch.elim (fun h => h coherent.1) (fun h => h coherent.2)

theorem encoded_mismatch_rejected (kind : C → Kind) (p : SourceTables T C)
    (fs : List (PrimitiveFact T))
    (mismatch : ¬ OwnerEndpointObservationsR69.Valid (encodedTables kind p) (fs.map (encodeFact p))) :
    construct kind p fs = none := by
  simp [construct, OwnerEndpointObservationsR69.construct, mismatch]


/-- Rust stores child tokens inside the nested View. R69 also retains the
source child coordinate; the two are equal, rather than independent indices. -/
theorem child_token_is_source_coordinate (kind : C → Kind) (p : SourceTables T C)
    (fs : List (PrimitiveFact T))
    (accepted : construct kind p fs = some (OwnerEndpointObservationsR69.assemble (encodedTables kind p)))
    (row : Observation T C) (member : row ∈ p.observations)
    (child : Nat × T) (atChild : child ∈ row.children) :
    termToken p child.2 = child.1 := by
  apply token_position (terms p) ((construction_iff kind p fs).mp accepted).1.1
  simpa only [terms, List.getElem?_map] using
    (source_children_reflect kind p fs accepted row member).2 child atChild

end YulangClosure.EncodedOwnerObservationsR70
