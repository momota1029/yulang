import YulangClosure.SimpleSubRegularConstraintSoundness
import YulangClosure.SimpleSubScopedPublication

/-! Executable finite syntax decoding connects scoped publication to a shared
regular graph solution. Reference assignments are data, not satisfying models.
All four Function ports and whole finite record/tuple/variant metadata are
preserved. Union/intersection decoding fails explicitly. This does not prove
native graph serialization, trace production, or original source Call coverage. -/
namespace YulangClosure.SimpleSub.RegularPublication
open Regular

abbrev References := Kind → Nat → Nat

deriving instance DecidableEq for Node

def findList {k} (wanted : Node k) : List (Node k) → Option Nat
  | [] => none
  | head :: tail => if head = wanted then some 0 else (findList wanted tail).map Nat.succ

def findNode (graph : Graph) {k} (wanted : Node k) : Option Nat := findList wanted (graph k)

theorem findList_sound {k} {wanted : Node k} {nodes : List (Node k)} {index : Nat}
    (found : findList wanted nodes = some index) : lookupList nodes index = some wanted := by
  induction nodes generalizing index with
  | nil => cases found
  | cons head tail ih =>
      by_cases same : head = wanted
      · simp only [findList, same, ↓reduceIte, Option.some.injEq] at found
        subst index
        simp [lookupList, same]
      · simp only [findList, same, ↓reduceIte] at found
        cases ht : findList wanted tail with
        | none => simp [ht] at found
        | some n =>
            simp only [ht, Option.map_some, Option.some.injEq] at found
            subst index
            exact ih ht

theorem findNode_sound {graph : Graph} {k} {wanted : Node k} {index : Nat}
    (found : findNode graph wanted = some index) : graph.lookup k index = some wanted :=
  findList_sound found

def checkedReference (graph : Graph) (k : Kind) (index : Nat) : Option Nat :=
  match graph.lookup k index with
  | some _ => some index
  | none => none

def prependRecord (graph : Graph) (label : Nat) (optional : Bool) (field tail : Nat) : Option Nat :=
  match graph.lookup .value tail with
  | some (.record fields) => findNode graph (.record (⟨label,optional,field⟩ :: fields))
  | _ => none

def prependTuple (graph : Graph) (head tail : Nat) : Option Nat :=
  match graph.lookup .value tail with
  | some (.tuple elements) => findNode graph (.tuple (head :: elements))
  | _ => none

def prependVariant (graph : Graph) (tag payloads tail : Nat) : Option Nat :=
  match graph.lookup .value payloads, graph.lookup .value tail with
  | some (.tuple elements), some (.variant alternatives) =>
      findNode graph (.variant (⟨tag,elements⟩ :: alternatives))
  | _, _ => none

/-- Total structural decoder: success is a reference to an exact existing
constructor, with children obtained from the recursive calls. A row tail is
unpacked as a finite existing list, never unfolded into an infinite row spine. -/
def decodeTerm (graph : Graph) (refs : References) : {k : Kind} → Term k → Option Nat
  | k, .var identity => checkedReference graph k (refs k identity)
  | k, .atom identity => findNode graph (k := k) (.atom identity)
  | k, .bottom => findNode graph (k := k) .bottom
  | k, .top => findNode graph (k := k) .top
  | _, .union _ _ | _, .intersection _ _ => none
  | .value, .function a ae re r => do
      let a' ← decodeTerm graph refs a
      let ae' ← decodeTerm graph refs ae
      let re' ← decodeTerm graph refs re
      let r' ← decodeTerm graph refs r
      findNode graph (.function a' ae' re' r')
  | .value, .recordNil => findNode graph (.record [])
  | .value, .recordCons label optional field tail => do
      let field' ← decodeTerm graph refs field
      let tail' ← decodeTerm graph refs tail
      prependRecord graph label optional field' tail'
  | .value, .tupleNil => findNode graph (.tuple [])
  | .value, .tupleCons head tail => do
      let head' ← decodeTerm graph refs head
      let tail' ← decodeTerm graph refs tail
      prependTuple graph head' tail'
  | .value, .variantNil => findNode graph (.variant [])
  | .value, .variantCons tag payloads tail => do
      let payloads' ← decodeTerm graph refs payloads
      let tail' ← decodeTerm graph refs tail
      prependVariant graph tag payloads' tail'

theorem decodeTerm_rename (graph : Graph) (refs : References) (q : Renaming)
    {k} (term : Term k) :
    decodeTerm graph refs (term.rename q) =
      decodeTerm graph (fun k i => refs k (q k i)) term := by
  induction term <;> simp_all [Term.rename, Term.subst, decodeTerm]

theorem decodeTerm_congr_bounded {n graph refs refs' k} {term : Term k}
    (bounded : Generalization.Bounded n term)
    (same : ∀ k i, i < n → refs k i = refs' k i) :
    decodeTerm graph refs term = decodeTerm graph refs' term := by
  induction term <;> simp_all [Generalization.Bounded, decodeTerm]

/-- The existing freshening commuting square is now realized by the actual
term decoder, with one reference assignment for all occurrences and ports. -/
theorem decode_freshen_transport {n count boundary before after q use graph refs k}
    {term : Term k} (anchors : Generalization.PreservesAnchors n boundary before after q)
    (useBound : use < count) (bounded : Generalization.Bounded n term) :
    decodeTerm graph
      (fun k i => refs k (Generalization.transport n count boundary after q k i))
      (term.rename (Generalization.freshen n boundary before use)) =
    decodeTerm graph refs
      ((term.rename q).rename (Generalization.freshen n boundary after use)) := by
  simp only [decodeTerm_rename]
  apply decodeTerm_congr_bounded bounded
  intro k i hi
  rw [Generalization.transport_freshen anchors useBound hi]

def Found (graph : Graph) (k : Kind) (result : Option Nat) : Prop :=
  ∀ identity, result = some identity → Reference.Exists graph ⟨k,identity⟩

theorem found_none (graph : Graph) (k : Kind) : Found graph k none := by
  intro identity h; cases h

theorem found_findNode (graph : Graph) {k} (node : Node k) : Found graph k (findNode graph node) :=
  fun _ h => ⟨node,findNode_sound h⟩

theorem found_bind {α : Type} {graph : Graph} {k} (input : Option α) (next : α → Option Nat)
    (all : ∀ value, Found graph k (next value)) : Found graph k (input.bind next) := by
  cases input with
  | none => exact found_none _ _
  | some value => exact all value

theorem checkedReference_found (graph : Graph) (k : Kind) (identity : Nat) :
    Found graph k (checkedReference graph k identity) := by
  intro result decoded
  cases h : graph.lookup k identity with
  | none => simp [checkedReference,h] at decoded
  | some node =>
      simp only [checkedReference,h,Option.some.injEq] at decoded
      subst result
      exact ⟨node,h⟩

theorem prependRecord_found (graph : Graph) (label : Nat) (optional : Bool) (field tail : Nat) :
    Found graph .value (prependRecord graph label optional field tail) := by
  cases h : graph.lookup .value tail with
  | none => simp [prependRecord,h,Found]
  | some node => cases node <;> simp only [prependRecord,h] <;>
      first | exact found_none _ _ | exact found_findNode _ _

theorem prependTuple_found (graph : Graph) (head tail : Nat) :
    Found graph .value (prependTuple graph head tail) := by
  cases h : graph.lookup .value tail with
  | none => simp [prependTuple,h,Found]
  | some node => cases node <;> simp only [prependTuple,h] <;>
      first | exact found_none _ _ | exact found_findNode _ _

theorem prependVariant_found (graph : Graph) (tag payloads tail : Nat) :
    Found graph .value (prependVariant graph tag payloads tail) := by
  cases hp : graph.lookup .value payloads with
  | none => simp [prependVariant,hp,Found]
  | some payloadNode =>
      cases ht : graph.lookup .value tail with
      | none => cases payloadNode <;> simp [prependVariant,hp,ht,Found]
      | some tailNode => cases payloadNode <;> cases tailNode <;>
          simp only [prependVariant,hp,ht] <;>
          first | exact found_none _ _ | exact found_findNode _ _

/-- Every decoded reference really exists in the same graph. -/
theorem decodeTerm_found (graph : Graph) (refs : References) {k} (term : Term k) :
    Found graph k (decodeTerm graph refs term) := by
  cases term with
  | var identity => exact checkedReference_found _ _ _
  | atom identity => exact found_findNode _ _
  | bottom => exact found_findNode _ _
  | top => exact found_findNode _ _
  | union => exact found_none _ _
  | intersection => exact found_none _ _
  | function a ae re r =>
      apply found_bind; intro a'
      apply found_bind; intro ae'
      apply found_bind; intro re'
      apply found_bind; intro r'
      exact found_findNode _ _
  | recordNil => exact found_findNode _ _
  | recordCons label optional field tail =>
      apply found_bind; intro field'
      apply found_bind; intro tail'
      exact prependRecord_found _ _ _ _ _
  | tupleNil => exact found_findNode _ _
  | tupleCons head tail =>
      apply found_bind; intro head'
      apply found_bind; intro tail'
      exact prependTuple_found _ _ _
  | variantNil => exact found_findNode _ _
  | variantCons tag payloads tail =>
      apply found_bind; intro payloads'
      apply found_bind; intro tail'
      exact prependVariant_found _ _ _ _

def decodeConstraint (graph : Graph) (refs : References) (clause : Constraint) : Option Comparison := do
  let lower ← decodeTerm graph refs clause.lower
  let upper ← decodeTerm graph refs clause.upper
  pure ⟨clause.kind,lower,upper⟩

def decodeStore (graph : Graph) (refs : References) : Store → Option (List Comparison)
  | [] => some []
  | clause :: rest => do
      let pair ← decodeConstraint graph refs clause
      let pairs ← decodeStore graph refs rest
      pure (pair :: pairs)

/-- Interpretation uses the independently defined all-depth regular relation;
it is not defined as acceptance of the finite certificate. -/
def ClauseSatisfied (graph : Graph) (refs : References) (clause : Constraint) : Prop :=
  ∃ pair, decodeConstraint graph refs clause = some pair ∧ RegularSub graph pair

def StoreSatisfied (graph : Graph) (refs : References) (store : Store) : Prop :=
  ∀ clause, clause ∈ store → ClauseSatisfied graph refs clause

theorem decodeConstraint_rename (graph : Graph) (refs : References) (q : Renaming)
    (clause : Constraint) :
    decodeConstraint graph refs (clause.rename q) =
      decodeConstraint graph (fun k i => refs k (q k i)) clause := by
  simp [decodeConstraint, Constraint.rename, decodeTerm_rename]

theorem clause_rename (graph : Graph) (refs : References) (q : Renaming) (clause : Constraint) :
    ClauseSatisfied graph refs (clause.rename q) ↔
      ClauseSatisfied graph (fun k i => refs k (q k i)) clause := by
  simp only [ClauseSatisfied,decodeConstraint_rename]

theorem bind_some {α β : Type} {input : Option α} {next : α → Option β} {result : β}
    (h : input.bind next = some result) :
    ∃ value, input = some value ∧ next value = some result := by
  cases input with
  | none => cases h
  | some value => exact ⟨value,rfl,h⟩

theorem decodeStore_member {graph refs store pairs}
    (decoded : decodeStore graph refs store = some pairs) :
    ∀ clause, clause ∈ store → ∃ pair, pair ∈ pairs ∧
      decodeConstraint graph refs clause = some pair := by
  induction store generalizing pairs with
  | nil => intro clause hc; cases hc
  | cons head tail ih =>
      rcases bind_some decoded with ⟨pair,hpair,remaining⟩
      rcases bind_some remaining with ⟨rest,hrest,whole⟩
      have same : pair :: rest = pairs := Option.some.inj whole
      subst pairs
      intro clause hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨pair,by simp,hpair⟩
      · rcases ih hrest clause hc with ⟨other,member,found⟩
        exact ⟨other,List.mem_cons_of_mem _ member,found⟩

theorem decoded_store_satisfied {graph refs store pairs}
    (decoded : decodeStore graph refs store = some pairs) (solved : Holds graph pairs) :
    StoreSatisfied graph refs store := by
  intro clause hc
  rcases decodeStore_member decoded clause hc with ⟨pair,hpair,found⟩
  exact ⟨pair,found,solved pair hpair⟩

def checkStore (graph : Graph) (refs : References) (certificate : Regular.Certificate) (store : Store) : Bool :=
  match decodeStore graph refs store with
  | none => false
  | some pairs => accepts graph certificate pairs

theorem checkStore_sound {graph refs certificate store}
    (checked : checkStore graph refs certificate store = true) :
    graph.Valid ∧ StoreSatisfied graph refs store := by
  cases h : decodeStore graph refs store with
  | none => simp [checkStore,h] at checked
  | some pairs =>
      have accepted : accepts graph certificate pairs = true := by simpa [checkStore,h] using checked
      exact ⟨accepted_graph_valid accepted,
        decoded_store_satisfied h (accepted_demands_sound accepted)⟩

/-- The decoded inventory may itself undergo the concrete proved constraint
history; only its terminal finite certificate is required to accept. -/
theorem history_store_sound {graph refs store pairs events ref birth last certificate}
    (decoded : decodeStore graph refs store = some pairs)
    (history : ConstraintHistory graph ref birth ⟨pairs,events⟩ last)
    (accepted : accepts graph certificate last.obligations = true) :
    graph.Valid ∧ StoreSatisfied graph refs store := by
  have original := accepted_original_demands history accepted
  exact ⟨original.1,decoded_store_satisfied decoded original.2⟩


/-- Successful function decoding preserves all four actual graph ports. -/
theorem decode_function_exact {graph refs a ae re r identity}
    (decoded : decodeTerm graph refs (.function a ae re r) = some identity) :
    ∃ a' ae' re' r', decodeTerm graph refs a = some a' ∧
      decodeTerm graph refs ae = some ae' ∧ decodeTerm graph refs re = some re' ∧
      decodeTerm graph refs r = some r' ∧
      graph.lookup .value identity = some (.function a' ae' re' r') := by
  rcases bind_some decoded with ⟨a',ha,remaining⟩
  rcases bind_some remaining with ⟨ae',hae,remaining⟩
  rcases bind_some remaining with ⟨re',hre,remaining⟩
  rcases bind_some remaining with ⟨r',hr,found⟩
  exact ⟨a',ae',re',r',ha,hae,hre,hr,findNode_sound found⟩

theorem prependRecord_exact {graph label optional field tail identity}
    (decoded : prependRecord graph label optional field tail = some identity) :
    ∃ fields, graph.lookup .value tail = some (.record fields) ∧
      graph.lookup .value identity = some (.record (⟨label,optional,field⟩ :: fields)) := by
  cases h : graph.lookup .value tail with
  | none => simp [prependRecord,h] at decoded
  | some node =>
      cases node <;> simp only [prependRecord,h] at decoded
      all_goals first | exact ⟨_,rfl,findNode_sound decoded⟩ | cases decoded

theorem prependTuple_exact {graph head tail identity}
    (decoded : prependTuple graph head tail = some identity) :
    ∃ elements, graph.lookup .value tail = some (.tuple elements) ∧
      graph.lookup .value identity = some (.tuple (head :: elements)) := by
  cases h : graph.lookup .value tail with
  | none => simp [prependTuple,h] at decoded
  | some node =>
      cases node <;> simp only [prependTuple,h] at decoded
      all_goals first | exact ⟨_,rfl,findNode_sound decoded⟩ | cases decoded

theorem prependVariant_exact {graph tag payloads tail identity}
    (decoded : prependVariant graph tag payloads tail = some identity) :
    ∃ elements alternatives,
      graph.lookup .value payloads = some (.tuple elements) ∧
      graph.lookup .value tail = some (.variant alternatives) ∧
      graph.lookup .value identity = some (.variant (⟨tag,elements⟩ :: alternatives)) := by
  cases hp : graph.lookup .value payloads with
  | none => simp [prependVariant,hp] at decoded
  | some payloadNode =>
      cases ht : graph.lookup .value tail with
      | none => cases payloadNode <;> simp [prependVariant,hp,ht] at decoded
      | some tailNode =>
          cases payloadNode <;> cases tailNode <;> simp only [prependVariant,hp,ht] at decoded
          all_goals first | exact ⟨_,_,rfl,rfl,findNode_sound decoded⟩ | cases decoded

def publicationTransport (n count : Nat) (afterUse : ScopedPublication.Flags) (q : Renaming) : Renaming :=
  Generalization.transport n count 0 (ScopedPublication.guardLevels afterUse) q

def PublishedSatisfied (graph : Graph) (refs : References) (n : Nat)
    (bounds : List ScopedPublication.Bound) (captured allocation : ScopedPublication.Flags)
    (roots : List ScopedPublication.Row) (uses : List Nat) : Prop :=
  ∀ clause, ScopedPublication.Published n bounds captured allocation roots uses clause →
    ClauseSatisfied graph refs clause

/-- The only inventory condition is syntactic coverage of target publication.
The original-clause image is DERIVED from publication_clause_image. Final
finite acceptance constructs the interpretation, and the concrete regular
history reflects it to the decoded inventory before the common pullback. -/
theorem publication_history_with_clients
    {n count bounds beforeCap afterCap beforeUse afterUse roots uses q graph refs}
    {inventory clients : Store} {pairs events ref birth last certificate}
    (bounded : ScopedPublication.BoundsBounded n bounds)
    (images : ScopedPublication.InactiveImages n beforeUse afterUse q)
    (closed : ScopedPublication.StoppedClosed (bounds.map (ScopedPublication.Bound.rename q)) afterCap)
    (stops : ∀ k i, afterCap k i = false → afterUse k i = false)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (coverage : ∀ clause,
      ScopedPublication.Published n (bounds.map (ScopedPublication.Bound.rename q)) afterCap afterUse
        (roots.map (ScopedPublication.Row.rename q)) uses clause → clause ∈ inventory)
    (decoded : decodeStore graph refs
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q))) = some pairs)
    (history : ConstraintHistory graph ref birth ⟨pairs,events⟩ last)
    (accepted : accepts graph certificate last.obligations = true) :
    graph.Valid ∧
      PublishedSatisfied graph (fun k i => refs k (publicationTransport n count afterUse q k i))
        n bounds beforeCap beforeUse roots uses ∧
      StoreSatisfied graph (fun k i => refs k (publicationTransport n count afterUse q k i)) clients := by
  have solved := history_store_sound decoded history accepted
  refine ⟨solved.1,?_,?_⟩
  · intro clause published
    apply (clause_rename graph refs (publicationTransport n count afterUse q) clause).mp
    apply solved.2
    apply List.mem_append_left
    exact coverage _ (ScopedPublication.publication_clause_image bounded images closed stops useBounds published)
  · intro clause member
    apply (clause_rename graph refs (publicationTransport n count afterUse q) clause).mp
    apply solved.2
    exact List.mem_append_right _ (List.mem_map.mpr ⟨clause,member,rfl⟩)

/-- Direct finite checking is the zero-step specialization. The inputs still
contain no satisfying valuation or semantic interpretation laws. -/
theorem checked_publication_with_clients
    {n count bounds beforeCap afterCap beforeUse afterUse roots uses q graph refs}
    {inventory clients : Store} {certificate}
    (bounded : ScopedPublication.BoundsBounded n bounds)
    (images : ScopedPublication.InactiveImages n beforeUse afterUse q)
    (closed : ScopedPublication.StoppedClosed (bounds.map (ScopedPublication.Bound.rename q)) afterCap)
    (stops : ∀ k i, afterCap k i = false → afterUse k i = false)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (coverage : ∀ clause,
      ScopedPublication.Published n (bounds.map (ScopedPublication.Bound.rename q)) afterCap afterUse
        (roots.map (ScopedPublication.Row.rename q)) uses clause → clause ∈ inventory)
    (checked : checkStore graph refs certificate
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q))) = true) :
    graph.Valid ∧
      PublishedSatisfied graph (fun k i => refs k (publicationTransport n count afterUse q k i))
        n bounds beforeCap beforeUse roots uses ∧
      StoreSatisfied graph (fun k i => refs k (publicationTransport n count afterUse q k i)) clients := by
  cases decoded : decodeStore graph refs
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q))) with
  | none => simp [checkStore,decoded] at checked
  | some pairs =>
      have accepted : accepts graph certificate pairs = true := by simpa [checkStore,decoded] using checked
      exact publication_history_with_clients (events := []) (ref := fun _ _ => False)
        (birth := fun _ => 0) bounded images closed stops useBounds coverage decoded
        (.nil ⟨pairs,[]⟩) accepted


/-! Concrete finite carrier decoding and explicit unsupported cases. -/
def carrierGraph : Graph
  | .value => [.atom 9,.record [],.record [⟨7,true,0⟩],.tuple [],.tuple [0],
      .variant [],.variant [⟨8,[0]⟩]]
  | .effect => []
def zeroReferences : References := fun _ _ => 0

def carrierRecord : Term .value := .recordCons 7 true (.atom 9) .recordNil
def carrierTuple : Term .value := .tupleCons (.atom 9) .tupleNil
def carrierVariant : Term .value := .variantCons 8 carrierTuple .variantNil

theorem carrier_record_decoded : decodeTerm carrierGraph zeroReferences carrierRecord = some 2 := rfl
theorem carrier_tuple_decoded : decodeTerm carrierGraph zeroReferences carrierTuple = some 4 := rfl
theorem carrier_variant_decoded : decodeTerm carrierGraph zeroReferences carrierVariant = some 6 := rfl

theorem optional_metadata_mismatch_rejected :
    decodeTerm carrierGraph zeroReferences (.recordCons 7 false (.atom 9) .recordNil) = none := rfl

theorem wrong_kind_reference_rejected :
    decodeTerm carrierGraph zeroReferences (Term.var (k := .effect) 0) = none := rfl

theorem missing_reference_rejected :
    decodeTerm carrierGraph (fun _ _ => 99) (Term.var (k := .value) 0) = none := rfl

theorem lattice_decoding_unsupported (graph : Graph) (refs : References) {k} (a b : Term k) :
    decodeTerm graph refs (.union a b) = none ∧
    decodeTerm graph refs (.intersection a b) = none := ⟨rfl,rfl⟩

def carrierStore : Store :=
  [⟨.value,carrierRecord,carrierRecord⟩,⟨.value,carrierTuple,carrierTuple⟩,
   ⟨.value,carrierVariant,carrierVariant⟩]
def carrierCertificate : Regular.Certificate :=
  [⟨.value,2,2⟩,⟨.value,4,4⟩,⟨.value,6,6⟩,⟨.value,0,0⟩]

theorem carrier_store_checked : checkStore carrierGraph zeroReferences carrierCertificate carrierStore = true := rfl

theorem carrier_store_regular : carrierGraph.Valid ∧ StoreSatisfied carrierGraph zeroReferences carrierStore :=
  checkStore_sound carrier_store_checked

/-! Two fresh uses share an unchanged lower-level anchor. A quotient lowers
both use images to that anchor. The decoded semantic graph is genuinely cyclic:
its Function argument and result refer back to the Function itself. Both effect
ports resolve in the separate effect table. -/
def cyclicGraph : Graph
  | .value => [.function 0 0 0 0]
  | .effect => [.atom 17]
def cyclicCertificate : Regular.Certificate := [⟨.value,0,0⟩,⟨.effect,0,0⟩]
def cyclicBound : ScopedPublication.Bound :=
  ⟨.value,1,.positive,.function (.var 0) (.var 0) (.var 0) (.var 0)⟩
def beforeFlags : ScopedPublication.Flags := fun _ i => decide (i = 1)
def afterFlags : ScopedPublication.Flags := fun _ _ => false
def anchorQuotient : Renaming := fun _ _ => 0
def cyclicRoots : List ScopedPublication.Row := [⟨.value,1⟩]
def cyclicInventory : Store := [(cyclicBound.rename anchorQuotient).clause]
def cyclicClients : Store := [⟨.value,.var 3,.var 5⟩]
def pulledReferences : References :=
  fun k i => zeroReferences k (publicationTransport 2 2 afterFlags anchorQuotient k i)
def cyclicPairs : List Comparison := [⟨.value,0,0⟩,⟨.value,0,0⟩]
def cyclicTerminal : ConstraintState :=
  ⟨[⟨.value,0,0⟩,⟨.effect,0,0⟩,⟨.effect,0,0⟩,⟨.value,0,0⟩,⟨.value,0,0⟩],[]⟩

theorem cyclic_inventory_coverage : ∀ clause,
    ScopedPublication.Published 2 ([cyclicBound].map (ScopedPublication.Bound.rename anchorQuotient))
      afterFlags afterFlags (cyclicRoots.map (ScopedPublication.Row.rename anchorQuotient)) [0,1] clause →
    clause ∈ cyclicInventory := by
  intro clause published
  cases published with
  | base bound member =>
      have same : bound = cyclicBound.rename anchorQuotient := by simpa using member
      subst bound
      exact List.mem_cons_self
  | copy bound member use hu reach active =>
      change false = true at active
      cases active

theorem cyclic_inventory_decoded : decodeStore cyclicGraph zeroReferences
    (cyclicInventory ++ cyclicClients.map (Constraint.rename (publicationTransport 2 2 afterFlags anchorQuotient))) =
      some cyclicPairs := rfl

theorem cyclic_inventory_history : ConstraintHistory cyclicGraph
    (fun _ _ => False) (fun _ => 0) ⟨cyclicPairs,[]⟩ cyclicTerminal :=
  .cons (.decompose ⟨.value,0,0⟩
    [⟨.value,0,0⟩,⟨.effect,0,0⟩,⟨.effect,0,0⟩,⟨.value,0,0⟩] [⟨.value,0,0⟩] [] rfl) (.nil _)

theorem cyclic_terminal_accepted : accepts cyclicGraph cyclicCertificate cyclicTerminal.obligations = true := rfl

/-- Complete executable-decoder → actual structural history → finite regular
certificate → original scoped publication and client constraints example. -/
theorem cyclic_publication_and_clients : cyclicGraph.Valid ∧
    PublishedSatisfied cyclicGraph pulledReferences 2 [cyclicBound] beforeFlags beforeFlags cyclicRoots [0,1] ∧
    StoreSatisfied cyclicGraph pulledReferences cyclicClients := by
  apply publication_history_with_clients (n := 2) (count := 2) (bounds := [cyclicBound])
    (beforeCap := beforeFlags) (afterCap := afterFlags) (beforeUse := beforeFlags) (afterUse := afterFlags)
    (roots := cyclicRoots) (uses := [0,1]) (q := anchorQuotient)
    (graph := cyclicGraph) (refs := zeroReferences) (inventory := cyclicInventory) (clients := cyclicClients)
    (pairs := cyclicPairs) (events := []) (ref := fun _ _ => False) (birth := fun _ => 0)
    (last := cyclicTerminal) (certificate := cyclicCertificate)
  · intro bound member
    have same : bound = cyclicBound := by simpa using member
    subst bound
    simp [cyclicBound,Generalization.Bounded]
  · exact fun _ _ _ _ => rfl
  · exact fun _ _ _ _ _ => rfl
  · exact fun _ _ _ => rfl
  · intro use member
    simp at member
    omega
  · exact cyclic_inventory_coverage
  · exact cyclic_inventory_decoded
  · exact cyclic_inventory_history
  · exact cyclic_terminal_accepted

theorem two_distinct_uses_one_shared_anchor :
    ScopedPublication.fresh 2 beforeFlags 0 .value 1 = 3 ∧
    ScopedPublication.fresh 2 beforeFlags 1 .value 1 = 5 ∧
    ScopedPublication.fresh 2 beforeFlags 0 .value 0 = 0 ∧
    ScopedPublication.fresh 2 beforeFlags 1 .value 0 = 0 ∧
    publicationTransport 2 2 afterFlags anchorQuotient .value 3 = 0 ∧
    publicationTransport 2 2 afterFlags anchorQuotient .value 5 = 0 ∧
    publicationTransport 2 2 afterFlags anchorQuotient .value 6 = 6 := by decide

/-- Both original use clauses and the later cross-use client hold under the
same pulled-back reference assignment; no witness is chosen per use. -/
theorem cyclic_two_uses_and_client :
    ClauseSatisfied cyclicGraph pulledReferences
      (cyclicBound.clause.rename (ScopedPublication.fresh 2 beforeFlags 0)) ∧
    ClauseSatisfied cyclicGraph pulledReferences
      (cyclicBound.clause.rename (ScopedPublication.fresh 2 beforeFlags 1)) ∧
    ClauseSatisfied cyclicGraph pulledReferences ⟨.value,.var 3,.var 5⟩ := by
  have all := cyclic_publication_and_clients
  refine ⟨all.2.1 _ ?_,all.2.1 _ ?_,all.2.2 _ List.mem_cons_self⟩
  · exact .copy cyclicBound List.mem_cons_self 0 (by simp)
      (.root _ List.mem_cons_self) rfl
  · exact .copy cyclicBound List.mem_cons_self 1 (by simp)
      (.root _ List.mem_cons_self) rfl

end YulangClosure.SimpleSub.RegularPublication
