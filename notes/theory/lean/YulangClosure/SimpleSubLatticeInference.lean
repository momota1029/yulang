import YulangClosure.SimpleSubLatticeCertificates
import YulangClosure.SimpleSubRegularPublication

/-!
Consume finite lattice certificates through the existing Term, Store and
scoped-publication syntax. Decoding includes union and intersection and retains
all four Function ports and exact finite row/payload shape. The new histories
are indexed by Lattice.Graph; no old Regular.Graph history is cast or assumed.

This is proof-side construction. Native graph/trace/certificate extraction,
source formation of the concrete legality premises, ordinary coalescing, and
original Call/effect correspondence remain separate obligations. Publication guards
are retained exactly; no semantic preservation law or final model is supplied.
-/
namespace YulangClosure.SimpleSub.LatticeInference
open Lattice
open Regular (Comparison Field Alternative lookupList copyLink copyEqualities ConstraintState)
open RegularPublication (bind_some)

abbrev References := RegularPublication.References

deriving instance DecidableEq for Lattice.Node

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
      · simp only [findList,same,↓reduceIte,Option.some.injEq] at found
        subst index
        simp [lookupList,same]
      · simp only [findList,same,↓reduceIte] at found
        cases ht : findList wanted tail with
        | none => simp [ht] at found
        | some n =>
            simp only [ht,Option.map_some,Option.some.injEq] at found
            subst index
            exact ih ht

theorem findNode_sound {graph : Graph} {k} {wanted : Node k} {index : Nat}
    (found : findNode graph wanted = some index) : graph.lookup k index = some wanted :=
  findList_sound found

def checkedReference (graph : Graph) (k : Kind) (index : Nat) : Option Nat :=
  match graph.lookup k index with
  | some _ => some index
  | none => none

/-- Rows are finite structural lists. A lattice node cannot masquerade as a
row tail or a payload spine. -/
def prependRecord (graph : Graph) (label : Nat) (optional : Bool) (field tail : Nat) : Option Nat :=
  match graph.lookup .value tail with
  | some (.structural (.record fields)) =>
      findNode graph (.structural (.record (⟨label,optional,field⟩ :: fields)))
  | _ => none

def prependTuple (graph : Graph) (head tail : Nat) : Option Nat :=
  match graph.lookup .value tail with
  | some (.structural (.tuple elements)) => findNode graph (.structural (.tuple (head :: elements)))
  | _ => none

def prependVariant (graph : Graph) (tag payloads tail : Nat) : Option Nat :=
  match graph.lookup .value payloads, graph.lookup .value tail with
  | some (.structural (.tuple elements)), some (.structural (.variant alternatives)) =>
      findNode graph (.structural (.variant (⟨tag,elements⟩ :: alternatives)))
  | _, _ => none

/-- The actual existing Term syntax is decoded, including both lattice cases.
Success always returns an existing exact constructor in the one shared graph. -/
def decodeTerm (graph : Graph) (refs : References) : {k : Kind} → Term k → Option Nat
  | k, .var identity => checkedReference graph k (refs k identity)
  | k, .atom identity => findNode graph (k := k) (.structural (.atom identity))
  | k, .bottom => findNode graph (k := k) (.structural .bottom)
  | k, .top => findNode graph (k := k) (.structural .top)
  | k, .union left right => do
      let left' ← decodeTerm graph refs left
      let right' ← decodeTerm graph refs right
      findNode graph (k := k) (.union left' right')
  | k, .intersection left right => do
      let left' ← decodeTerm graph refs left
      let right' ← decodeTerm graph refs right
      findNode graph (k := k) (.intersection left' right')
  | .value, .function a ae re r => do
      let a' ← decodeTerm graph refs a
      let ae' ← decodeTerm graph refs ae
      let re' ← decodeTerm graph refs re
      let r' ← decodeTerm graph refs r
      findNode graph (.structural (.function a' ae' re' r'))
  | .value, .recordNil => findNode graph (.structural (.record []))
  | .value, .recordCons label optional field tail => do
      let field' ← decodeTerm graph refs field
      let tail' ← decodeTerm graph refs tail
      prependRecord graph label optional field' tail'
  | .value, .tupleNil => findNode graph (.structural (.tuple []))
  | .value, .tupleCons head tail => do
      let head' ← decodeTerm graph refs head
      let tail' ← decodeTerm graph refs tail
      prependTuple graph head' tail'
  | .value, .variantNil => findNode graph (.structural (.variant []))
  | .value, .variantCons tag payloads tail => do
      let payloads' ← decodeTerm graph refs payloads
      let tail' ← decodeTerm graph refs tail
      prependVariant graph tag payloads' tail'

theorem decodeTerm_rename (graph : Graph) (refs : References) (q : Renaming)
    {k} (term : Term k) :
    decodeTerm graph refs (term.rename q) =
      decodeTerm graph (fun k i => refs k (q k i)) term := by
  induction term <;> simp_all [Term.rename,Term.subst,decodeTerm]

theorem decodeTerm_congr_bounded {n graph refs refs' k} {term : Term k}
    (bounded : Generalization.Bounded n term)
    (same : ∀ k i, i < n → refs k i = refs' k i) :
    decodeTerm graph refs term = decodeTerm graph refs' term := by
  induction term <;> simp_all [Generalization.Bounded,decodeTerm]

/-- One commuting reference assignment handles every source variable,
including lattice children and all four Function ports. -/
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
  ∀ identity, result = some identity → Exists graph k identity

theorem found_none (graph : Graph) (k : Kind) : Found graph k none := by
  intro identity h
  cases h

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
  | some node => cases node with
    | union _ _ | intersection _ _ => simp [prependRecord,h,Found]
    | structural node => cases node <;> simp only [prependRecord,h] <;>
        first | exact found_none _ _ | exact found_findNode _ _

theorem prependTuple_found (graph : Graph) (head tail : Nat) :
    Found graph .value (prependTuple graph head tail) := by
  cases h : graph.lookup .value tail with
  | none => simp [prependTuple,h,Found]
  | some node => cases node with
    | union _ _ | intersection _ _ => simp [prependTuple,h,Found]
    | structural node => cases node <;> simp only [prependTuple,h] <;>
        first | exact found_none _ _ | exact found_findNode _ _

theorem prependVariant_found (graph : Graph) (tag payloads tail : Nat) :
    Found graph .value (prependVariant graph tag payloads tail) := by
  cases hp : graph.lookup .value payloads with
  | none => simp [prependVariant,hp,Found]
  | some payloadNode =>
      cases payloadNode with
      | union _ _ | intersection _ _ => simp [prependVariant,hp,Found]
      | structural payloadNode =>
          cases ht : graph.lookup .value tail with
          | none => cases payloadNode <;> simp [prependVariant,hp,ht,Found]
          | some tailNode => cases tailNode with
            | union _ _ | intersection _ _ => cases payloadNode <;> simp [prependVariant,hp,ht,Found]
            | structural tailNode => cases payloadNode <;> cases tailNode <;>
                simp only [prependVariant,hp,ht] <;>
                first | exact found_none _ _ | exact found_findNode _ _

theorem decodeTerm_found (graph : Graph) (refs : References) {k} (term : Term k) :
    Found graph k (decodeTerm graph refs term) := by
  cases term with
  | var identity => exact checkedReference_found _ _ _
  | atom identity => exact found_findNode _ _
  | bottom => exact found_findNode _ _
  | top => exact found_findNode _ _
  | union left right | intersection left right =>
      apply found_bind; intro left'
      apply found_bind; intro right'
      exact found_findNode _ _
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

theorem decode_union_exact {graph refs k} {left right : Term k} {identity}
    (decoded : decodeTerm graph refs (.union left right) = some identity) :
    ∃ l r, decodeTerm graph refs left = some l ∧ decodeTerm graph refs right = some r ∧
      graph.lookup k identity = some (.union l r) := by
  rcases bind_some decoded with ⟨l,hl,remaining⟩
  rcases bind_some remaining with ⟨r,hr,found⟩
  exact ⟨l,r,hl,hr,findNode_sound found⟩

theorem decode_intersection_exact {graph refs k} {left right : Term k} {identity}
    (decoded : decodeTerm graph refs (.intersection left right) = some identity) :
    ∃ l r, decodeTerm graph refs left = some l ∧ decodeTerm graph refs right = some r ∧
      graph.lookup k identity = some (.intersection l r) := by
  rcases bind_some decoded with ⟨l,hl,remaining⟩
  rcases bind_some remaining with ⟨r,hr,found⟩
  exact ⟨l,r,hl,hr,findNode_sound found⟩

theorem decode_function_exact {graph refs a ae re r identity}
    (decoded : decodeTerm graph refs (.function a ae re r) = some identity) :
    ∃ a' ae' re' r', decodeTerm graph refs a = some a' ∧
      decodeTerm graph refs ae = some ae' ∧ decodeTerm graph refs re = some re' ∧
      decodeTerm graph refs r = some r' ∧
      graph.lookup .value identity = some (.structural (.function a' ae' re' r')) := by
  rcases bind_some decoded with ⟨a',ha,remaining⟩
  rcases bind_some remaining with ⟨ae',hae,remaining⟩
  rcases bind_some remaining with ⟨re',hre,remaining⟩
  rcases bind_some remaining with ⟨r',hr,found⟩
  exact ⟨a',ae',re',r',ha,hae,hre,hr,findNode_sound found⟩

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

/-- Semantic satisfaction is independent of finite certificate acceptance. -/
def ClauseSatisfied (graph : Graph) (refs : References) (clause : Constraint) : Prop :=
  ∃ pair, decodeConstraint graph refs clause = some pair ∧ RegularSub graph pair

def StoreSatisfied (graph : Graph) (refs : References) (store : Store) : Prop :=
  ∀ clause, clause ∈ store → ClauseSatisfied graph refs clause

def Holds (graph : Graph) (demands : List Comparison) : Prop :=
  ∀ pair, pair ∈ demands → RegularSub graph pair

theorem decodeConstraint_rename (graph : Graph) (refs : References) (q : Renaming)
    (clause : Constraint) :
    decodeConstraint graph refs (clause.rename q) =
      decodeConstraint graph (fun k i => refs k (q k i)) clause := by
  simp [decodeConstraint,Constraint.rename,decodeTerm_rename]

theorem clause_rename (graph : Graph) (refs : References) (q : Renaming) (clause : Constraint) :
    ClauseSatisfied graph refs (clause.rename q) ↔
      ClauseSatisfied graph (fun k i => refs k (q k i)) clause := by
  simp only [ClauseSatisfied,decodeConstraint_rename]

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

def checkStore (graph : Graph) (refs : References) (certificate : Lattice.Certificate) (store : Store) : Bool :=
  match decodeStore graph refs store with
  | none => false
  | some pairs => accepts graph certificate pairs

theorem checkStore_sound {graph refs certificate store}
    (checked : checkStore graph refs certificate store = true) :
    graph.Valid ∧ graph.Guarded ∧ StoreSatisfied graph refs store := by
  cases h : decodeStore graph refs store with
  | none => simp [checkStore,h] at checked
  | some pairs =>
      have accepted : accepts graph certificate pairs = true := by simpa [checkStore,h] using checked
      have solved := accepts_sound accepted
      exact ⟨solved.1,solved.2.1,decoded_store_satisfied h solved.2.2⟩

abbrev publicationTransport := RegularPublication.publicationTransport

def PublishedSatisfied (graph : Graph) (refs : References) (n : Nat)
    (bounds : List ScopedPublication.Bound) (captured allocation : ScopedPublication.Flags)
    (roots : List ScopedPublication.Row) (uses : List Nat) : Prop :=
  ∀ clause, ScopedPublication.Published n bounds captured allocation roots uses clause →
    ClauseSatisfied graph refs clause

/-- The actual existing scoped publication theorem supplies clause images.
Decoder success is checked by checkStore; the original guard hypotheses remain. -/
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
    graph.Valid ∧ graph.Guarded ∧
      PublishedSatisfied graph (fun k i => refs k (publicationTransport n count afterUse q k i))
        n bounds beforeCap beforeUse roots uses ∧
      StoreSatisfied graph (fun k i => refs k (publicationTransport n count afterUse q k i)) clients := by
  have solved := checkStore_sound checked
  refine ⟨solved.1,solved.2.1,?_,?_⟩
  · intro clause published
    apply (clause_rename graph refs (publicationTransport n count afterUse q) clause).mp
    apply solved.2.2
    apply List.mem_append_left
    exact coverage _ (ScopedPublication.publication_clause_image bounded images closed stops useBounds published)
  · intro clause member
    apply (clause_rename graph refs (publicationTransport n count afterUse q) clause).mp
    apply solved.2.2
    exact List.mem_append_right _ (List.mem_map.mpr ⟨clause,member,rfl⟩)

/-! New histories use the actual extended graph. Only graph-free coordinates,
occurrences, and state lists are shared with the existing history language. -/

@[simp] theorem holds_cons (graph : Graph) (pair : Comparison) (rest : List Comparison) :
    Holds graph (pair :: rest) ↔ RegularSub graph pair ∧ Holds graph rest := by
  simp [Holds]

@[simp] theorem holds_append (graph : Graph) (left right : List Comparison) :
    Holds graph (left ++ right) ↔ Holds graph left ∧ Holds graph right := by
  simp [Holds,List.mem_append,or_imp,forall_and]

theorem regular_unionElim {graph : Graph} {k u a b c}
    (found : unionAt graph k u = some (a,b))
    (left : RegularSub graph ⟨k,a,c⟩) (right : RegularSub graph ⟨k,b,c⟩) :
    RegularSub graph ⟨k,u,c⟩ := by
  intro depth
  cases depth with
  | zero => trivial
  | succ depth => exact .unionElim found (left (depth + 1)) (right (depth + 1))

theorem regular_intersectionIntro {graph : Graph} {k u a b c}
    (found : intersectionAt graph k u = some (a,b))
    (left : RegularSub graph ⟨k,c,a⟩) (right : RegularSub graph ⟨k,c,b⟩) :
    RegularSub graph ⟨k,c,u⟩ := by
  intro depth
  cases depth with
  | zero => trivial
  | succ depth => exact .intersectionIntro found (left (depth + 1)) (right (depth + 1))

theorem regular_unionMono {graph : Graph} {k u v a b c d}
    (lower : unionAt graph k u = some (a,b)) (upper : unionAt graph k v = some (c,d))
    (left : RegularSub graph ⟨k,a,c⟩) (right : RegularSub graph ⟨k,b,d⟩) :
    RegularSub graph ⟨k,u,v⟩ := by
  intro depth
  cases depth with
  | zero => trivial
  | succ depth => exact .unionMono lower upper (left (depth + 1)) (right (depth + 1))

theorem regular_intersectionMono {graph : Graph} {k u v a b c d}
    (lower : intersectionAt graph k u = some (a,b))
    (upper : intersectionAt graph k v = some (c,d))
    (left : RegularSub graph ⟨k,a,c⟩) (right : RegularSub graph ⟨k,b,d⟩) :
    RegularSub graph ⟨k,u,v⟩ := by
  intro depth
  cases depth with
  | zero => trivial
  | succ depth => exact .intersectionMono lower upper (left (depth + 1)) (right (depth + 1))

inductive Extrusion (graph : Graph) : Comparison → List Copy → Prop where
  | copy (coordinate : Copy) : Extrusion graph (copyLink coordinate) [coordinate]
  | same (k : Kind) (identity : Nat) (present : Exists graph k identity) :
      Extrusion graph ⟨k,identity,identity⟩ []
  | structural (pair : Comparison) (parts : List (Comparison × List Copy))
      (expanded : structuralExpand graph pair = some (parts.map Prod.fst))
      (children : ∀ part, part ∈ parts → Extrusion graph part.1 part.2) :
      Extrusion graph pair (parts.flatMap Prod.snd)
  | union {k u v a b c d leftCopies rightCopies}
      (lower : unionAt graph k u = some (a,b)) (upper : unionAt graph k v = some (c,d))
      (left : Extrusion graph ⟨k,a,c⟩ leftCopies)
      (right : Extrusion graph ⟨k,b,d⟩ rightCopies) :
      Extrusion graph ⟨k,u,v⟩ (leftCopies ++ rightCopies)
  | intersection {k u v a b c d leftCopies rightCopies}
      (lower : intersectionAt graph k u = some (a,b))
      (upper : intersectionAt graph k v = some (c,d))
      (left : Extrusion graph ⟨k,a,c⟩ leftCopies)
      (right : Extrusion graph ⟨k,b,d⟩ rightCopies) :
      Extrusion graph ⟨k,u,v⟩ (leftCopies ++ rightCopies)

theorem Extrusion.sound {graph : Graph} {pair : Comparison} {copies : List Copy}
    (trace : Extrusion graph pair copies) (links : Holds graph (copies.map copyLink)) :
    RegularSub graph pair := by
  induction trace with
  | copy coordinate => exact (holds_cons _ _ _).mp links |>.1
  | same k identity present => exact regular_refl present
  | structural pair parts expanded children ih =>
      apply regular_structural expanded
      intro child hc
      rcases List.mem_map.mp hc with ⟨part,hpart,rfl⟩
      apply ih part hpart
      intro link hlink
      rcases List.mem_map.mp hlink with ⟨copy,hcopy,rfl⟩
      apply links
      exact List.mem_map.mpr ⟨copy,List.mem_flatMap.mpr ⟨part,hpart,hcopy⟩,rfl⟩
  | union lower upper left right ih₁ ih₂ =>
      simp only [List.map_append,holds_append] at links
      exact regular_unionMono lower upper (ih₁ links.1) (ih₂ links.2)
  | intersection lower upper left right ih₁ ih₂ =>
      simp only [List.map_append,holds_append] at links
      exact regular_intersectionMono lower upper (ih₁ links.1) (ih₂ links.2)

def StateSatisfied (graph : Graph) (state : ConstraintState) : Prop := Holds graph state.obligations

/-- Every operation has only syntactic lookup, traversal, or actual retained
occurrence premises. Backward semantic reflection is derived below. -/
inductive ConstraintStep (graph : Graph) (ref : Nat → Nat → Prop) (birth : Nat → Nat) :
    ConstraintState → ConstraintState → Prop where
  | reflexive (k : Kind) (identity : Nat) (rest : List Comparison) (events : List Occurrence)
      (present : Exists graph k identity) :
      ConstraintStep graph ref birth ⟨⟨k,identity,identity⟩ :: rest,events⟩ ⟨rest,events⟩
  | decompose (pair : Comparison) (children rest : List Comparison) (events : List Occurrence)
      (expanded : structuralExpand graph pair = some children) :
      ConstraintStep graph ref birth ⟨pair :: rest,events⟩ ⟨children ++ rest,events⟩
  | union (k : Kind) (u a b upper : Nat) (rest : List Comparison) (events : List Occurrence)
      (found : unionAt graph k u = some (a,b)) :
      ConstraintStep graph ref birth ⟨⟨k,u,upper⟩ :: rest,events⟩
        ⟨⟨k,a,upper⟩ :: ⟨k,b,upper⟩ :: rest,events⟩
  | intersection (k : Kind) (lower u a b : Nat) (rest : List Comparison) (events : List Occurrence)
      (found : intersectionAt graph k u = some (a,b)) :
      ConstraintStep graph ref birth ⟨⟨k,lower,u⟩ :: rest,events⟩
        ⟨⟨k,lower,a⟩ :: ⟨k,lower,b⟩ :: rest,events⟩
  | insertLower (k : Kind) (lower row : Nat) (state : ConstraintState) :
      ConstraintStep graph ref birth state ⟨⟨k,lower,row⟩ :: state.obligations,state.occurrences⟩
  | insertUpper (k : Kind) (row upper : Nat) (state : ConstraintState) :
      ConstraintStep graph ref birth state ⟨⟨k,row,upper⟩ :: state.obligations,state.occurrences⟩
  | replay (k : Kind) (lower row upper : Nat) (rest : List Comparison) (events : List Occurrence)
      (lowerBound : Comparison.mk k lower row ∈ rest)
      (upperBound : Comparison.mk k row upper ∈ rest) :
      ConstraintStep graph ref birth ⟨⟨k,lower,upper⟩ :: rest,events⟩ ⟨rest,events⟩
  | extrudeUpper (k : Kind) (lower upper fresh : Nat) (copies : List Copy)
      (rest : List Comparison) (events : List Occurrence) (identity origin receiver : Nat)
      (traversal : Extrusion graph ⟨k,fresh,upper⟩ copies) :
      ConstraintStep graph ref birth ⟨⟨k,lower,upper⟩ :: rest,events⟩
        ⟨copies.map copyLink ++ ⟨k,lower,fresh⟩ :: rest,
          ⟨identity,origin,receiver,copies⟩ :: events⟩
  | extrudeLower (k : Kind) (lower fresh upper : Nat) (copies : List Copy)
      (rest : List Comparison) (events : List Occurrence) (identity origin receiver : Nat)
      (traversal : Extrusion graph ⟨k,lower,fresh⟩ copies) :
      ConstraintStep graph ref birth ⟨⟨k,lower,upper⟩ :: rest,events⟩
        ⟨copies.map copyLink ++ ⟨k,fresh,upper⟩ :: rest,
          ⟨identity,origin,receiver,copies⟩ :: events⟩
  | intrude (state : ConstraintState) (event : Occurrence) (selected : List Copy)
      (retained : event ∈ state.occurrences) (qualifies : event.Qualifies ref birth)
      (actual : ∀ copy, copy ∈ selected → copy ∈ event.copies) :
      ConstraintStep graph ref birth state
        ⟨selected.flatMap copyEqualities ++ state.obligations,state.occurrences⟩

theorem ConstraintStep.sound {graph : Graph} {ref : Nat → Nat → Prop} {birth : Nat → Nat}
    {before after : ConstraintState} (step : ConstraintStep graph ref birth before after)
    (solved : StateSatisfied graph after) : StateSatisfied graph before := by
  cases step <;> simp only [StateSatisfied,holds_cons,holds_append] at solved ⊢
  case reflexive present => exact ⟨regular_refl present,solved⟩
  case decompose expanded => exact ⟨regular_structural expanded solved.1,solved.2⟩
  case union found => exact ⟨regular_unionElim found solved.1 solved.2.1,solved.2.2⟩
  case intersection found => exact ⟨regular_intersectionIntro found solved.1 solved.2.1,solved.2.2⟩
  case insertLower => exact solved.2
  case insertUpper => exact solved.2
  case replay lowerBound upperBound =>
    exact ⟨regular_trans (solved _ lowerBound) (solved _ upperBound),solved⟩
  case extrudeUpper traversal => exact ⟨regular_trans solved.2.1 (traversal.sound solved.1),solved.2.2⟩
  case extrudeLower traversal => exact ⟨regular_trans (traversal.sound solved.1) solved.2.1,solved.2.2⟩
  case intrude => exact solved.2

theorem ConstraintStep.retains_occurrences {graph : Graph} {ref : Nat → Nat → Prop}
    {birth : Nat → Nat} {before after : ConstraintState}
    (step : ConstraintStep graph ref birth before after) :
    ∀ event, event ∈ before.occurrences → event ∈ after.occurrences := by
  cases step <;> intro event retained <;> first | exact retained | exact List.mem_cons_of_mem _ retained

inductive ConstraintHistory (graph : Graph) (ref : Nat → Nat → Prop) (birth : Nat → Nat) :
    ConstraintState → ConstraintState → Prop where
  | nil (state) : ConstraintHistory graph ref birth state state
  | cons {first middle last} (step : ConstraintStep graph ref birth first middle)
      (tail : ConstraintHistory graph ref birth middle last) : ConstraintHistory graph ref birth first last

theorem ConstraintHistory.sound {graph : Graph} {ref : Nat → Nat → Prop} {birth : Nat → Nat}
    {first last : ConstraintState} (history : ConstraintHistory graph ref birth first last)
    (solved : StateSatisfied graph last) : StateSatisfied graph first := by
  induction history with
  | nil => exact solved
  | cons step tail ih => exact step.sound (ih solved)

theorem ConstraintHistory.retains_occurrences {graph : Graph} {ref : Nat → Nat → Prop}
    {birth : Nat → Nat} {first last : ConstraintState}
    (history : ConstraintHistory graph ref birth first last) :
    ∀ event, event ∈ first.occurrences → event ∈ last.occurrences := by
  induction history with
  | nil => exact fun _ h => h
  | cons step tail ih => exact fun event h => ih event (step.retains_occurrences event h)

theorem accepted_original_demands {graph : Graph} {ref : Nat → Nat → Prop} {birth : Nat → Nat}
    {first last : ConstraintState} {certificate : Lattice.Certificate}
    (history : ConstraintHistory graph ref birth first last)
    (accepted : accepts graph certificate last.obligations = true) :
    graph.Valid ∧ graph.Guarded ∧ StateSatisfied graph first := by
  have solved := accepts_sound accepted
  exact ⟨solved.1,solved.2.1,history.sound solved.2.2⟩

theorem history_store_sound {graph refs store pairs events ref birth last certificate}
    (decoded : decodeStore graph refs store = some pairs)
    (history : ConstraintHistory graph ref birth ⟨pairs,events⟩ last)
    (accepted : accepts graph certificate last.obligations = true) :
    graph.Valid ∧ graph.Guarded ∧ StoreSatisfied graph refs store := by
  have original := accepted_original_demands history accepted
  exact ⟨original.1,original.2.1,decoded_store_satisfied decoded original.2.2⟩

/-- Apply the same original scoped-publication image theorem after concrete
lattice-aware histories. One final graph and reference assignment serve all uses. -/
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
    graph.Valid ∧ graph.Guarded ∧
      PublishedSatisfied graph (fun k i => refs k (publicationTransport n count afterUse q k i))
        n bounds beforeCap beforeUse roots uses ∧
      StoreSatisfied graph (fun k i => refs k (publicationTransport n count afterUse q k i)) clients := by
  have solved := history_store_sound decoded history accepted
  refine ⟨solved.1,solved.2.1,?_,?_⟩
  · intro clause published
    apply (clause_rename graph refs (publicationTransport n count afterUse q) clause).mp
    apply solved.2.2
    apply List.mem_append_left
    exact coverage _ (ScopedPublication.publication_clause_image bounded images closed stops useBounds published)
  · intro clause member
    apply (clause_rename graph refs (publicationTransport n count afterUse q) clause).mp
    apply solved.2.2
    exact List.mem_append_right _ (List.mem_map.mpr ⟨clause,member,rfl⟩)

/-- Successful row decoding exposes the original optional bit and exact tail. -/
theorem prependRecord_exact {graph label optional field tail identity}
    (decoded : prependRecord graph label optional field tail = some identity) :
    ∃ fields, graph.lookup .value tail = some (.structural (.record fields)) ∧
      graph.lookup .value identity = some (.structural (.record (⟨label,optional,field⟩ :: fields))) := by
  cases h : graph.lookup .value tail with
  | none => simp [prependRecord,h] at decoded
  | some node => cases node with
    | union _ _ | intersection _ _ => simp [prependRecord,h] at decoded
    | structural node =>
        cases node <;> simp only [prependRecord,h] at decoded
        all_goals first | exact ⟨_,rfl,findNode_sound decoded⟩ | cases decoded

theorem prependTuple_exact {graph head tail identity}
    (decoded : prependTuple graph head tail = some identity) :
    ∃ elements, graph.lookup .value tail = some (.structural (.tuple elements)) ∧
      graph.lookup .value identity = some (.structural (.tuple (head :: elements))) := by
  cases h : graph.lookup .value tail with
  | none => simp [prependTuple,h] at decoded
  | some node => cases node with
    | union _ _ | intersection _ _ => simp [prependTuple,h] at decoded
    | structural node =>
        cases node <;> simp only [prependTuple,h] at decoded
        all_goals first | exact ⟨_,rfl,findNode_sound decoded⟩ | cases decoded

theorem prependVariant_exact {graph tag payloads tail identity}
    (decoded : prependVariant graph tag payloads tail = some identity) :
    ∃ elements alternatives,
      graph.lookup .value payloads = some (.structural (.tuple elements)) ∧
      graph.lookup .value tail = some (.structural (.variant alternatives)) ∧
      graph.lookup .value identity = some (.structural (.variant (⟨tag,elements⟩ :: alternatives))) := by
  cases hp : graph.lookup .value payloads with
  | none => simp [prependVariant,hp] at decoded
  | some payloadNode => cases payloadNode with
    | union _ _ | intersection _ _ => simp [prependVariant,hp] at decoded
    | structural payloadNode =>
        cases ht : graph.lookup .value tail with
        | none => cases payloadNode <;> simp [prependVariant,hp,ht] at decoded
        | some tailNode => cases tailNode with
          | union _ _ | intersection _ _ => cases payloadNode <;> simp [prependVariant,hp,ht] at decoded
          | structural tailNode =>
              cases payloadNode <;> cases tailNode <;> simp only [prependVariant,hp,ht] at decoded
              all_goals first | exact ⟨_,_,rfl,rfl,findNode_sound decoded⟩ | cases decoded

/-- The graph-free coordinates and states are unchanged. This theorem proves
an actual translation of every old extrusion constructor into the new graph. -/
theorem ofRegular_present {graph : Regular.Graph} {k i}
    (present : Regular.Reference.Exists graph ⟨k,i⟩) : Exists (ofRegular graph) k i := by
  rcases present with ⟨node,found⟩
  exact ⟨.structural node,by simp [ofRegular_lookup,found]⟩

theorem ofRegular_extrusion {graph : Regular.Graph} {pair copies}
    (trace : Regular.Extrusion graph pair copies) : Extrusion (ofRegular graph) pair copies := by
  induction trace with
  | copy coordinate => exact .copy coordinate
  | same k identity present => exact .same k identity (ofRegular_present present)
  | structural pair parts expanded children ih =>
      exact .structural pair parts (by simpa only [ofRegular_expansion] using expanded) ih

theorem ofRegular_step {graph : Regular.Graph} {ref birth first last}
    (step : Regular.ConstraintStep graph ref birth first last) :
    ConstraintStep (ofRegular graph) ref birth first last := by
  cases step with
  | reflexive k identity rest events present => exact .reflexive k identity rest events (ofRegular_present present)
  | decompose pair children rest events expanded =>
      exact .decompose pair children rest events (by simpa only [ofRegular_expansion] using expanded)
  | insertLower k lower row state => exact .insertLower k lower row _
  | insertUpper k row upper state => exact .insertUpper k row upper _
  | replay k lower row upper rest events hl hu => exact .replay k lower row upper rest events hl hu
  | extrudeUpper k lower upper fresh copies rest events identity origin receiver traversal =>
      exact .extrudeUpper k lower upper fresh copies rest events identity origin receiver
        (ofRegular_extrusion traversal)
  | extrudeLower k lower fresh upper copies rest events identity origin receiver traversal =>
      exact .extrudeLower k lower fresh upper copies rest events identity origin receiver
        (ofRegular_extrusion traversal)
  | intrude state event selected retained qualifies actual =>
      exact .intrude _ event selected retained qualifies actual

theorem ofRegular_history {graph : Regular.Graph} {ref birth first last}
    (history : Regular.ConstraintHistory graph ref birth first last) :
    ConstraintHistory (ofRegular graph) ref birth first last := by
  induction history with
  | nil state => exact .nil state
  | cons step tail ih => exact .cons (ofRegular_step step) ih

/-- The retained occurrence's actual selected equalities are reconstructed
from the terminal certificate along the subsequent concrete history. -/
theorem accepted_intrusion_equalities {graph : Graph} {ref : Nat → Nat → Prop} {birth : Nat → Nat}
    {state last : ConstraintState} {event : Occurrence} {selected : List Copy} {certificate : Lattice.Certificate}
    (retained : event ∈ state.occurrences) (qualifies : event.Qualifies ref birth)
    (actual : ∀ copy, copy ∈ selected → copy ∈ event.copies)
    (history : ConstraintHistory graph ref birth
      ⟨selected.flatMap copyEqualities ++ state.obligations,state.occurrences⟩ last)
    (accepted : accepts graph certificate last.obligations = true) :
    StateSatisfied graph state ∧ Holds graph (selected.flatMap copyEqualities) := by
  have solved := (accepted_original_demands history accepted).2.2
  exact ⟨(ConstraintStep.intrude state event selected retained qualifies actual).sound solved,
    ((holds_append _ _ _).mp solved).1⟩

/-- The existing metadata hypotheses are consumed without replacing actual
current/captured/non-generic guards by a numeric-only condition. -/
theorem metadata_checked_publication_with_clients
    {n count bounds beforeCapture afterCapture beforeLive afterLive roots uses q boundary graph refs}
    {inventory clients : Store} {certificate}
    (bounded : ScopedPublication.BoundsBounded n bounds)
    (captureTransport : ScopedPublication.MetadataTransport n beforeCapture afterCapture q)
    (liveTransport : ScopedPublication.MetadataTransport n beforeLive afterLive q)
    (levelClosure : ScopedPublication.BoundLevelsClosed
      (bounds.map (ScopedPublication.Bound.rename q)) afterCapture.levels)
    (nonGenericClosure : ScopedPublication.NonGenericClosed
      (bounds.map (ScopedPublication.Bound.rename q)) afterCapture.nonGeneric)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (coverage : ∀ clause,
      ScopedPublication.Published n (bounds.map (ScopedPublication.Bound.rename q))
        (ScopedPublication.captureGuard boundary afterCapture)
        (ScopedPublication.useGuard (ScopedPublication.captureGuard boundary afterCapture) boundary afterLive)
        (roots.map (ScopedPublication.Row.rename q)) uses clause → clause ∈ inventory)
    (checked : checkStore graph refs certificate
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count
        (ScopedPublication.useGuard (ScopedPublication.captureGuard boundary afterCapture) boundary afterLive) q))) = true) :
    graph.Valid ∧ graph.Guarded ∧
      PublishedSatisfied graph
        (fun k i => refs k (publicationTransport n count
          (ScopedPublication.useGuard (ScopedPublication.captureGuard boundary afterCapture) boundary afterLive) q k i))
        n bounds (ScopedPublication.captureGuard boundary beforeCapture)
        (ScopedPublication.useGuard (ScopedPublication.captureGuard boundary beforeCapture) boundary beforeLive) roots uses ∧
      StoreSatisfied graph
        (fun k i => refs k (publicationTransport n count
          (ScopedPublication.useGuard (ScopedPublication.captureGuard boundary afterCapture) boundary afterLive) q k i)) clients :=
  checked_publication_with_clients bounded
    (ScopedPublication.use_inactive_images
      (ScopedPublication.capture_inactive_images captureTransport) liveTransport)
    (ScopedPublication.capture_stopped_closed levelClosure nonGenericClosure)
    (ScopedPublication.useGuard_stops _ _ _) useBounds coverage checked

/-! Concrete original-syntax publication with two fresh uses, a shared anchor,
union/intersection in the function result, and a cross-use client. -/
def publicationGraph : Graph
  | .value => [.structural (.function 0 0 0 1), .intersection 2 3, .union 0 4,
      .structural .top, .structural (.atom 9)]
  | .effect => [.structural (.atom 17)]

def publicationCertificate : Lattice.Certificate :=
  [(⟨.value,0,0⟩,.structural),(⟨.effect,0,0⟩,.refl),
   (⟨.value,1,1⟩,.intersectionMono (.unionMono .structural .refl) .top),
   (⟨.value,1,2⟩,.intersectionLeft),(⟨.value,1,3⟩,.top)]

def latticeBound : ScopedPublication.Bound :=
  ⟨.value,1,.positive,
    .function (.var 0) (.var 0) (.var 0) (.intersection (.union (.var 0) (.atom 9)) .top)⟩
def beforeFlags : ScopedPublication.Flags := fun _ i => decide (i = 1)
def afterFlags : ScopedPublication.Flags := fun _ _ => false
def anchorQuotient : Renaming := fun _ _ => 0
def zeroReferences : References := fun _ _ => 0
def publicationRoots : List ScopedPublication.Row := [⟨.value,1⟩]
def publicationInventory : Store := [(latticeBound.rename anchorQuotient).clause]
def publicationClients : Store := [⟨.value,.var 3,.var 5⟩]
def pulledReferences : References :=
  fun k i => zeroReferences k (publicationTransport 2 2 afterFlags anchorQuotient k i)
def publicationPairs : List Comparison := [⟨.value,0,0⟩,⟨.value,0,0⟩]
def publicationTerminal : ConstraintState :=
  ⟨[⟨.value,0,0⟩,⟨.effect,0,0⟩,⟨.effect,0,0⟩,⟨.value,1,1⟩,⟨.value,0,0⟩],[]⟩

theorem publication_inventory_coverage : ∀ clause,
    ScopedPublication.Published 2 ([latticeBound].map (ScopedPublication.Bound.rename anchorQuotient))
      afterFlags afterFlags (publicationRoots.map (ScopedPublication.Row.rename anchorQuotient)) [0,1] clause →
    clause ∈ publicationInventory := by
  intro clause published
  cases published with
  | base bound member =>
      have same : bound = latticeBound.rename anchorQuotient := by simpa using member
      subst bound
      exact List.mem_cons_self
  | copy bound member use hu reach active =>
      change false = true at active
      cases active

theorem publication_inventory_decoded : decodeStore publicationGraph zeroReferences
    (publicationInventory ++ publicationClients.map
      (Constraint.rename (publicationTransport 2 2 afterFlags anchorQuotient))) = some publicationPairs := rfl

theorem publication_inventory_history : ConstraintHistory publicationGraph
    (fun _ _ => False) (fun _ => 0) ⟨publicationPairs,[]⟩ publicationTerminal :=
  .cons (.decompose ⟨.value,0,0⟩
    [⟨.value,0,0⟩,⟨.effect,0,0⟩,⟨.effect,0,0⟩,⟨.value,1,1⟩] [⟨.value,0,0⟩] [] rfl) (.nil _)

theorem publication_terminal_accepted :
    accepts publicationGraph publicationCertificate publicationTerminal.obligations = true := rfl

theorem lattice_publication_and_clients : publicationGraph.Valid ∧ publicationGraph.Guarded ∧
    PublishedSatisfied publicationGraph pulledReferences 2 [latticeBound] beforeFlags beforeFlags publicationRoots [0,1] ∧
    StoreSatisfied publicationGraph pulledReferences publicationClients := by
  apply publication_history_with_clients (n := 2) (count := 2) (bounds := [latticeBound])
    (beforeCap := beforeFlags) (afterCap := afterFlags) (beforeUse := beforeFlags) (afterUse := afterFlags)
    (roots := publicationRoots) (uses := [0,1]) (q := anchorQuotient)
    (graph := publicationGraph) (refs := zeroReferences) (inventory := publicationInventory) (clients := publicationClients)
    (pairs := publicationPairs) (events := []) (ref := fun _ _ => False) (birth := fun _ => 0)
    (last := publicationTerminal) (certificate := publicationCertificate)
  · intro bound member
    have same : bound = latticeBound := by simpa using member
    subst bound
    simp [latticeBound,Generalization.Bounded]
  · exact fun _ _ _ _ => rfl
  · exact fun _ _ _ _ _ => rfl
  · exact fun _ _ _ => rfl
  · intro use member
    simp at member
    omega
  · exact publication_inventory_coverage
  · exact publication_inventory_decoded
  · exact publication_inventory_history
  · exact publication_terminal_accepted

theorem lattice_two_uses_and_client :
    ClauseSatisfied publicationGraph pulledReferences
      (latticeBound.clause.rename (ScopedPublication.fresh 2 beforeFlags 0)) ∧
    ClauseSatisfied publicationGraph pulledReferences
      (latticeBound.clause.rename (ScopedPublication.fresh 2 beforeFlags 1)) ∧
    ClauseSatisfied publicationGraph pulledReferences ⟨.value,.var 3,.var 5⟩ := by
  have all := lattice_publication_and_clients
  refine ⟨all.2.2.1 _ ?_,all.2.2.1 _ ?_,all.2.2.2 _ List.mem_cons_self⟩
  · exact .copy latticeBound List.mem_cons_self 0 (by simp) (.root _ List.mem_cons_self) rfl
  · exact .copy latticeBound List.mem_cons_self 1 (by simp) (.root _ List.mem_cons_self) rfl

theorem lattice_tail_rejected :
    decodeTerm publicationGraph zeroReferences
      (.recordCons 7 true (.atom 9) (.intersection (.union (.var 0) (.atom 9)) .top)) = none := rfl

theorem wrong_effect_kind_rejected :
    decodeTerm publicationGraph (fun _ _ => 1) (Term.var (k := .effect) 0) = none := rfl

/-! Exact compatibility with the original decoder, in addition to the proved
old-history translation. New lattice nodes do not change any old constructor. -/
theorem findList_ofRegular {k} (node : Regular.Node k) (nodes : List (Regular.Node k)) :
    findList (.structural node) (nodes.map Node.structural) =
      RegularPublication.findList node nodes := by
  induction nodes with
  | nil => rfl
  | cons head tail ih => simp [findList,RegularPublication.findList,ih]

theorem findNode_ofRegular (graph : Regular.Graph) {k} (node : Regular.Node k) :
    findNode (ofRegular graph) (.structural node) = RegularPublication.findNode graph node :=
  findList_ofRegular _ _

theorem findList_union_absent {k} (a b : Nat) (nodes : List (Regular.Node k)) :
    findList (Node.union (k := k) a b) (nodes.map Node.structural) = none := by
  induction nodes with
  | nil => rfl
  | cons head tail ih => simp [findList,ih]

theorem findList_intersection_absent {k} (a b : Nat) (nodes : List (Regular.Node k)) :
    findList (Node.intersection (k := k) a b) (nodes.map Node.structural) = none := by
  induction nodes with
  | nil => rfl
  | cons head tail ih => simp [findList,ih]

theorem findNode_union_ofRegular (graph : Regular.Graph) (k : Kind) (a b : Nat) :
    findNode (ofRegular graph) (Node.union (k := k) a b) = none := findList_union_absent _ _ _

theorem findNode_intersection_ofRegular (graph : Regular.Graph) (k : Kind) (a b : Nat) :
    findNode (ofRegular graph) (Node.intersection (k := k) a b) = none := findList_intersection_absent _ _ _

theorem checkedReference_ofRegular (graph : Regular.Graph) (k : Kind) (i : Nat) :
    checkedReference (ofRegular graph) k i = RegularPublication.checkedReference graph k i := by
  cases h : graph.lookup k i <;> simp [checkedReference,RegularPublication.checkedReference,ofRegular_lookup,h]

theorem prependRecord_ofRegular (graph : Regular.Graph) (label : Nat) (optional : Bool) (field tail : Nat) :
    prependRecord (ofRegular graph) label optional field tail =
      RegularPublication.prependRecord graph label optional field tail := by
  cases h : graph.lookup .value tail with
  | none => simp [prependRecord,RegularPublication.prependRecord,ofRegular_lookup,h]
  | some node => cases node <;>
      simp [prependRecord,RegularPublication.prependRecord,ofRegular_lookup,h,findNode_ofRegular]

theorem prependTuple_ofRegular (graph : Regular.Graph) (head tail : Nat) :
    prependTuple (ofRegular graph) head tail = RegularPublication.prependTuple graph head tail := by
  cases h : graph.lookup .value tail with
  | none => simp [prependTuple,RegularPublication.prependTuple,ofRegular_lookup,h]
  | some node => cases node <;>
      simp [prependTuple,RegularPublication.prependTuple,ofRegular_lookup,h,findNode_ofRegular]

theorem prependVariant_ofRegular (graph : Regular.Graph) (tag payloads tail : Nat) :
    prependVariant (ofRegular graph) tag payloads tail =
      RegularPublication.prependVariant graph tag payloads tail := by
  cases hp : graph.lookup .value payloads with
  | none => simp [prependVariant,RegularPublication.prependVariant,ofRegular_lookup,hp]
  | some payloadNode =>
      cases ht : graph.lookup .value tail with
      | none => cases payloadNode <;>
          simp [prependVariant,RegularPublication.prependVariant,ofRegular_lookup,hp,ht]
      | some tailNode => cases payloadNode <;> cases tailNode <;>
          simp [prependVariant,RegularPublication.prependVariant,ofRegular_lookup,hp,ht,findNode_ofRegular]

theorem decodeTerm_ofRegular (graph : Regular.Graph) (refs : References) {k} (term : Term k) :
    decodeTerm (ofRegular graph) refs term = RegularPublication.decodeTerm graph refs term := by
  induction term <;>
    simp_all [decodeTerm,RegularPublication.decodeTerm,checkedReference_ofRegular,findNode_ofRegular,
      findNode_union_ofRegular,findNode_intersection_ofRegular,prependRecord_ofRegular,
      prependTuple_ofRegular,prependVariant_ofRegular]

theorem decodeStore_ofRegular (graph : Regular.Graph) (refs : References) (store : Store) :
    decodeStore (ofRegular graph) refs store = RegularPublication.decodeStore graph refs store := by
  induction store with
  | nil => rfl
  | cons clause rest ih =>
      simp [decodeStore,RegularPublication.decodeStore,decodeConstraint,
        RegularPublication.decodeConstraint,decodeTerm_ofRegular,ih]

theorem old_store_solution_embeds {graph : Regular.Graph} {refs store}
    (solved : RegularPublication.StoreSatisfied graph refs store) :
    StoreSatisfied (ofRegular graph) refs store := by
  intro clause hc
  rcases solved clause hc with ⟨pair,decoded,related⟩
  refine ⟨pair,?_,Lattice.ofRegular_sub related⟩
  simpa [decodeConstraint,RegularPublication.decodeConstraint,decodeTerm_ofRegular] using decoded

/-! Append-only constructor completion. Legality mentions only actual variable
lookups, finite row shapes and unique labels. It contains no decoder-success,
subtyping or semantic-model premise. Completion proves the actual decoder
succeeds; final validity and guardedness still come from accepted evidence,
not from prefix extension alone. -/
namespace Completion

def Extends (source target : Graph) : Prop := ∀ k, ∃ suffix, target k = source k ++ suffix

theorem Extends.refl (graph : Graph) : Extends graph graph := fun _ => ⟨[],(List.append_nil _).symm⟩

theorem Extends.trans {a b c : Graph} (ab : Extends a b) (bc : Extends b c) : Extends a c := by
  intro k
  rcases ab k with ⟨xs,hxs⟩
  rcases bc k with ⟨ys,hys⟩
  exact ⟨xs ++ ys,by rw [hys,hxs,List.append_assoc]⟩

theorem lookupList_append_some {α} {xs : List α} {i x} (h : lookupList xs i = some x)
    (ys : List α) : lookupList (xs ++ ys) i = some x := by
  induction xs generalizing i with
  | nil => cases h
  | cons a xs ih => cases i with
    | zero => exact h
    | succ i => exact ih h

theorem Extends.lookup {source target : Graph} (extension : Extends source target)
    {k i node} (h : source.lookup k i = some node) : target.lookup k i = some node := by
  rcases extension k with ⟨suffix,hs⟩
  change lookupList (target k) i = some node
  rw [hs]
  exact lookupList_append_some h suffix

theorem findList_append_some {k} {node : Node k} {xs : List (Node k)} {i}
    (h : findList node xs = some i) (ys : List (Node k)) :
    findList node (xs ++ ys) = some i := by
  induction xs generalizing i with
  | nil => cases h
  | cons a xs ih =>
      by_cases same : a = node
      · simpa [findList,same] using h
      · simp only [List.cons_append,findList,same,↓reduceIte] at h ⊢
        cases hf : findList node xs with
        | none => simp [hf] at h
        | some j =>
            rw [ih hf]
            simpa [hf] using h

theorem Extends.find_node {source target : Graph} (extension : Extends source target)
    {k} {node : Node k} {i} (h : findNode source node = some i) : findNode target node = some i := by
  rcases extension k with ⟨suffix,hs⟩
  change findList node (target k) = some i
  rw [hs]
  exact findList_append_some h suffix

theorem Extends.prepend_record {source target : Graph} (extension : Extends source target)
    {label optional field tail i} (h : prependRecord source label optional field tail = some i) :
    prependRecord target label optional field tail = some i := by
  rcases prependRecord_exact h with ⟨fields,ht,_⟩
  have hf : findNode source (.structural (.record (⟨label,optional,field⟩ :: fields))) = some i := by
    simpa [prependRecord,ht] using h
  simpa [prependRecord,extension.lookup ht] using extension.find_node hf

theorem Extends.prepend_tuple {source target : Graph} (extension : Extends source target)
    {head tail i} (h : prependTuple source head tail = some i) :
    prependTuple target head tail = some i := by
  rcases prependTuple_exact h with ⟨elements,ht,_⟩
  have hf : findNode source (.structural (.tuple (head :: elements))) = some i := by
    simpa [prependTuple,ht] using h
  simpa [prependTuple,extension.lookup ht] using extension.find_node hf

theorem Extends.prepend_variant {source target : Graph} (extension : Extends source target)
    {tag payloads tail i} (h : prependVariant source tag payloads tail = some i) :
    prependVariant target tag payloads tail = some i := by
  rcases prependVariant_exact h with ⟨elements,alternatives,hp,ht,_⟩
  have hf : findNode source (.structural (.variant (⟨tag,elements⟩ :: alternatives))) = some i := by
    simpa [prependVariant,hp,ht] using h
  simpa [prependVariant,extension.lookup hp,extension.lookup ht] using extension.find_node hf

theorem Extends.checked_reference {source target : Graph} (extension : Extends source target)
    {k i j} (h : checkedReference source k i = some j) : checkedReference target k i = some j := by
  cases hl : source.lookup k i with
  | none => simp [checkedReference,hl] at h
  | some node => simpa [checkedReference,hl,extension.lookup hl] using h

theorem Extends.decode_term {source target : Graph} (extension : Extends source target)
    {refs k} {term : Term k} {i} (h : decodeTerm source refs term = some i) :
    decodeTerm target refs term = some i := by
  induction term generalizing i with
  | var identity => exact extension.checked_reference h
  | atom identity => exact extension.find_node h
  | bottom => exact extension.find_node h
  | top => exact extension.find_node h
  | union a b iha ihb | intersection a b iha ihb =>
      rcases bind_some h with ⟨a',ha,h⟩
      rcases bind_some h with ⟨b',hb,h⟩
      simpa [decodeTerm,iha ha,ihb hb] using extension.find_node h
  | function a ae re r iha ihae ihre ihr =>
      rcases bind_some h with ⟨a',ha,h⟩
      rcases bind_some h with ⟨ae',hae,h⟩
      rcases bind_some h with ⟨re',hre,h⟩
      rcases bind_some h with ⟨r',hr,h⟩
      simpa [decodeTerm,iha ha,ihae hae,ihre hre,ihr hr] using extension.find_node h
  | recordNil => exact extension.find_node h
  | tupleNil => exact extension.find_node h
  | variantNil => exact extension.find_node h
  | recordCons label optional field tail ihf iht =>
      rcases bind_some h with ⟨f,hf,h⟩
      rcases bind_some h with ⟨t,ht,h⟩
      simpa [decodeTerm,ihf hf,iht ht] using extension.prepend_record h
  | tupleCons head tail ihh iht =>
      rcases bind_some h with ⟨a,ha,h⟩
      rcases bind_some h with ⟨t,ht,h⟩
      simpa [decodeTerm,ihh ha,iht ht] using extension.prepend_tuple h
  | variantCons tag payloads tail ihp iht =>
      rcases bind_some h with ⟨p,hp,h⟩
      rcases bind_some h with ⟨t,ht,h⟩
      simpa [decodeTerm,ihp hp,iht ht] using extension.prepend_variant h

theorem Extends.decode_constraint {source target : Graph} (extension : Extends source target)
    {refs clause pair} (h : decodeConstraint source refs clause = some pair) :
    decodeConstraint target refs clause = some pair := by
  rcases bind_some h with ⟨lower,hl,h⟩
  rcases bind_some h with ⟨upper,hu,h⟩
  simpa [decodeConstraint,extension.decode_term hl,extension.decode_term hu] using h

def appendNode (graph : Graph) : {k : Kind} → Node k → Graph
  | .value, node => fun k => match k with
      | .value => graph .value ++ [node]
      | .effect => graph .effect
  | .effect, node => fun k => match k with
      | .value => graph .value
      | .effect => graph .effect ++ [node]

theorem appendNode_extends (graph : Graph) {k} (node : Node k) : Extends graph (appendNode graph node) := by
  cases k <;> intro j <;> cases j <;> first
    | exact ⟨[node],rfl⟩
    | exact ⟨[],(List.append_nil _).symm⟩

def intern (graph : Graph) {k} (node : Node k) : Graph × Nat :=
  match findNode graph node with
  | some i => (graph,i)
  | none => (appendNode graph node,(graph k).length)

theorem findList_append_self {k} (node : Node k) (xs : List (Node k))
    (missing : findList node xs = none) : findList node (xs ++ [node]) = some xs.length := by
  induction xs with
  | nil => simp [findList]
  | cons a xs ih =>
      by_cases same : a = node
      · simp [findList,same] at missing
      · have tailMissing : findList node xs = none := by
          cases h : findList node xs <;> simp_all [findList]
        simp [findList,same,ih tailMissing]

theorem intern_spec (graph : Graph) {k} (node : Node k) :
    Extends graph (intern graph node).1 ∧ findNode (intern graph node).1 node = some (intern graph node).2 := by
  cases found : findNode graph node with
  | some i => exact ⟨by simp [intern,found]; exact Extends.refl graph,by simp [intern,found]⟩
  | none =>
      refine ⟨by simpa [intern,found] using appendNode_extends graph node,?_⟩
      simp only [intern,found]
      cases k <;> simpa only [findNode,appendNode] using findList_append_self node _ found

inductive Shape : Kind → Type where
  | plain {k} : Shape k
  | record (labels : List Nat) : Shape .value
  | tuple : Shape .value
  | variant (tags : List Nat) : Shape .value
  deriving DecidableEq

def shapeOf : {k : Kind} → Node k → Shape k
  | _, .union _ _ | _, .intersection _ _ => .plain
  | _, .structural (.atom _) | _, .structural .bottom | _, .structural .top => .plain
  | .value, .structural (.function _ _ _ _) => .plain
  | .value, .structural (.record fields) => .record (fields.map Field.label)
  | .value, .structural (.tuple _) => .tuple
  | .value, .structural (.variant alternatives) => .variant (alternatives.map Alternative.tag)

inductive Lawful (base : Graph) (refs : References) : {k : Kind} → Term k → Shape k → Prop where
  | var {k} (identity : Nat) (node : Node k)
      (present : base.lookup k (refs k identity) = some node) :
      Lawful base refs (.var identity) (shapeOf node)
  | atom {k} (identity : Nat) : Lawful base refs (Term.atom (k := k) identity) .plain
  | bottom {k} : Lawful base refs (Term.bottom (k := k)) .plain
  | top {k} : Lawful base refs (Term.top (k := k)) .plain
  | union (k : Kind) {left right sl sr}
      (a : Lawful base refs (k := k) left sl) (b : Lawful base refs right sr) :
      Lawful base refs (.union left right) .plain
  | intersection (k : Kind) {left right sl sr}
      (a : Lawful base refs (k := k) left sl) (b : Lawful base refs right sr) :
      Lawful base refs (.intersection left right) .plain
  | function {a ae re r sa sae sre sr}
      (argument : Lawful base refs a sa) (argumentEffect : Lawful base refs ae sae)
      (resultEffect : Lawful base refs re sre) (result : Lawful base refs r sr) :
      Lawful base refs (.function a ae re r) .plain
  | recordNil : Lawful base refs .recordNil (.record [])
  | recordCons {field tail sf labels} (label : Nat) (optional : Bool)
      (head : Lawful base refs field sf) (rest : Lawful base refs tail (.record labels))
      (fresh : label ∉ labels) :
      Lawful base refs (.recordCons label optional field tail) (.record (label :: labels))
  | tupleNil : Lawful base refs .tupleNil .tuple
  | tupleCons {head tail sh} (first : Lawful base refs head sh)
      (rest : Lawful base refs tail .tuple) : Lawful base refs (.tupleCons head tail) .tuple
  | variantNil : Lawful base refs .variantNil (.variant [])
  | variantCons {payloads tail tags} (tag : Nat)
      (payload : Lawful base refs payloads .tuple) (rest : Lawful base refs tail (.variant tags))
      (fresh : tag ∉ tags) :
      Lawful base refs (.variantCons tag payloads tail) (.variant (tag :: tags))

def completeTerm (graph : Graph) (refs : References) : {k : Kind} → Term k → Option (Graph × Nat)
  | k, .var identity => (checkedReference graph k (refs k identity)).map (graph,·)
  | k, .atom identity => some (intern graph (k := k) (.structural (.atom identity)))
  | k, .bottom => some (intern graph (k := k) (.structural .bottom))
  | k, .top => some (intern graph (k := k) (.structural .top))
  | k, .union left right => do
      let (g1,l) ← completeTerm graph refs left
      let (g2,r) ← completeTerm g1 refs right
      pure (intern g2 (k := k) (.union l r))
  | k, .intersection left right => do
      let (g1,l) ← completeTerm graph refs left
      let (g2,r) ← completeTerm g1 refs right
      pure (intern g2 (k := k) (.intersection l r))
  | .value, .function a ae re r => do
      let (g1,a') ← completeTerm graph refs a
      let (g2,ae') ← completeTerm g1 refs ae
      let (g3,re') ← completeTerm g2 refs re
      let (g4,r') ← completeTerm g3 refs r
      pure (intern g4 (.structural (.function a' ae' re' r')))
  | .value, .recordNil => some (intern graph (.structural (.record [])))
  | .value, .tupleNil => some (intern graph (.structural (.tuple [])))
  | .value, .variantNil => some (intern graph (.structural (.variant [])))
  | .value, .recordCons label optional field tail => do
      let (g1,f) ← completeTerm graph refs field
      let (g2,t) ← completeTerm g1 refs tail
      match g2.lookup .value t with
      | some (.structural (.record fields)) => pure (intern g2 (.structural (.record (⟨label,optional,f⟩ :: fields))))
      | _ => none
  | .value, .tupleCons head tail => do
      let (g1,h) ← completeTerm graph refs head
      let (g2,t) ← completeTerm g1 refs tail
      match g2.lookup .value t with
      | some (.structural (.tuple elements)) => pure (intern g2 (.structural (.tuple (h :: elements))))
      | _ => none
  | .value, .variantCons tag payloads tail => do
      let (g1,p) ← completeTerm graph refs payloads
      let (g2,t) ← completeTerm g1 refs tail
      match g2.lookup .value p, g2.lookup .value t with
      | some (.structural (.tuple elements)), some (.structural (.variant alternatives)) =>
          pure (intern g2 (.structural (.variant (⟨tag,elements⟩ :: alternatives))))
      | _, _ => none

structure Built (source : Graph) (refs : References) {k} (term : Term k) (shape : Shape k)
    (target : Graph) (identity : Nat) : Prop where
  extension : Extends source target
  decoded : decodeTerm target refs term = some identity
  represents : ∃ node, target.lookup k identity = some node ∧ shapeOf node = shape

theorem Built.record {source refs term labels target identity}
    (built : Built source refs term (.record labels) target identity) :
    ∃ fields, target.lookup .value identity = some (.structural (.record fields)) ∧
      fields.map Field.label = labels := by
  rcases built.represents with ⟨node,hn,hs⟩
  cases node with
  | union _ _ | intersection _ _ => cases hs
  | structural node => cases node <;> simp_all [shapeOf]

theorem Built.tuple {source refs term target identity}
    (built : Built source refs term .tuple target identity) :
    ∃ elements, target.lookup .value identity = some (.structural (.tuple elements)) := by
  rcases built.represents with ⟨node,hn,hs⟩
  cases node with
  | union _ _ | intersection _ _ => cases hs
  | structural node => cases node <;> simp_all [shapeOf]

theorem Built.variant {source refs term tags target identity}
    (built : Built source refs term (.variant tags) target identity) :
    ∃ alternatives, target.lookup .value identity = some (.structural (.variant alternatives)) ∧
      alternatives.map Alternative.tag = tags := by
  rcases built.represents with ⟨node,hn,hs⟩
  cases node with
  | union _ _ | intersection _ _ => cases hs
  | structural node => cases node <;> simp_all [shapeOf]

private theorem intern_build {graph refs k} {term : Term k} (node : Node k)
    (form : ∀ g, decodeTerm g refs term = findNode g node) :
    Built graph refs term (shapeOf node) (intern graph node).1 (intern graph node).2 := by
  rcases intern_spec graph node with ⟨extension,found⟩
  exact ⟨extension,by rw [form]; exact found,⟨node,findNode_sound found,rfl⟩⟩

/-- Syntactic lookup/shape legality constructs successful completion and the
actual decoder equation; successful execution is not an assumed premise. -/
theorem completeTerm_correct {base refs k} {term : Term k} {shape}
    (lawful : Lawful base refs term shape) :
    ∀ graph, Extends base graph →
      ∃ target identity, completeTerm graph refs term = some (target,identity) ∧
        Built graph refs term shape target identity := by
  induction lawful with
  | var identity node present =>
      intro graph extension
      have hn := extension.lookup present
      refine ⟨graph,_,?_,Extends.refl graph,?_,⟨node,hn,rfl⟩⟩
      · simp [completeTerm,checkedReference,hn]
      · simp [decodeTerm,checkedReference,hn]
  | atom identity => intro graph extension; exact ⟨_,_,rfl,intern_build (.structural (.atom identity)) (fun _ => rfl)⟩
  | bottom => intro graph extension; exact ⟨_,_,rfl,intern_build (.structural .bottom) (fun _ => rfl)⟩
  | top => intro graph extension; exact ⟨_,_,rfl,intern_build (.structural .top) (fun _ => rfl)⟩
  | recordNil => intro graph extension; exact ⟨_,_,rfl,intern_build (.structural (.record [])) (fun _ => rfl)⟩
  | tupleNil => intro graph extension; exact ⟨_,_,rfl,intern_build (.structural (.tuple [])) (fun _ => rfl)⟩
  | variantNil => intro graph extension; exact ⟨_,_,rfl,intern_build (.structural (.variant [])) (fun _ => rfl)⟩
  | union k left right ihl ihr =>
      intro graph extension
      rcases ihl graph extension with ⟨g1,l,runL,bl⟩
      rcases ihr g1 (extension.trans bl.extension) with ⟨g2,r,runR,br⟩
      let node : Node k := .union l r
      rcases intern_spec g2 node with ⟨ei,fi⟩
      refine ⟨(intern g2 node).1,(intern g2 node).2,?_,(bl.extension.trans br.extension).trans ei,?_,
        ⟨node,findNode_sound fi,rfl⟩⟩
      · simp [completeTerm,runL,runR,node]
      · simpa [decodeTerm,(br.extension.trans ei).decode_term bl.decoded,
          ei.decode_term br.decoded,node] using fi
  | intersection k left right ihl ihr =>
      intro graph extension
      rcases ihl graph extension with ⟨g1,l,runL,bl⟩
      rcases ihr g1 (extension.trans bl.extension) with ⟨g2,r,runR,br⟩
      let node : Node k := .intersection l r
      rcases intern_spec g2 node with ⟨ei,fi⟩
      refine ⟨(intern g2 node).1,(intern g2 node).2,?_,(bl.extension.trans br.extension).trans ei,?_,
        ⟨node,findNode_sound fi,rfl⟩⟩
      · simp [completeTerm,runL,runR,node]
      · simpa [decodeTerm,(br.extension.trans ei).decode_term bl.decoded,
          ei.decode_term br.decoded,node] using fi
  | function argument argumentEffect resultEffect result iha ihae ihre ihr =>
      intro graph extension
      rcases iha graph extension with ⟨g1,a,runA,ba⟩
      rcases ihae g1 (extension.trans ba.extension) with ⟨g2,ae,runAE,bae⟩
      rcases ihre g2 ((extension.trans ba.extension).trans bae.extension) with ⟨g3,re,runRE,bre⟩
      rcases ihr g3 (((extension.trans ba.extension).trans bae.extension).trans bre.extension) with ⟨g4,r,runR,br⟩
      have e14 := (bae.extension.trans bre.extension).trans br.extension
      have e24 := bre.extension.trans br.extension
      let node := Node.structural (.function a ae re r)
      rcases intern_spec g4 node with ⟨ei,fi⟩
      refine ⟨(intern g4 node).1,(intern g4 node).2,?_,
        (((ba.extension.trans bae.extension).trans bre.extension).trans br.extension).trans ei,?_,
        ⟨node,findNode_sound fi,rfl⟩⟩
      · simp [completeTerm,runA,runAE,runRE,runR,node]
      · simpa [decodeTerm,(e14.trans ei).decode_term ba.decoded,
          (e24.trans ei).decode_term bae.decoded,(br.extension.trans ei).decode_term bre.decoded,
          ei.decode_term br.decoded,node] using fi
  | recordCons label optional head rest fresh ihh iht =>
      intro graph extension
      rcases ihh graph extension with ⟨g1,f,runF,bf⟩
      rcases iht g1 (extension.trans bf.extension) with ⟨g2,t,runT,bt⟩
      rcases bt.record with ⟨fields,ht,labels⟩
      let node := Node.structural (.record (⟨label,optional,f⟩ :: fields))
      rcases intern_spec g2 node with ⟨ei,fi⟩
      refine ⟨(intern g2 node).1,(intern g2 node).2,?_,
        (bf.extension.trans bt.extension).trans ei,?_,⟨node,findNode_sound fi,?_⟩⟩
      · simp [completeTerm,runF,runT,ht,node]
      · simpa [decodeTerm,(bt.extension.trans ei).decode_term bf.decoded,
          ei.decode_term bt.decoded,prependRecord,ei.lookup ht,node] using fi
      · simp [node,shapeOf,labels]
  | tupleCons first rest ihh iht =>
      intro graph extension
      rcases ihh graph extension with ⟨g1,h,runH,bh⟩
      rcases iht g1 (extension.trans bh.extension) with ⟨g2,t,runT,bt⟩
      rcases bt.tuple with ⟨elements,ht⟩
      let node := Node.structural (.tuple (h :: elements))
      rcases intern_spec g2 node with ⟨ei,fi⟩
      refine ⟨(intern g2 node).1,(intern g2 node).2,?_,
        (bh.extension.trans bt.extension).trans ei,?_,⟨node,findNode_sound fi,rfl⟩⟩
      · simp [completeTerm,runH,runT,ht,node]
      · simpa [decodeTerm,(bt.extension.trans ei).decode_term bh.decoded,
          ei.decode_term bt.decoded,prependTuple,ei.lookup ht,node] using fi
  | variantCons tag payload rest fresh ihp iht =>
      intro graph extension
      rcases ihp graph extension with ⟨g1,p,runP,bp⟩
      rcases iht g1 (extension.trans bp.extension) with ⟨g2,t,runT,bt⟩
      rcases bp.tuple with ⟨elements,hp⟩
      have hp2 := bt.extension.lookup hp
      rcases bt.variant with ⟨alternatives,ht,tags⟩
      let node := Node.structural (.variant (⟨tag,elements⟩ :: alternatives))
      rcases intern_spec g2 node with ⟨ei,fi⟩
      refine ⟨(intern g2 node).1,(intern g2 node).2,?_,
        (bp.extension.trans bt.extension).trans ei,?_,⟨node,findNode_sound fi,?_⟩⟩
      · simp [completeTerm,runP,runT,hp2,ht,node]
      · simpa [decodeTerm,(bt.extension.trans ei).decode_term bp.decoded,
          ei.decode_term bt.decoded,prependVariant,ei.lookup hp2,ei.lookup ht,node] using fi
      · simp [node,shapeOf,tags]

def LawfulClause (base : Graph) (refs : References) (clause : Constraint) : Prop :=
  ∃ lowerShape upperShape, Lawful base refs clause.lower lowerShape ∧ Lawful base refs clause.upper upperShape

def LawfulStore (base : Graph) (refs : References) (store : Store) : Prop :=
  ∀ clause, clause ∈ store → LawfulClause base refs clause

def completeConstraint (graph : Graph) (refs : References) (clause : Constraint) : Option (Graph × Comparison) := do
  let (g1,lower) ← completeTerm graph refs clause.lower
  let (g2,upper) ← completeTerm g1 refs clause.upper
  pure (g2,⟨clause.kind,lower,upper⟩)

def completeStore (graph : Graph) (refs : References) : Store → Option (Graph × List Comparison)
  | [] => some (graph,[])
  | clause :: rest => do
      let (g1,pair) ← completeConstraint graph refs clause
      let (g2,pairs) ← completeStore g1 refs rest
      pure (g2,pair :: pairs)

theorem completeConstraint_correct {base refs clause} (lawful : LawfulClause base refs clause)
    (graph : Graph) (extension : Extends base graph) :
    ∃ target pair, completeConstraint graph refs clause = some (target,pair) ∧
      Extends graph target ∧ decodeConstraint target refs clause = some pair := by
  rcases lawful with ⟨sl,su,hl,hu⟩
  rcases completeTerm_correct hl graph extension with ⟨g1,lower,runL,bl⟩
  rcases completeTerm_correct hu g1 (extension.trans bl.extension) with ⟨g2,upper,runU,bu⟩
  refine ⟨g2,⟨clause.kind,lower,upper⟩,?_,bl.extension.trans bu.extension,?_⟩
  · simp [completeConstraint,runL,runU]
  · simp [decodeConstraint,bu.extension.decode_term bl.decoded,bu.decoded]

theorem completeStore_correct {base refs store} (lawful : LawfulStore base refs store) :
    ∀ graph, Extends base graph →
      ∃ target pairs, completeStore graph refs store = some (target,pairs) ∧
        Extends graph target ∧ decodeStore target refs store = some pairs := by
  induction store with
  | nil => intro graph extension; exact ⟨graph,[],rfl,Extends.refl graph,rfl⟩
  | cons clause rest ih =>
      intro graph extension
      rcases completeConstraint_correct (lawful clause List.mem_cons_self) graph extension with
        ⟨g1,pair,runC,ec,dc⟩
      have tailLawful : LawfulStore base refs rest := fun c hc => lawful c (List.mem_cons_of_mem _ hc)
      rcases ih tailLawful g1 (extension.trans ec) with ⟨g2,pairs,runS,es,ds⟩
      refine ⟨g2,pair :: pairs,?_,ec.trans es,?_⟩
      · simp [completeStore,runC,runS]
      · simp [decodeStore,es.decode_constraint dc,ds]

def completedStore (graph : Graph) (refs : References) (store : Store) : Graph × List Comparison :=
  (completeStore graph refs store).getD (graph,[])

theorem completedStore_correct {graph refs store} (lawful : LawfulStore graph refs store) :
    Extends graph (completedStore graph refs store).1 ∧
      decodeStore (completedStore graph refs store).1 refs store = some (completedStore graph refs store).2 := by
  rcases completeStore_correct lawful graph (Extends.refl graph) with ⟨target,pairs,run,extension,decoded⟩
  simpa [completedStore,run] using And.intro extension decoded

/-- Computed constructor inventory, concrete histories, and the accepted
lattice certificate now imply the original store interpretation. -/
theorem completed_history_store_sound {graph refs store} (lawful : LawfulStore graph refs store) :
    let result := completedStore graph refs store
    ∀ {events ref birth last certificate},
      ConstraintHistory result.1 ref birth ⟨result.2,events⟩ last →
      accepts result.1 certificate last.obligations = true →
      Extends graph result.1 ∧ result.1.Valid ∧ result.1.Guarded ∧ StoreSatisfied result.1 refs store := by
  intro result events ref birth last certificate history accepted
  exact ⟨(completedStore_correct lawful).1,
    history_store_sound (completedStore_correct lawful).2 history accepted⟩

theorem completed_publication_with_clients
    {n count bounds beforeCap afterCap beforeUse afterUse roots uses q graph refs}
    {inventory clients : Store}
    (lawful : LawfulStore graph refs
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q))))
    (bounded : ScopedPublication.BoundsBounded n bounds)
    (images : ScopedPublication.InactiveImages n beforeUse afterUse q)
    (closed : ScopedPublication.StoppedClosed (bounds.map (ScopedPublication.Bound.rename q)) afterCap)
    (stops : ∀ k i, afterCap k i = false → afterUse k i = false)
    (useBounds : ∀ use, use ∈ uses → use < count)
    (coverage : ∀ clause,
      ScopedPublication.Published n (bounds.map (ScopedPublication.Bound.rename q)) afterCap afterUse
        (roots.map (ScopedPublication.Row.rename q)) uses clause → clause ∈ inventory) :
    let result := completedStore graph refs
      (inventory ++ clients.map (Constraint.rename (publicationTransport n count afterUse q)))
    ∀ {events ref birth last certificate},
      ConstraintHistory result.1 ref birth ⟨result.2,events⟩ last →
      accepts result.1 certificate last.obligations = true →
      Extends graph result.1 ∧ result.1.Valid ∧ result.1.Guarded ∧
        PublishedSatisfied result.1 (fun k i => refs k (publicationTransport n count afterUse q k i))
          n bounds beforeCap beforeUse roots uses ∧
        StoreSatisfied result.1 (fun k i => refs k (publicationTransport n count afterUse q k i)) clients := by
  intro result events ref birth last certificate history accepted
  exact ⟨(completedStore_correct lawful).1,
    publication_history_with_clients bounded images closed stops useBounds coverage
      (completedStore_correct lawful).2 history accepted⟩

/-! Start with only a cyclic Function and its effect leaf. Completion must
create both lattice constructors, nil/suffix nodes, a tuple payload, a variant,
and an optional record field. -/
def sparseGraph : Graph
  | .value => [.structural (.function 0 0 0 0)]
  | .effect => [.structural (.atom 17)]

def sparseTerm : Term .value :=
  .recordCons 7 true
    (.intersection
      (.variantCons 8 (.tupleCons (.union (.var 0) .bottom) .tupleNil) .variantNil) .top)
    .recordNil

def sparseStore : Store := [⟨.value,sparseTerm,sparseTerm⟩]
def sparseResult : Graph × List Comparison := completedStore sparseGraph zeroReferences sparseStore

def sparseCertificate : Lattice.Certificate := [(⟨.value,10,10⟩,.refl)]

theorem sparse_term_lawful : Lawful sparseGraph zeroReferences sparseTerm (.record [7]) :=
  .recordCons 7 true
    (.intersection .value
      (.variantCons 8
        (.tupleCons (.union .value (.var 0 (.structural (.function 0 0 0 0)) rfl) .bottom) .tupleNil)
        .variantNil (by simp)) .top)
    .recordNil (by simp)

theorem sparse_store_lawful : LawfulStore sparseGraph zeroReferences sparseStore := by
  intro clause member
  have same : clause = ⟨.value,sparseTerm,sparseTerm⟩ := by simpa [sparseStore] using member
  subst clause
  exact ⟨_,_,sparse_term_lawful,sparse_term_lawful⟩

theorem sparse_missing_constructors : decodeTerm sparseGraph zeroReferences sparseTerm = none := rfl

theorem sparse_completed_inventory : sparseResult.2 = [⟨.value,10,10⟩] := rfl

theorem sparse_completed_accepted : accepts sparseResult.1 sparseCertificate sparseResult.2 = true := rfl

/-- The original finite Store becomes interpretable because constructors are
actually created; no successful decoder equation or model is an input. -/
theorem sparse_completed_satisfied : Extends sparseGraph sparseResult.1 ∧
    sparseResult.1.Valid ∧ sparseResult.1.Guarded ∧ StoreSatisfied sparseResult.1 zeroReferences sparseStore := by
  exact completed_history_store_sound sparse_store_lawful
    (events := []) (ref := fun _ _ => False) (birth := fun _ => 0)
    (ConstraintHistory.nil ⟨sparseResult.2,[]⟩) sparse_completed_accepted

/-- Prefix retention and completion alone do not establish guardedness. The
empty-inventory case preserves an unguarded base, and acceptance rejects it. -/
theorem completion_alone_does_not_check_guard :
    LawfulStore unguardedGraph zeroReferences [] ∧
      completedStore unguardedGraph zeroReferences [] = (unguardedGraph,[]) ∧
      checkGuarded (completedStore unguardedGraph zeroReferences []).1 = false := by
  refine ⟨?_,rfl,rfl⟩
  intro clause member
  cases member

end Completion

theorem optional_metadata_mismatch_rejected :
    decodeTerm (ofRegular RegularPublication.carrierGraph) zeroReferences
      (.recordCons 7 false (.atom 9) .recordNil) = none := by
  rw [decodeTerm_ofRegular]
  exact RegularPublication.optional_metadata_mismatch_rejected

end YulangClosure.SimpleSub.LatticeInference
