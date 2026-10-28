import YulangClosure.SimpleSubRegularGraphExtension

/-! Construct the missing finite constructor inventory without changing existing
references. Legality records actual variable lookups, row shape and fresh labels;
it contains no desired decoding equation or subtype/model premise. -/
namespace YulangClosure.SimpleSub.RegularCompletion
open Regular RegularPublication RegularExtension

inductive Shape : Kind → Type where
  | plain {k} : Shape k
  | record (labels : List Nat) : Shape .value
  | tuple : Shape .value
  | variant (tags : List Nat) : Shape .value
  deriving DecidableEq

def shapeOf : {k : Kind} → Node k → Shape k
  | _, .atom _ | _, .bottom | _, .top => .plain
  | .value, .function _ _ _ _ => .plain
  | .value, .record fields => .record (fields.map Field.label)
  | .value, .tuple _ => .tuple
  | .value, .variant alternatives => .variant (alternatives.map Alternative.tag)

/-- Exact shape conditions are independent of completion and decoding. -/
inductive Lawful (base : Graph) (refs : References) : {k : Kind} → Term k → Shape k → Prop where
  | var {k} (identity : Nat) (node : Node k)
      (present : base.lookup k (refs k identity) = some node) :
      Lawful base refs (.var identity) (shapeOf node)
  | atom {k} (identity : Nat) : Lawful base refs (Term.atom (k := k) identity) .plain
  | bottom {k} : Lawful base refs (Term.bottom (k := k)) .plain
  | top {k} : Lawful base refs (Term.top (k := k)) .plain
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

def intern (graph : Graph) {k} (node : Node k) : Graph × Nat :=
  match findNode graph node with
  | some i => (graph,i)
  | none => (appendNode graph node,(graph k).length)

theorem findList_append_self {k} (node : Node k) (xs : List (Node k))
    (missing : findList node xs = none) :
    findList node (xs ++ [node]) = some xs.length := by
  induction xs with
  | nil => simp [findList]
  | cons a xs ih =>
      by_cases same : a = node
      · simp [findList,same] at missing
      · have tailMissing : findList node xs = none := by
          cases h : findList node xs <;> simp_all [findList]
        simp [findList,same,ih tailMissing]

theorem intern_spec {graph : Graph} (valid : graph.Valid) {k} (node : Node k)
    (nodeValid : node.Valid graph) :
    Extends graph (intern graph node).1 ∧ (intern graph node).1.Valid ∧
      findNode (intern graph node).1 node = some (intern graph node).2 := by
  cases found : findNode graph node with
  | some i => exact ⟨by simp [intern,found]; exact Extends.refl graph,
      by simpa [intern,found] using valid,by simp [intern,found]⟩
  | none =>
      refine ⟨by simpa [intern,found] using appendNode_extends graph node,
        by simpa [intern,found] using appendNode_valid valid nodeValid,?_⟩
      simp only [intern,found]
      cases k <;> simpa only [findNode,appendNode] using
        findList_append_self node _ found

def completeTerm (graph : Graph) (refs : References) : {k : Kind} → Term k → Option (Graph × Nat)
  | k, .var identity => (checkedReference graph k (refs k identity)).map (graph,·)
  | k, .atom identity => some (intern graph (k := k) (.atom identity))
  | k, .bottom => some (intern graph (k := k) .bottom)
  | k, .top => some (intern graph (k := k) .top)
  | _, .union _ _ | _, .intersection _ _ => none
  | .value, .function a ae re r => do
      let (g1,a') ← completeTerm graph refs a
      let (g2,ae') ← completeTerm g1 refs ae
      let (g3,re') ← completeTerm g2 refs re
      let (g4,r') ← completeTerm g3 refs r
      pure (intern g4 (.function a' ae' re' r'))
  | .value, .recordNil => some (intern graph (.record []))
  | .value, .tupleNil => some (intern graph (.tuple []))
  | .value, .variantNil => some (intern graph (.variant []))
  | .value, .recordCons label optional field tail => do
      let (g1,f) ← completeTerm graph refs field
      let (g2,t) ← completeTerm g1 refs tail
      match g2.lookup .value t with
      | some (.record fields) => pure (intern g2 (.record (⟨label,optional,f⟩ :: fields)))
      | _ => none
  | .value, .tupleCons head tail => do
      let (g1,h) ← completeTerm graph refs head
      let (g2,t) ← completeTerm g1 refs tail
      match g2.lookup .value t with
      | some (.tuple elements) => pure (intern g2 (.tuple (h :: elements)))
      | _ => none
  | .value, .variantCons tag payloads tail => do
      let (g1,p) ← completeTerm graph refs payloads
      let (g2,t) ← completeTerm g1 refs tail
      match g2.lookup .value p, g2.lookup .value t with
      | some (.tuple elements), some (.variant alternatives) =>
          pure (intern g2 (.variant (⟨tag,elements⟩ :: alternatives)))
      | _, _ => none

structure Built (source : Graph) (refs : References) {k} (term : Term k) (shape : Shape k)
    (target : Graph) (identity : Nat) : Prop where
  extension : Extends source target
  valid : target.Valid
  decoded : decodeTerm target refs term = some identity
  represents : ∃ node, target.lookup k identity = some node ∧ shapeOf node = shape

theorem Built.present {source refs k} {term : Term k} {shape target identity}
    (built : Built source refs term shape target identity) : Reference.Exists target ⟨k,identity⟩ :=
  decodeTerm_found target refs term identity built.decoded

theorem Built.record {source refs term labels target identity}
    (built : Built source refs term (.record labels) target identity) :
    ∃ fields, target.lookup .value identity = some (.record fields) ∧ fields.map Field.label = labels := by
  rcases built.represents with ⟨node,hn,hs⟩
  cases node <;> simp_all [shapeOf]

theorem Built.tuple {source refs term target identity}
    (built : Built source refs term .tuple target identity) :
    ∃ elements, target.lookup .value identity = some (.tuple elements) := by
  rcases built.represents with ⟨node,hn,hs⟩
  cases node <;> simp_all [shapeOf]

theorem Built.variant {source refs term tags target identity}
    (built : Built source refs term (.variant tags) target identity) :
    ∃ alternatives, target.lookup .value identity = some (.variant alternatives) ∧
      alternatives.map Alternative.tag = tags := by
  rcases built.represents with ⟨node,hn,hs⟩
  cases node <;> simp_all [shapeOf]

theorem function_valid {graph a ae re r}
    (ha : Reference.Exists graph ⟨.value,a⟩) (hae : Reference.Exists graph ⟨.effect,ae⟩)
    (hre : Reference.Exists graph ⟨.effect,re⟩) (hr : Reference.Exists graph ⟨.value,r⟩) :
    (Node.function a ae re r).Valid graph := by
  simp only [Node.Valid,Node.uniqueLabels,Node.references,List.mem_cons,
    List.not_mem_nil,or_false,true_and]
  intro reference member
  rcases member with rfl | rfl | rfl | rfl <;> assumption

theorem record_valid {graph fields label optional child}
    (tail : (Node.record fields).Valid graph) (fresh : label ∉ fields.map Field.label)
    (head : Reference.Exists graph ⟨.value,child⟩) :
    (Node.record (⟨label,optional,child⟩ :: fields)).Valid graph := by
  refine ⟨?_,?_⟩
  · exact List.nodup_cons.mpr ⟨fresh,tail.1⟩
  · intro reference member
    simp only [Node.references,List.map_cons,List.mem_cons] at member
    rcases member with rfl | member
    · exact head
    · exact tail.2 _ member

theorem tuple_valid {graph elements child}
    (tail : (Node.tuple elements).Valid graph) (head : Reference.Exists graph ⟨.value,child⟩) :
    (Node.tuple (child :: elements)).Valid graph := by
  refine ⟨trivial,?_⟩
  intro reference member
  simp only [Node.references,List.map_cons,List.mem_cons] at member
  rcases member with rfl | member
  · exact head
  · exact tail.2 _ member

theorem variant_valid {graph alternatives tag elements}
    (tail : (Node.variant alternatives).Valid graph) (fresh : tag ∉ alternatives.map Alternative.tag)
    (payload : (Node.tuple elements).Valid graph) :
    (Node.variant (⟨tag,elements⟩ :: alternatives)).Valid graph := by
  refine ⟨List.nodup_cons.mpr ⟨fresh,tail.1⟩,?_⟩
  intro reference member
  simp only [Node.references,List.flatMap_cons,List.mem_append] at member
  rcases member with member | member
  · exact payload.2 _ member
  · exact tail.2 _ member

private theorem intern_build {graph refs k} {term : Term k} (valid : graph.Valid)
    (node : Node k) (nodeValid : node.Valid graph)
    (form : ∀ g, decodeTerm g refs term = findNode g node) :
    Built graph refs term (shapeOf node) (intern graph node).1 (intern graph node).2 := by
  rcases intern_spec valid node nodeValid with ⟨extension,good,found⟩
  exact ⟨extension,good,by rw [form]; exact found,⟨node,findNode_sound found,rfl⟩⟩

/-- Completion succeeds from lawful references and row shape alone. The result
retains every old node, is valid, and actually decodes with the existing decoder. -/
theorem completeTerm_correct {base refs k} {term : Term k} {shape}
    (lawful : Lawful base refs term shape) :
    ∀ graph, Extends base graph → graph.Valid →
      ∃ target identity, completeTerm graph refs term = some (target,identity) ∧
        Built graph refs term shape target identity := by
  induction lawful with
  | var identity node present =>
      intro graph extension valid
      have hn := extension.lookup present
      refine ⟨graph,_,?_,Extends.refl graph,valid,?_,⟨node,hn,rfl⟩⟩
      · simp [completeTerm,checkedReference,hn]
      · simp [decodeTerm,checkedReference,hn]
  | atom identity =>
      intro graph extension valid
      exact ⟨_,_,rfl,intern_build valid (.atom identity) (by simp [Node.Valid,Node.uniqueLabels,Node.references]) (fun _ => rfl)⟩
  | bottom =>
      intro graph extension valid
      exact ⟨_,_,rfl,intern_build valid .bottom (by simp [Node.Valid,Node.uniqueLabels,Node.references]) (fun _ => rfl)⟩
  | top =>
      intro graph extension valid
      exact ⟨_,_,rfl,intern_build valid .top (by simp [Node.Valid,Node.uniqueLabels,Node.references]) (fun _ => rfl)⟩
  | recordNil =>
      intro graph extension valid
      exact ⟨_,_,rfl,intern_build valid (.record []) (by simp [Node.Valid,Node.uniqueLabels,Node.references]) (fun _ => rfl)⟩
  | tupleNil =>
      intro graph extension valid
      exact ⟨_,_,rfl,intern_build valid (.tuple []) (by simp [Node.Valid,Node.uniqueLabels,Node.references]) (fun _ => rfl)⟩
  | variantNil =>
      intro graph extension valid
      exact ⟨_,_,rfl,intern_build valid (.variant []) (by simp [Node.Valid,Node.uniqueLabels,Node.references]) (fun _ => rfl)⟩
  | function argument argumentEffect resultEffect result iha ihae ihre ihr =>
      intro graph extension valid
      rcases iha graph extension valid with ⟨g1,a,runA,ba⟩
      rcases ihae g1 (extension.trans ba.extension) ba.valid with ⟨g2,ae,runAE,bae⟩
      rcases ihre g2 ((extension.trans ba.extension).trans bae.extension) bae.valid with ⟨g3,re,runRE,bre⟩
      rcases ihr g3 (((extension.trans ba.extension).trans bae.extension).trans bre.extension) bre.valid with ⟨g4,r,runR,br⟩
      have e14 := (bae.extension.trans bre.extension).trans br.extension
      have e24 := bre.extension.trans br.extension
      let node := Node.function a ae re r
      have nv : node.Valid g4 := function_valid (e14.reference ba.present)
        (e24.reference bae.present) (br.extension.reference bre.present) br.present
      rcases intern_spec br.valid node nv with ⟨ei,vi,fi⟩
      refine ⟨(intern g4 node).1,(intern g4 node).2,?_,
        (((ba.extension.trans bae.extension).trans bre.extension).trans br.extension).trans ei,vi,?_,
        ⟨node,findNode_sound fi,rfl⟩⟩
      · simp [completeTerm,runA,runAE,runRE,runR,node]
      · simpa [decodeTerm,(e14.trans ei).decode_term ba.decoded,
          (e24.trans ei).decode_term bae.decoded,(br.extension.trans ei).decode_term bre.decoded,
          ei.decode_term br.decoded,node] using fi
  | recordCons label optional head rest fresh ihh iht =>
      intro graph extension valid
      rcases ihh graph extension valid with ⟨g1,f,runF,bf⟩
      rcases iht g1 (extension.trans bf.extension) bf.valid with ⟨g2,t,runT,bt⟩
      rcases bt.record with ⟨fields,ht,labels⟩
      let node := Node.record (⟨label,optional,f⟩ :: fields)
      have nv : node.Valid g2 := record_valid (Graph.valid_lookup bt.valid ht)
        (by simpa [labels] using fresh) (bt.extension.reference bf.present)
      rcases intern_spec bt.valid node nv with ⟨ei,vi,fi⟩
      refine ⟨(intern g2 node).1,(intern g2 node).2,?_,
        (bf.extension.trans bt.extension).trans ei,vi,?_,⟨node,findNode_sound fi,?_⟩⟩
      · simp [completeTerm,runF,runT,ht,node]
      · simpa [decodeTerm,(bt.extension.trans ei).decode_term bf.decoded,
          ei.decode_term bt.decoded,prependRecord,ei.lookup ht,node] using fi
      · simp [node,shapeOf,labels]
  | tupleCons first rest ihh iht =>
      intro graph extension valid
      rcases ihh graph extension valid with ⟨g1,h,runH,bh⟩
      rcases iht g1 (extension.trans bh.extension) bh.valid with ⟨g2,t,runT,bt⟩
      rcases bt.tuple with ⟨elements,ht⟩
      let node := Node.tuple (h :: elements)
      have nv : node.Valid g2 := tuple_valid (Graph.valid_lookup bt.valid ht) (bt.extension.reference bh.present)
      rcases intern_spec bt.valid node nv with ⟨ei,vi,fi⟩
      refine ⟨(intern g2 node).1,(intern g2 node).2,?_,
        (bh.extension.trans bt.extension).trans ei,vi,?_,⟨node,findNode_sound fi,rfl⟩⟩
      · simp [completeTerm,runH,runT,ht,node]
      · simpa [decodeTerm,(bt.extension.trans ei).decode_term bh.decoded,
          ei.decode_term bt.decoded,prependTuple,ei.lookup ht,node] using fi
  | variantCons tag payload rest fresh ihp iht =>
      intro graph extension valid
      rcases ihp graph extension valid with ⟨g1,p,runP,bp⟩
      rcases iht g1 (extension.trans bp.extension) bp.valid with ⟨g2,t,runT,bt⟩
      rcases bp.tuple with ⟨elements,hp⟩
      have hp2 := bt.extension.lookup hp
      rcases bt.variant with ⟨alternatives,ht,tags⟩
      let node := Node.variant (⟨tag,elements⟩ :: alternatives)
      have nv : node.Valid g2 := variant_valid (Graph.valid_lookup bt.valid ht)
        (by simpa [tags] using fresh) (Graph.valid_lookup bt.valid hp2)
      rcases intern_spec bt.valid node nv with ⟨ei,vi,fi⟩
      refine ⟨(intern g2 node).1,(intern g2 node).2,?_,
        (bp.extension.trans bt.extension).trans ei,vi,?_,⟨node,findNode_sound fi,?_⟩⟩
      · simp [completeTerm,runP,runT,hp2,ht,node]
      · simpa [decodeTerm,(bt.extension.trans ei).decode_term bp.decoded,
          ei.decode_term bt.decoded,prependVariant,ei.lookup hp2,ei.lookup ht,node] using fi
      · simp [node,shapeOf,tags]

def LawfulClause (base : Graph) (refs : References) (clause : Constraint) : Prop :=
  ∃ lowerShape upperShape,
    Lawful base refs clause.lower lowerShape ∧ Lawful base refs clause.upper upperShape

def LawfulStore (base : Graph) (refs : References) (store : Store) : Prop :=
  ∀ clause, clause ∈ store → LawfulClause base refs clause

def completeConstraint (graph : Graph) (refs : References) (clause : Constraint) :
    Option (Graph × Comparison) := do
  let (g1,lower) ← completeTerm graph refs clause.lower
  let (g2,upper) ← completeTerm g1 refs clause.upper
  pure (g2,⟨clause.kind,lower,upper⟩)

def completeStore (graph : Graph) (refs : References) : Store → Option (Graph × List Comparison)
  | [] => some (graph,[])
  | clause :: rest => do
      let (g1,pair) ← completeConstraint graph refs clause
      let (g2,pairs) ← completeStore g1 refs rest
      pure (g2,pair :: pairs)

theorem completeConstraint_correct {base refs clause}
    (lawful : LawfulClause base refs clause) (graph : Graph)
    (extension : Extends base graph) (valid : graph.Valid) :
    ∃ target pair, completeConstraint graph refs clause = some (target,pair) ∧
      Extends graph target ∧ target.Valid ∧ decodeConstraint target refs clause = some pair := by
  rcases lawful with ⟨sl,su,hl,hu⟩
  rcases completeTerm_correct hl graph extension valid with ⟨g1,lower,runL,bl⟩
  rcases completeTerm_correct hu g1 (extension.trans bl.extension) bl.valid with ⟨g2,upper,runU,bu⟩
  refine ⟨g2,⟨clause.kind,lower,upper⟩,?_,bl.extension.trans bu.extension,bu.valid,?_⟩
  · simp [completeConstraint,runL,runU]
  · simp [decodeConstraint,bu.extension.decode_term bl.decoded,bu.decoded]

/-- A finite inventory is completed jointly with one reference assignment. -/
theorem completeStore_correct {base refs store} (lawful : LawfulStore base refs store) :
    ∀ graph, Extends base graph → graph.Valid →
      ∃ target pairs, completeStore graph refs store = some (target,pairs) ∧
        Extends graph target ∧ target.Valid ∧ decodeStore target refs store = some pairs := by
  induction store with
  | nil => intro graph extension valid; exact ⟨graph,[],rfl,Extends.refl graph,valid,rfl⟩
  | cons clause rest ih =>
      intro graph extension valid
      rcases completeConstraint_correct (lawful clause List.mem_cons_self) graph extension valid with
        ⟨g1,pair,runC,ec,vc,dc⟩
      have tailLawful : LawfulStore base refs rest := fun c hc => lawful c (List.mem_cons_of_mem _ hc)
      rcases ih tailLawful g1 (extension.trans ec) vc with ⟨g2,pairs,runS,es,vs,ds⟩
      refine ⟨g2,pair :: pairs,?_,ec.trans es,vs,?_⟩
      · simp [completeStore,runC,runS]
      · simp [decodeStore,es.decode_constraint dc,ds]

/-- The fallback is unreachable under `LawfulStore` and initial validity. -/
def completedStore (graph : Graph) (refs : References) (store : Store) : Graph × List Comparison :=
  (completeStore graph refs store).getD (graph,[])

theorem completedStore_correct {graph refs store} (valid : graph.Valid)
    (lawful : LawfulStore graph refs store) :
    Extends graph (completedStore graph refs store).1 ∧
      (completedStore graph refs store).1.Valid ∧
      decodeStore (completedStore graph refs store).1 refs store =
        some (completedStore graph refs store).2 := by
  rcases completeStore_correct lawful graph (Extends.refl graph) valid with
    ⟨target,pairs,run,extension,good,decoded⟩
  simpa [completedStore,run] using And.intro extension (And.intro good decoded)

/-- Old accepted evidence remains accepted after the constructed completion;
validity of all newly inserted nodes is derived from the construction. -/
theorem completedStore_accepts {graph refs store certificate demands} (valid : graph.Valid)
    (lawful : LawfulStore graph refs store) (accepted : accepts graph certificate demands = true) :
    accepts (completedStore graph refs store).1 certificate demands = true := by
  have result := completedStore_correct valid lawful
  exact result.1.accepts result.2.1 accepted

/-- A completed inventory consumes the original history theorem without a
supplied decoder-success equation. Certificate acceptance remains explicit. -/
theorem completed_history_store_sound {graph refs store} (valid : graph.Valid)
    (lawful : LawfulStore graph refs store) :
    let result := completedStore graph refs store
    ∀ {events ref birth last certificate},
      ConstraintHistory result.1 ref birth ⟨result.2,events⟩ last →
      accepts result.1 certificate last.obligations = true →
      result.1.Valid ∧ StoreSatisfied result.1 refs store := by
  intro result events ref birth last certificate history accepted
  exact history_store_sound (completedStore_correct valid lawful).2.2 history accepted

/-- Construct missing nil/suffix/payload nodes for the entire finite publication
and client inventory, then apply the existing scoped-publication theorem. -/
theorem completed_publication_with_clients
    {n count bounds beforeCap afterCap beforeUse afterUse roots uses q graph refs}
    {inventory clients : Store}
    (valid : graph.Valid)
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
      result.1.Valid ∧
        PublishedSatisfied result.1 (fun k i => refs k (publicationTransport n count afterUse q k i))
          n bounds beforeCap beforeUse roots uses ∧
        StoreSatisfied result.1 (fun k i => refs k (publicationTransport n count afterUse q k i)) clients := by
  intro result events ref birth last certificate history accepted
  exact publication_history_with_clients bounded images closed stops useBounds coverage
    (completedStore_correct valid lawful).2.2 history accepted

/-! Missing auxiliary nodes beside an existing cyclic constructor. -/
def sparseGraph : Graph
  | .value => [.atom 9,.record [⟨7,true,0⟩],.tuple [0],.variant [⟨8,[0]⟩],.function 4 0 0 4]
  | .effect => [.atom 17]
def identityReferences : References := fun _ i => i
def sparseFunction : Term .value := .function (.var 4) (.var 0) (.var 0) (.var 4)
def sparseInventory : Store :=
  [⟨.value,carrierRecord,carrierRecord⟩,⟨.value,carrierTuple,carrierTuple⟩,
   ⟨.value,carrierVariant,carrierVariant⟩,⟨.value,sparseFunction,sparseFunction⟩]

theorem sparse_valid : sparseGraph.Valid := (checkGraph_iff _).mp rfl

theorem missing_nil_rejected : decodeTerm sparseGraph identityReferences carrierRecord = none := rfl

theorem sparse_inventory_lawful : LawfulStore sparseGraph identityReferences sparseInventory := by
  have record : Lawful sparseGraph identityReferences carrierRecord (.record [7]) :=
    .recordCons 7 true (.atom 9) .recordNil (by simp)
  have tuple : Lawful sparseGraph identityReferences carrierTuple .tuple :=
    .tupleCons (.atom 9) .tupleNil
  have variant : Lawful sparseGraph identityReferences carrierVariant (.variant [8]) :=
    .variantCons 8 tuple .variantNil (by simp)
  have fn : Lawful sparseGraph identityReferences sparseFunction .plain :=
    .function (.var 4 (.function 4 0 0 4) rfl) (.var 0 (.atom 17) rfl)
      (.var 0 (.atom 17) rfl) (.var 4 (.function 4 0 0 4) rfl)
  intro clause member
  simp only [sparseInventory,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨_,_,record,record⟩
  · exact ⟨_,_,tuple,tuple⟩
  · exact ⟨_,_,variant,variant⟩
  · exact ⟨_,_,fn,fn⟩

theorem sparse_completed_decoded :
    decodeStore (completedStore sparseGraph identityReferences sparseInventory).1
      identityReferences sparseInventory =
        some [⟨.value,1,1⟩,⟨.value,2,2⟩,⟨.value,3,3⟩,⟨.value,4,4⟩] := rfl

theorem sparse_completed_prefix_and_valid :
    Extends sparseGraph (completedStore sparseGraph identityReferences sparseInventory).1 ∧
      (completedStore sparseGraph identityReferences sparseInventory).1.Valid :=
  ⟨(completedStore_correct sparse_valid sparse_inventory_lawful).1,
    (completedStore_correct sparse_valid sparse_inventory_lawful).2.1⟩

theorem sparse_cycle_preserved :
    (completedStore sparseGraph identityReferences sparseInventory).1.lookup .value 4 =
      some (.function 4 0 0 4) := rfl

theorem lattice_completion_unsupported (graph : Graph) (refs : References) {k} (a b : Term k) :
    completeTerm graph refs (.union a b) = none ∧
      completeTerm graph refs (.intersection a b) = none := ⟨rfl,rfl⟩

end YulangClosure.SimpleSub.RegularCompletion
