import YulangClosure.SimpleSubRegularPublication

/-! Append-only extensions preserve existing regular graph evidence. No acyclicity
assumption is made, and no existing identity or node is rewritten. -/
namespace YulangClosure.SimpleSub.RegularExtension
open Regular RegularPublication

/-- Both kind tables retain their exact old prefix. -/
def Extends (source target : Graph) : Prop :=
  ∀ k, ∃ suffix, target k = source k ++ suffix

theorem Extends.refl (graph : Graph) : Extends graph graph :=
  fun _ => ⟨[], (List.append_nil _).symm⟩

theorem Extends.trans {a b c : Graph} (ab : Extends a b) (bc : Extends b c) : Extends a c := by
  intro k
  rcases ab k with ⟨xs,hxs⟩
  rcases bc k with ⟨ys,hys⟩
  exact ⟨xs ++ ys, by rw [hys,hxs,List.append_assoc]⟩

theorem lookupList_append_some {α} {xs : List α} {i x} (h : lookupList xs i = some x)
    (ys : List α) : lookupList (xs ++ ys) i = some x := by
  induction xs generalizing i with
  | nil => cases h
  | cons a xs ih =>
      cases i with
      | zero => exact h
      | succ i => exact ih h

theorem Extends.lookup {source target : Graph} (extension : Extends source target)
    {k i node} (h : source.lookup k i = some node) : target.lookup k i = some node := by
  rcases extension k with ⟨suffix,hs⟩
  change lookupList (target k) i = some node
  rw [hs]
  exact lookupList_append_some h suffix

theorem Extends.reference {source target : Graph} (extension : Extends source target)
    {reference : Reference} (h : reference.Exists source) : reference.Exists target := by
  rcases h with ⟨node,hn⟩
  exact ⟨node,extension.lookup hn⟩

theorem Extends.node_valid {source target : Graph} (extension : Extends source target)
    {k} {node : Node k} (h : node.Valid source) : node.Valid target :=
  ⟨h.1,fun _ hr => extension.reference (h.2 _ hr)⟩

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
    {k} {node : Node k} {i} (h : findNode source node = some i) :
    findNode target node = some i := by
  rcases extension k with ⟨suffix,hs⟩
  change findList node (target k) = some i
  rw [hs]
  exact findList_append_some h suffix

theorem Extends.expansion {source target : Graph} (extension : Extends source target)
    {pair children} (h : expand source pair = some children) : expand target pair = some children := by
  rcases expand_endpoints_exist h with ⟨⟨lower,hl⟩,⟨upper,hu⟩⟩
  simpa [expand,extension.lookup hl,extension.lookup hu] using
    (show expandNodes lower upper = some children by simpa [expand,hl,hu] using h)

theorem Extends.layer {source target : Graph} (extension : Extends source target)
    {relation pair} (h : Layer source relation pair) : Layer target relation pair := by
  rcases h with ⟨children,expanded,closed⟩
  exact ⟨children,extension.expansion expanded,closed⟩

theorem Extends.regular {source target : Graph} (extension : Extends source target)
    {pair} (h : RegularSub source pair) : RegularSub target pair := by
  apply coinduction (relation := RegularSub source) _ pair h
  intro current hc
  exact extension.layer (regular_unfold.mp hc)

theorem Extends.extrusion {source target : Graph} (extension : Extends source target)
    {pair copies} (h : Extrusion source pair copies) : Extrusion target pair copies := by
  induction h with
  | copy coordinate => exact .copy coordinate
  | same k identity present => exact .same k identity (extension.reference present)
  | structural pair parts expanded children ih =>
      exact .structural pair parts (extension.expansion expanded) ih

theorem Extends.step {source target : Graph} (extension : Extends source target)
    {ref birth before after} (h : ConstraintStep source ref birth before after) :
    ConstraintStep target ref birth before after := by
  cases h with
  | reflexive k identity rest events present =>
      exact .reflexive k identity rest events (extension.reference present)
  | decompose pair children rest events expanded =>
      exact .decompose pair children rest events (extension.expansion expanded)
  | insertLower k lower row state => exact .insertLower k lower row _
  | insertUpper k row upper state => exact .insertUpper k row upper _
  | replay k lower row upper rest events lb ub => exact .replay k lower row upper rest events lb ub
  | extrudeUpper k lower upper fresh copies rest events identity origin receiver traversal =>
      exact .extrudeUpper k lower upper fresh copies rest events identity origin receiver
        (extension.extrusion traversal)
  | extrudeLower k lower fresh upper copies rest events identity origin receiver traversal =>
      exact .extrudeLower k lower fresh upper copies rest events identity origin receiver
        (extension.extrusion traversal)
  | intrude state event selected retained qualifies actual =>
      exact .intrude _ event selected retained qualifies actual

theorem Extends.history {source target : Graph} (extension : Extends source target)
    {ref birth first last} (h : ConstraintHistory source ref birth first last) :
    ConstraintHistory target ref birth first last := by
  induction h with
  | nil state => exact .nil state
  | cons step tail ih => exact .cons (extension.step step) ih

theorem Extends.certificate {source target : Graph} (extension : Extends source target)
    {certificate} (h : checkCertificate source certificate = true) :
    checkCertificate target certificate = true := by
  apply (checkCertificate_iff _ _).mpr
  intro pair hp
  exact extension.layer ((checkCertificate_iff _ _).mp h pair hp)

theorem Extends.accepts {source target : Graph} (extension : Extends source target)
    (valid : target.Valid) {certificate demands} (h : accepts source certificate demands = true) :
    accepts target certificate demands = true := by
  rcases (accepts_iff _ _ _).mp h with ⟨_,hc,hd⟩
  exact (accepts_iff _ _ _).mpr ⟨valid,extension.certificate hc,hd⟩

theorem Extends.prepend_record {source target : Graph} (extension : Extends source target)
    {label optional field tail i} (h : prependRecord source label optional field tail = some i) :
    prependRecord target label optional field tail = some i := by
  rcases prependRecord_exact h with ⟨fields,ht,_⟩
  have hf : findNode source (.record (⟨label,optional,field⟩ :: fields)) = some i := by
    simpa [prependRecord,ht] using h
  simpa [prependRecord,extension.lookup ht] using extension.find_node hf

theorem Extends.prepend_tuple {source target : Graph} (extension : Extends source target)
    {head tail i} (h : prependTuple source head tail = some i) :
    prependTuple target head tail = some i := by
  rcases prependTuple_exact h with ⟨elements,ht,_⟩
  have hf : findNode source (.tuple (head :: elements)) = some i := by
    simpa [prependTuple,ht] using h
  simpa [prependTuple,extension.lookup ht] using extension.find_node hf

theorem Extends.prepend_variant {source target : Graph} (extension : Extends source target)
    {tag payloads tail i} (h : prependVariant source tag payloads tail = some i) :
    prependVariant target tag payloads tail = some i := by
  rcases prependVariant_exact h with ⟨elements,alternatives,hp,ht,_⟩
  have hf : findNode source (.variant (⟨tag,elements⟩ :: alternatives)) = some i := by
    simpa [prependVariant,hp,ht] using h
  simpa [prependVariant,extension.lookup hp,extension.lookup ht] using extension.find_node hf

theorem Extends.checked_reference {source target : Graph} (extension : Extends source target)
    {k i j} (h : checkedReference source k i = some j) :
    checkedReference target k i = some j := by
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
  | union a b => cases h
  | intersection a b => cases h
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

theorem Extends.decode_store {source target : Graph} (extension : Extends source target)
    {refs store pairs} (h : decodeStore source refs store = some pairs) :
    decodeStore target refs store = some pairs := by
  induction store generalizing pairs with
  | nil => exact h
  | cons clause rest ih =>
      rcases bind_some h with ⟨pair,hp,h⟩
      rcases bind_some h with ⟨pairs,hs,h⟩
      simpa [decodeStore,extension.decode_constraint hp,ih hs] using h

theorem Extends.storeSatisfied {source target : Graph} (extension : Extends source target)
    {refs store} (h : StoreSatisfied source refs store) : StoreSatisfied target refs store := by
  intro clause hc
  rcases h clause hc with ⟨pair,decoded,solved⟩
  exact ⟨pair,extension.decode_constraint decoded,extension.regular solved⟩

theorem Extends.check_store {source target : Graph} (extension : Extends source target)
    (valid : target.Valid) {refs certificate store}
    (h : checkStore source refs certificate store = true) :
    checkStore target refs certificate store = true := by
  cases decoded : decodeStore source refs store with
  | none => simp [checkStore,decoded] at h
  | some pairs =>
      have accepted : Regular.accepts source certificate pairs = true := by simpa [checkStore,decoded] using h
      simpa [checkStore,extension.decode_store decoded] using extension.accepts valid accepted

/-- A single-node append updates only its kind table. -/
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

theorem appendNode_valid {graph : Graph} (valid : graph.Valid) {k} {node : Node k}
    (nodeValid : node.Valid graph) : (appendNode graph node).Valid := by
  have extension := appendNode_extends graph node
  intro j item member
  cases k <;> cases j <;> simp only [appendNode] at member
  all_goals first
    | exact extension.node_valid (valid _ _ member)
    | rcases List.mem_append.mp member with old | new
      · exact extension.node_valid (valid _ _ old)
      · have same : item = node := by simpa using new
        subst item
        exact extension.node_valid nodeValid

end YulangClosure.SimpleSub.RegularExtension
