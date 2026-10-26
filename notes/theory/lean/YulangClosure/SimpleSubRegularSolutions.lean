import YulangClosure.SimpleSubConstraintSyntax

/-!
Finite certificates construct guarded regular structural subtype solutions.

The semantic relation is agreement at every finite structural unfolding depth;
the executable checker only checks one-step closure of a finite pair table.
Their connection is proved, without a supplied solution or preservation law.

Function has all four native ports (-,-,+,+). Records and variants have finite
whole field/alternative lists, with exact labels, optional bits, tags, payload
arity and order. Child references may cycle through structural constructors.
There are no alias nodes, bare variable cycles, or union/intersection cycles:
the guarded-hypothesis discipline of the reference paper is not discarded.

This is a proof certificate construction, not an added runtime requirement or
Rust correspondence theorem. Native no-error/admission success, faithful graph
and certificate extraction, ordinary versus unifying coalescing, complete
Call/effect meaning and original source inference remain separate obligations.
-/
namespace YulangClosure.SimpleSub.Regular

structure Field where
  label : Nat
  optional : Bool
  child : Nat
  deriving DecidableEq, Repr

structure Alternative where
  tag : Nat
  payloads : List Nat
  deriving DecidableEq, Repr

inductive Node : Kind → Type where
  | atom {k} (identity : Nat) : Node k
  | bottom {k} : Node k
  | top {k} : Node k
  | function (argument argumentEffect resultEffect result : Nat) : Node .value
  | record (fields : List Field) : Node .value
  | tuple (elements : List Nat) : Node .value
  | variant (alternatives : List Alternative) : Node .value
  deriving Repr

/-- Two finite node tables; kind is never inferred from an untyped integer. -/
abbrev Graph := (k : Kind) → List (Node k)

def lookupList {α : Type} : List α → Nat → Option α
  | [], _ => none
  | head :: _, 0 => some head
  | _ :: tail, index + 1 => lookupList tail index

def Graph.lookup (graph : Graph) (k : Kind) (identity : Nat) : Option (Node k) :=
  lookupList (graph k) identity

structure Reference where
  kind : Kind
  identity : Nat
  deriving DecidableEq, Repr

def Node.references {k} : Node k → List Reference
  | .atom _ | .bottom | .top => []
  | .function a ae re r => [⟨.value, a⟩, ⟨.effect, ae⟩, ⟨.effect, re⟩, ⟨.value, r⟩]
  | .record fields => fields.map (fun field => ⟨.value, field.child⟩)
  | .tuple elements => elements.map (fun child => ⟨.value, child⟩)
  | .variant alternatives =>
      alternatives.flatMap (fun alternative => alternative.payloads.map (fun child => ⟨.value, child⟩))

def Node.uniqueLabels {k} : Node k → Prop
  | .record fields => (fields.map Field.label).Nodup
  | .variant alternatives => (alternatives.map Alternative.tag).Nodup
  | _ => True

instance {k} (node : Node k) : Decidable node.uniqueLabels := by
  cases node <;> simp only [Node.uniqueLabels] <;> infer_instance

def Reference.Exists (graph : Graph) (reference : Reference) : Prop :=
  ∃ node, graph.lookup reference.kind reference.identity = some node

def Node.Valid (graph : Graph) {k} (node : Node k) : Prop :=
  node.uniqueLabels ∧ ∀ reference, reference ∈ node.references → reference.Exists graph

def Graph.Valid (graph : Graph) : Prop :=
  ∀ k node, node ∈ graph k → node.Valid graph

def checkReference (graph : Graph) (reference : Reference) : Bool :=
  (graph.lookup reference.kind reference.identity).isSome

def checkNode (graph : Graph) {k} (node : Node k) : Bool :=
  decide node.uniqueLabels && node.references.all (checkReference graph)

def checkGraph (graph : Graph) : Bool :=
  (graph .value).all (checkNode graph) && (graph .effect).all (checkNode graph)

theorem checkReference_iff (graph : Graph) (reference : Reference) :
    checkReference graph reference = true ↔ reference.Exists graph := by
  cases h : graph.lookup reference.kind reference.identity <;>
    simp [checkReference, Reference.Exists, h]

theorem checkNode_iff (graph : Graph) {k} (node : Node k) :
    checkNode graph node = true ↔ node.Valid graph := by
  simp [checkNode, Node.Valid, List.all_eq_true, checkReference_iff]

theorem checkGraph_iff (graph : Graph) : checkGraph graph = true ↔ graph.Valid := by
  simp only [checkGraph, Bool.and_eq_true, List.all_eq_true, checkNode_iff]
  constructor
  · rintro ⟨hv, he⟩ k
    cases k
    · exact hv
    · exact he
  · intro h
    exact ⟨h .value, h .effect⟩

theorem lookupList_mem {α : Type} {items : List α} {index : Nat} {item : α}
    (found : lookupList items index = some item) : item ∈ items := by
  induction items generalizing index with
  | nil => cases found
  | cons head tail ih =>
      cases index with
      | zero =>
          have same : head = item := Option.some.inj found
          subst item
          exact List.mem_cons_self
      | succ index => exact List.mem_cons_of_mem _ (ih found)

theorem Graph.valid_lookup {graph : Graph} (valid : graph.Valid) {k : Kind}
    {identity : Nat} {node : Node k} (found : graph.lookup k identity = some node) :
    node.Valid graph :=
  valid k node (lookupList_mem found)

structure Comparison where
  kind : Kind
  lower : Nat
  upper : Nat
  deriving DecidableEq, Repr

def pairLists (kind : Kind) : List Nat → List Nat → Option (List Comparison)
  | [], [] => some []
  | lower :: lowers, upper :: uppers =>
      (pairLists kind lowers uppers).map (⟨kind, lower, upper⟩ :: ·)
  | _, _ => none

def recordPairs : List Field → List Field → Option (List Comparison)
  | [], [] => some []
  | lower :: lowers, upper :: uppers =>
      if lower.label = upper.label ∧ lower.optional = upper.optional then
        (recordPairs lowers uppers).map (⟨.value, lower.child, upper.child⟩ :: ·)
      else none
  | _, _ => none

def variantPairs : List Alternative → List Alternative → Option (List Comparison)
  | [], [] => some []
  | lower :: lowers, upper :: uppers =>
      if lower.tag = upper.tag then do
        let payloadPairs ← pairLists .value lower.payloads upper.payloads
        let remainingPairs ← variantPairs lowers uppers
        pure (payloadPairs ++ remainingPairs)
      else none
  | _, _ => none

/-- One structural layer. Both endpoints must exist, even for bottom/top.
Every recursively demanded comparison crosses a structural constructor. -/
def expandNodes : {k : Kind} → Node k → Node k → Option (List Comparison)
  | _, .bottom, _ => some []
  | _, _, .top => some []
  | _, .atom lower, .atom upper => if lower = upper then some [] else none
  | .value, .function a ae re r, .function a' ae' re' r' =>
      some [⟨.value, a', a⟩, ⟨.effect, ae', ae⟩, ⟨.effect, re, re'⟩, ⟨.value, r, r'⟩]
  | .value, .record lower, .record upper => recordPairs lower upper
  | .value, .tuple lower, .tuple upper => pairLists .value lower upper
  | .value, .variant lower, .variant upper => variantPairs lower upper
  | _, _, _ => none

def expand (graph : Graph) (pair : Comparison) : Option (List Comparison) :=
  match graph.lookup pair.kind pair.lower, graph.lookup pair.kind pair.upper with
  | some lower, some upper => expandNodes lower upper
  | _, _ => none

theorem expand_function {graph : Graph} {lower upper a ae re r a' ae' re' r' : Nat}
    (left : graph.lookup .value lower = some (.function a ae re r))
    (right : graph.lookup .value upper = some (.function a' ae' re' r')) :
    expand graph ⟨.value, lower, upper⟩ =
      some [⟨.value, a', a⟩, ⟨.effect, ae', ae⟩, ⟨.effect, re, re'⟩, ⟨.value, r, r'⟩] := by
  simp [expand, left, right, expandNodes]

theorem expand_record {graph : Graph} {lower upper : Nat} {fields fields' : List Field}
    (left : graph.lookup .value lower = some (.record fields))
    (right : graph.lookup .value upper = some (.record fields')) :
    expand graph ⟨.value, lower, upper⟩ = recordPairs fields fields' := by
  simp [expand, left, right, expandNodes]

theorem expand_tuple {graph : Graph} {lower upper : Nat} {items items' : List Nat}
    (left : graph.lookup .value lower = some (.tuple items))
    (right : graph.lookup .value upper = some (.tuple items')) :
    expand graph ⟨.value, lower, upper⟩ = pairLists .value items items' := by
  simp [expand, left, right, expandNodes]

theorem expand_variant {graph : Graph} {lower upper : Nat}
    {alternatives alternatives' : List Alternative}
    (left : graph.lookup .value lower = some (.variant alternatives))
    (right : graph.lookup .value upper = some (.variant alternatives')) :
    expand graph ⟨.value, lower, upper⟩ = variantPairs alternatives alternatives' := by
  simp [expand, left, right, expandNodes]

theorem expand_endpoints_exist {graph : Graph} {pair : Comparison} {children : List Comparison}
    (expanded : expand graph pair = some children) :
    (∃ lower, graph.lookup pair.kind pair.lower = some lower) ∧
      (∃ upper, graph.lookup pair.kind pair.upper = some upper) := by
  cases hl : graph.lookup pair.kind pair.lower with
  | none => simp [expand, hl] at expanded
  | some lower =>
      cases hu : graph.lookup pair.kind pair.upper with
      | none => simp [expand, hl, hu] at expanded
      | some upper => exact ⟨⟨lower, rfl⟩, ⟨upper, rfl⟩⟩

def Layer (graph : Graph) (relation : Comparison → Prop) (pair : Comparison) : Prop :=
  ∃ children, expand graph pair = some children ∧ ∀ child, child ∈ children → relation child

def Approx (graph : Graph) : Nat → Comparison → Prop
  | 0, _ => True
  | depth + 1, pair => Layer graph (Approx graph depth) pair

/-- Independent, potentially infinite regular structural interpretation.
It is not defined by certificate acceptance or a finite-Term valuation. -/
def RegularSub (graph : Graph) (pair : Comparison) : Prop :=
  ∀ depth, Approx graph depth pair

theorem Layer.mono {graph : Graph} {left right : Comparison → Prop}
    (included : ∀ pair, left pair → right pair) {pair : Comparison}
    (h : Layer graph left pair) : Layer graph right pair := by
  rcases h with ⟨children, expanded, closed⟩
  exact ⟨children, expanded, fun child hc => included child (closed child hc)⟩

/-- Every postfixed relation is included in the independent all-depth relation. -/
theorem coinduction {graph : Graph} {relation : Comparison → Prop}
    (postfixed : ∀ pair, relation pair → Layer graph relation pair) :
    ∀ pair, relation pair → RegularSub graph pair := by
  intro pair hp depth
  induction depth generalizing pair with
  | zero => trivial
  | succ depth ih =>
      exact Layer.mono (fun child hc => ih child hc) (postfixed pair hp)

/-- Deterministic finite branching lets all finite approximants unfold into
one shared child list. No new witness is selected separately at each depth. -/
theorem regular_unfold {graph : Graph} {pair : Comparison} :
    RegularSub graph pair ↔ Layer graph (RegularSub graph) pair := by
  constructor
  · intro h
    rcases h 1 with ⟨children, expanded, _⟩
    refine ⟨children, expanded, ?_⟩
    intro child hc depth
    rcases h (depth + 1) with ⟨other, expandedOther, related⟩
    have same : other = children := Option.some.inj (expandedOther.symm.trans expanded)
    subst other
    exact related child hc
  · rintro ⟨children, expanded, related⟩ depth
    cases depth with
    | zero => trivial
    | succ depth => exact ⟨children, expanded, fun child hc => related child hc depth⟩

theorem regular_no_failed_expansion {graph : Graph} {pair : Comparison}
    (failed : expand graph pair = none) : ¬ RegularSub graph pair := by
  intro h
  rcases regular_unfold.mp h with ⟨children, expanded, _⟩
  rw [failed] at expanded
  cases expanded

theorem regular_of_leaf {graph : Graph} {pair : Comparison}
    (expanded : expand graph pair = some []) : RegularSub graph pair := by
  apply regular_unfold.mpr
  exact ⟨[], expanded, fun child hc => by cases hc⟩

abbrev Certificate := List Comparison

def checkPair (graph : Graph) (certificate : Certificate) (pair : Comparison) : Bool :=
  match expand graph pair with
  | none => false
  | some children => children.all (fun child => decide (child ∈ certificate))

def checkCertificate (graph : Graph) (certificate : Certificate) : Bool :=
  certificate.all (checkPair graph certificate)

def accepts (graph : Graph) (certificate : Certificate) (demands : List Comparison) : Bool :=
  checkGraph graph && checkCertificate graph certificate &&
    demands.all (fun pair => decide (pair ∈ certificate))

theorem checkPair_iff (graph : Graph) (certificate : Certificate) (pair : Comparison) :
    checkPair graph certificate pair = true ↔
      Layer graph (fun child => child ∈ certificate) pair := by
  cases h : expand graph pair with
  | none => simp [checkPair, Layer, h]
  | some children => simp [checkPair, Layer, h, List.all_eq_true]

theorem checkCertificate_iff (graph : Graph) (certificate : Certificate) :
    checkCertificate graph certificate = true ↔
      ∀ pair, pair ∈ certificate → Layer graph (fun child => child ∈ certificate) pair := by
  simp only [checkCertificate, List.all_eq_true, checkPair_iff]

/-- Finite executable closure checking constructs every certified regular
comparison. The conclusion is not a premise of any checker branch. -/
theorem certificate_sound {graph : Graph} {certificate : Certificate}
    (checked : checkCertificate graph certificate = true) :
    ∀ pair, pair ∈ certificate → RegularSub graph pair :=
  coinduction ((checkCertificate_iff graph certificate).mp checked)

theorem accepts_iff (graph : Graph) (certificate : Certificate) (demands : List Comparison) :
    accepts graph certificate demands = true ↔
      graph.Valid ∧ checkCertificate graph certificate = true ∧
        ∀ pair, pair ∈ demands → pair ∈ certificate := by
  simp [accepts, List.all_eq_true, checkGraph_iff, and_assoc]

theorem accepted_graph_valid {graph : Graph} {certificate : Certificate}
    {demands : List Comparison} (accepted : accepts graph certificate demands = true) :
    graph.Valid := ((accepts_iff graph certificate demands).mp accepted).1

/-- No model/valuation is supplied: accepted finite evidence constructs the
same graph's regular structural solution for every demanded comparison. -/
theorem accepted_demands_sound {graph : Graph} {certificate : Certificate}
    {demands : List Comparison} (accepted : accepts graph certificate demands = true) :
    ∀ pair, pair ∈ demands → RegularSub graph pair := by
  rcases (accepts_iff graph certificate demands).mp accepted with ⟨_, checked, covered⟩
  exact fun pair hp => certificate_sound checked pair (covered pair hp)

theorem accepted_all_depths {graph : Graph} {certificate : Certificate}
    {demands : List Comparison} (accepted : accepts graph certificate demands = true) :
    ∀ depth pair, pair ∈ demands → Approx graph depth pair :=
  fun depth pair hp => accepted_demands_sound accepted pair hp depth

/-- A single concrete postfixed relation supplies all demands together.
This is shared structural pair evidence, not a replacement for the original
source-scoped joint Call/effect strategy. -/
theorem accepted_joint_relation {graph : Graph} {certificate : Certificate}
    {demands : List Comparison} (accepted : accepts graph certificate demands = true) :
    graph.Valid ∧ ∃ relation : Comparison → Prop,
      (∀ pair, relation pair → Layer graph relation pair) ∧
      (∀ pair, pair ∈ demands → relation pair) ∧
      (∀ pair, relation pair → RegularSub graph pair) := by
  rcases (accepts_iff graph certificate demands).mp accepted with ⟨valid, checked, covered⟩
  exact ⟨valid, (fun pair => pair ∈ certificate),
    (checkCertificate_iff graph certificate).mp checked, covered, certificate_sound checked⟩

theorem accepted_demand_endpoints {graph : Graph} {certificate : Certificate}
    {demands : List Comparison} (accepted : accepts graph certificate demands = true)
    {pair : Comparison} (demanded : pair ∈ demands) :
    (∃ lower, graph.lookup pair.kind pair.lower = some lower) ∧
      (∃ upper, graph.lookup pair.kind pair.upper = some upper) := by
  rcases regular_unfold.mp (accepted_demands_sound accepted pair demanded) with ⟨children, h, _⟩
  exact expand_endpoints_exist h

theorem missing_demand_rejected {graph : Graph} {certificate : Certificate}
    {demands : List Comparison} {pair : Comparison}
    (demanded : pair ∈ demands) (missing : pair ∉ certificate) :
    accepts graph certificate demands = false := by
  cases h : accepts graph certificate demands with
  | false => rfl
  | true => exact False.elim (missing (((accepts_iff graph certificate demands).mp h).2.2 pair demanded))

theorem broken_pair_rejected {graph : Graph} {certificate : Certificate} {pair : Comparison}
    (retained : pair ∈ certificate) (failed : expand graph pair = none) :
    checkCertificate graph certificate = false := by
  cases h : checkCertificate graph certificate with
  | false => rfl
  | true => exact False.elim (regular_no_failed_expansion failed (certificate_sound h pair retained))

/-! A genuine shared cyclic certificate. The root Functions return records;
one field returns through tuple/variant payloads to the root Functions, and
another field recursively refers to its record. Argument and both effect
comparisons use bottom/top in directions forced by the four-port variance. -/

def mixedCyclicGraph : Graph
  | .value =>
      [.function 2 0 1 4, .function 3 1 0 5, .top, .bottom,
       .record [⟨10, false, 6⟩, ⟨11, true, 4⟩],
       .record [⟨10, false, 7⟩, ⟨11, true, 5⟩],
       .tuple [8], .tuple [9], .variant [⟨12, [0]⟩], .variant [⟨12, [1]⟩]]
  | .effect => [.top, .bottom]

def mixedCyclicCertificate : Certificate :=
  [⟨.value, 0, 1⟩, ⟨.value, 3, 2⟩, ⟨.effect, 1, 0⟩,
   ⟨.value, 4, 5⟩, ⟨.value, 6, 7⟩, ⟨.value, 8, 9⟩]

theorem mixedCyclic_accepted :
    accepts mixedCyclicGraph mixedCyclicCertificate [⟨.value, 0, 1⟩] = true := rfl

theorem mixedCyclic_regular : RegularSub mixedCyclicGraph ⟨.value, 0, 1⟩ :=
  accepted_demands_sound mixedCyclic_accepted _ (by simp)

theorem mixedCyclic_all_depths (depth : Nat) :
    Approx mixedCyclicGraph depth ⟨.value, 0, 1⟩ := mixedCyclic_regular depth

/-- Omitting the effect comparison invalidates the finite certificate,
although every value comparison has been retained. -/
theorem mixedCyclic_missing_effect_rejected :
    accepts mixedCyclicGraph
      [⟨.value, 0, 1⟩, ⟨.value, 3, 2⟩, ⟨.value, 4, 5⟩,
       ⟨.value, 6, 7⟩, ⟨.value, 8, 9⟩] [⟨.value, 0, 1⟩] = false := rfl

theorem mixedCyclic_reverse_rejected :
    accepts mixedCyclicGraph
      [⟨.value, 1, 0⟩, ⟨.value, 2, 3⟩, ⟨.effect, 0, 1⟩,
       ⟨.value, 5, 4⟩, ⟨.value, 7, 6⟩, ⟨.value, 9, 8⟩]
      [⟨.value, 1, 0⟩] = false := rfl

def optionalMismatchGraph : Graph
  | .value => [.record [⟨7, false, 0⟩], .record [⟨7, true, 1⟩]]
  | .effect => []

theorem optional_mismatch_rejected :
    accepts optionalMismatchGraph [⟨.value, 0, 1⟩] [⟨.value, 0, 1⟩] = false := rfl

def danglingGraph : Graph
  | .value => [.bottom, .function 99 0 0 0]
  | .effect => [.atom 0]

/-- Even bottom's immediate subtype rule cannot hide an invalid graph edge. -/
theorem dangling_graph_rejected :
    accepts danglingGraph [⟨.value, 0, 1⟩] [⟨.value, 0, 1⟩] = false := rfl

end YulangClosure.SimpleSub.Regular
