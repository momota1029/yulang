import Yulang.CommonRoleRegularGraph
import Yulang.ProducerCanonicalOpen

/-!
# Finite graph bisimulation for recursive role heads

Finite unrolling may introduce an acyclic node that denotes the same regular
tree as a cyclic node. Equality of node identities is therefore insufficient
for K2. This module computes a finite bisimulation witness using the complete
powerset of node pairs; it does not search for a substitution for an impl
head. Unresolved nodes can be related only when they have the same graph
identity. The relationship to the full Common type carrier and to incremental
graph updates remains open. In particular, this graph has no alias node:
source slots already unified by the ordinary solver must first be represented
by a shared canonical identity, with that source bridge proved separately.
-/
namespace Yulang.CommonRoleGraphBisimulation

open CommonRoleRegularGraph

abbrev Relation (n : Nat) := List (Fin n × Fin n)

def childrenRelated (relation : Relation n) : List (Fin n) → List (Fin n) → Prop
  | [], [] => True
  | first :: rest, last :: tail => (first, last) ∈ relation ∧ childrenRelated relation rest tail
  | _, _ => False

def childrenCheck (relation : Relation n) : List (Fin n) → List (Fin n) → Bool
  | [], [] => true
  | first :: rest, last :: tail => decide ((first, last) ∈ relation) && childrenCheck relation rest tail
  | _, _ => false

theorem children_check_exact (relation : Relation n) (first last : List (Fin n)) :
    childrenCheck relation first last = true ↔ childrenRelated relation first last := by
  induction first generalizing last with
  | nil => cases last <;> simp [childrenCheck, childrenRelated]
  | cons head tail ih =>
      cases last <;> simp [childrenCheck, childrenRelated, ih]

def nodeRelated (relation : Relation n) (firstNode lastNode : Fin n) : Node n → Node n → Prop
  | .unresolved, .unresolved => firstNode = lastNode
  | .scalar first, .scalar last => first = last
  | .structural first children, .structural last other =>
      first = last ∧ childrenRelated relation children other
  | .nominal first children, .nominal last other =>
      first = last ∧ childrenRelated relation children other
  | _, _ => False

def nodeCheck (relation : Relation n) (firstNode lastNode : Fin n) : Node n → Node n → Bool
  | .unresolved, .unresolved => decide (firstNode = lastNode)
  | .scalar first, .scalar last => decide (first = last)
  | .structural first children, .structural last other =>
      decide (first = last) && childrenCheck relation children other
  | .nominal first children, .nominal last other =>
      decide (first = last) && childrenCheck relation children other
  | _, _ => false

theorem node_check_exact (relation : Relation n) (firstNode lastNode : Fin n) (first last : Node n) :
    nodeCheck relation firstNode lastNode first last = true ↔
      nodeRelated relation firstNode lastNode first last := by
  cases first <;> cases last <;> simp [nodeCheck, nodeRelated, children_check_exact]

def Bisimulation (graph : Graph n) (relation : Relation n) : Prop :=
  ∀ pair ∈ relation, nodeRelated relation pair.1 pair.2 (graph pair.1) (graph pair.2)

def checkBisimulation (graph : Graph n) (relation : Relation n) : Bool :=
  relation.all fun pair => nodeCheck relation pair.1 pair.2 (graph pair.1) (graph pair.2)

theorem check_bisimulation_exact (graph : Graph n) (relation : Relation n) :
    checkBisimulation graph relation = true ↔ Bisimulation graph relation := by
  simp [checkBisimulation, Bisimulation, node_check_exact]

def allPairs (n : Nat) : Relation n :=
  (List.finRange n).flatMap fun first => (List.finRange n).map fun last => (first, last)

/-- This enumerates relations on nodes, not assignments for role heads. -/
def bisimilar (graph : Graph n) (first last : Fin n) : Bool :=
  (ProducerCanonicalOpen.sublists (allPairs n)).any fun relation =>
    decide ((first, last) ∈ relation) && checkBisimulation graph relation

def Bisimilar (graph : Graph n) (first last : Fin n) : Prop :=
  ∃ relation, relation.Sublist (allPairs n) ∧ (first, last) ∈ relation ∧ Bisimulation graph relation

theorem bisimilar_exact (graph : Graph n) (first last : Fin n) :
    bisimilar graph first last = true ↔ Bisimilar graph first last := by
  simp [bisimilar, Bisimilar, ProducerCanonicalOpen.mem_sublists_iff, check_bisimulation_exact]

theorem unresolved_bisimilar_same (graph : Graph n) (first last : Fin n)
    (firstUnknown : graph first = .unresolved) (lastUnknown : graph last = .unresolved)
    (related : bisimilar graph first last = true) : first = last := by
  obtain ⟨relation, _, member, valid⟩ := (bisimilar_exact graph first last).mp related
  have same := valid (first, last) member
  simpa [firstUnknown, lastUnknown, nodeRelated] using same

/-- Finite observations expose constructors and their children, without
unfolding named declaration bodies. -/
inductive View where
  | cut
  | unresolved
  | scalar (name : Nat)
  | structural (constructor : Nat) (children : List View)
  | nominal (name : Nat) (arguments : List View)
  deriving Repr

def observe (graph : Graph n) : Nat → Fin n → View
  | 0, _ => .cut
  | depth + 1, node =>
      match graph node with
      | .unresolved => .unresolved
      | .scalar name => .scalar name
      | .structural constructor children => .structural constructor (children.map (observe graph depth))
      | .nominal name arguments => .nominal name (arguments.map (observe graph depth))

theorem children_map_equal (relation : Relation n) (first last : List (Fin n))
    (related : childrenRelated relation first last) (read : Fin n → View)
    (preserves : ∀ a b, (a, b) ∈ relation → read a = read b) :
    first.map read = last.map read := by
  induction first generalizing last with
  | nil => cases last <;> simp_all [childrenRelated]
  | cons head tail ih =>
      cases last with
      | nil => cases related
      | cons other rest =>
          simp only [childrenRelated] at related
          simp only [List.map_cons, List.cons.injEq]
          exact ⟨preserves _ _ related.1, ih rest related.2⟩

/-- A finite bisimulation witness preserves every finite graph observation. -/
theorem bisimulation_observations (graph : Graph n) (relation : Relation n)
    (bisimulation : Bisimulation graph relation) (depth : Nat) :
    ∀ first last, (first, last) ∈ relation → observe graph depth first = observe graph depth last := by
  induction depth with
  | zero => intros; rfl
  | succ depth ih =>
      intro first last member
      have related := bisimulation (first, last) member
      cases left : graph first <;> cases right : graph last <;>
        simp only [left, right, nodeRelated] at related
      case unresolved.unresolved => simp [observe, left, right]
      case scalar.scalar a b =>
        subst b
        simp [observe, left, right]
      case structural.structural a xs b ys =>
        obtain ⟨same, children⟩ := related
        subst b
        have equal := children_map_equal relation xs ys children (observe graph depth) ih
        simp [observe, left, right, equal]
      case nominal.nominal a xs b ys =>
        obtain ⟨same, children⟩ := related
        subst b
        have equal := children_map_equal relation xs ys children (observe graph depth) ih
        simp [observe, left, right, equal]

theorem bisimilar_observations (graph : Graph n) (first last : Fin n)
    (bisimilar : bisimilar graph first last = true) (depth : Nat) :
    observe graph depth first = observe graph depth last := by
  obtain ⟨relation, _, member, bisimulation⟩ := (bisimilar_exact graph first last).mp bisimilar
  exact bisimulation_observations graph relation bisimulation depth first last member

theorem mem_all_pairs (first last : Fin n) : (first, last) ∈ allPairs n := by
  simp [allPairs]

def ObservationallyEqual (graph : Graph n) (first last : Fin n) : Prop :=
  ∀ depth, observe graph depth first = observe graph depth last

theorem observed_children_related (graph : Graph n) (first last : List (Fin n))
    (same : ∀ depth, first.map (observe graph depth) = last.map (observe graph depth))
    (relation : Relation n)
    (included : ∀ a b, ObservationallyEqual graph a b → (a, b) ∈ relation) :
    childrenRelated relation first last := by
  induction first generalizing last with
  | nil =>
      cases last with
      | nil => trivial
      | cons head tail =>
          have impossible := same 0
          simp at impossible
  | cons head tail ih =>
      cases last with
      | nil =>
          have impossible := same 0
          simp at impossible
      | cons other rest =>
          refine ⟨included head other ?_, ih rest ?_⟩
          · intro depth
            exact (List.cons.inj (same depth)).1
          · intro depth
            exact (List.cons.inj (same depth)).2

/-- On a completely determined finite graph, equality at every depth also
constructs a finite bisimulation witness. -/
theorem observations_bisimilar (graph : Graph n)
    (closed : ∀ node, graph node ≠ .unresolved) (first last : Fin n)
    (same : ObservationallyEqual graph first last) : Bisimilar graph first last := by
  classical
  let relation : Relation n := (allPairs n).filter fun pair =>
    decide (ObservationallyEqual graph pair.1 pair.2)
  have included : ∀ a b, ObservationallyEqual graph a b → (a, b) ∈ relation := by
    intro a b equal
    simp [relation, mem_all_pairs, equal]
  refine ⟨relation, List.filter_sublist, included first last same, ?_⟩
  intro pair member
  have equal : ObservationallyEqual graph pair.1 pair.2 := by
    simpa [relation] using (List.mem_filter.mp member).2
  cases left : graph pair.1 <;> cases right : graph pair.2 <;>
    simp only [nodeRelated]
  all_goals try exact False.elim (closed _ left)
  all_goals try exact False.elim (closed _ right)
  all_goals try
    have impossible := equal 1
    simp [observe, left, right] at impossible
  case scalar.scalar a b =>
    have one := equal 1
    simpa [observe, left, right] using one
  case structural.structural a xs b ys =>
    have sameHead : a = b := by
      have one := equal 1
      simpa [observe, left, right] using (View.structural.inj (by simpa [observe, left, right] using one)).1
    refine ⟨sameHead, observed_children_related graph xs ys ?_ relation included⟩
    intro depth
    have current := equal (depth + 1)
    exact (View.structural.inj (by simpa [observe, left, right] using current)).2
  case nominal.nominal a xs b ys =>
    have sameHead : a = b := by
      have one := equal 1
      simpa [observe, left, right] using (View.nominal.inj (by simpa [observe, left, right] using one)).1
    refine ⟨sameHead, observed_children_related graph xs ys ?_ relation included⟩
    intro depth
    have current := equal (depth + 1)
    exact (View.nominal.inj (by simpa [observe, left, right] using current)).2

theorem bisimilar_iff_observations (graph : Graph n)
    (closed : ∀ node, graph node ≠ .unresolved) (first last : Fin n) :
    bisimilar graph first last = true ↔ ObservationallyEqual graph first last := by
  constructor
  · intro same depth
    exact bisimilar_observations graph first last same depth
  · intro same
    exact (bisimilar_exact graph first last).mpr (observations_bisimilar graph closed first last same)

/-- A reached anonymous constructor is regular when it is bisimilar to an
anonymous constructor on an actual nonempty cycle. Nominal heads remain
outside this check and are not unfolded through declaration bodies. -/
def regularAt (graph : Graph n) (root : Fin n) : Bool :=
  match graph root with
  | .structural _ _ => recursiveAt graph root || (List.finRange n).any fun candidate =>
      recursiveAt graph candidate && bisimilar graph root candidate
  | .unresolved | .scalar _ | .nominal _ _ => false

def RegularAt (graph : Graph n) (root : Fin n) : Prop :=
  StructuralCycleAt graph root ∨
    ((∃ constructor children, graph root = .structural constructor children) ∧
      ∃ candidate, StructuralCycleAt graph candidate ∧ Bisimilar graph root candidate)

theorem regular_at_exact (graph : Graph n) (root : Fin n) :
    regularAt graph root = true ↔ RegularAt graph root := by
  cases found : graph root with
  | unresolved => simp [regularAt, RegularAt, StructuralCycleAt, found]
  | scalar name => simp [regularAt, RegularAt, StructuralCycleAt, found]
  | nominal name arguments => simp [regularAt, RegularAt, StructuralCycleAt, found]
  | structural constructor children =>
      simp [regularAt, RegularAt, found, recursive_at_exact, bisimilar_exact]

/-- Node 0 is one finite unrolling of node 1, which points to itself. -/
def unrolledGraph : Graph 2 := fun _ => .structural 0 [1]

theorem identity_cycle_misses_unrolling : recursiveAt unrolledGraph 0 = false := by
  decide +kernel

theorem bisimulation_detects_unrolling : regularAt unrolledGraph 0 = true := by
  decide +kernel

/-- A later constraint update can turn an unresolved descendant into an
edge back to the root. A previous negative snapshot must be revalidated. -/
def beforeUpdate : Graph 2 := fun index =>
  if index = 0 then .structural 0 [1] else .unresolved

def afterUpdate : Graph 2 := fun index =>
  if index = 0 then .structural 0 [1] else .structural 0 [0]

theorem graph_update_changes_regularity :
    regularAt beforeUpdate 0 = false ∧ regularAt afterUpdate 0 = true := by
  decide +kernel

/-- A known back-edge is enough even if a different child is unresolved. -/
def cycleWithUnresolved : Graph 2 := fun index =>
  if index = 0 then .structural 0 [0, 1] else .unresolved

theorem direct_cycle_with_unresolved : regularAt cycleWithUnresolved 0 = true := by
  decide +kernel

/-- An unrolled cycle can share an unresolved slot with the cyclic node.
The shared identity is stable even though the slot's eventual type is not. -/
def unrolledWithSharedUnknown : Graph 3 := fun node =>
  if node = 0 then .structural 0 [1, 2]
  else if node = 1 then .structural 0 [1, 2] else .unresolved

theorem unrolled_shared_unknown_detected :
    recursiveAt unrolledWithSharedUnknown 0 = false ∧
      regularAt unrolledWithSharedUnknown 0 = true := by
  constructor <;> decide +kernel

def twoUnknowns : Graph 2 := fun _ => .unresolved

theorem distinct_unknowns_not_bisimilar : bisimilar twoUnknowns 0 1 = false := by
  decide +kernel

/-- Named nominal heads are never classified as anonymous regular roots,
even when their explicit arguments contain a recursive graph. -/
theorem nominal_not_regular (graph : Graph n) (root : Fin n) (name : Nat)
    (arguments : List (Fin n)) (found : graph root = .nominal name arguments) :
    regularAt graph root = false := by simp [regularAt, found]

end Yulang.CommonRoleGraphBisimulation
