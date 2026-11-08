import Yulang.FiniteWorklist

/-!
# Finite structural type graphs for role inspection

Graph references are actual finite node indices. `structural` nodes describe
anonymous constructors; `nominal` nodes store only a name and explicit type
arguments, never the body of a named declaration. Edges through nominal type
arguments remain visible: an anonymous recursive node can reach itself through
one. An unresolved node has no currently known constructor. This is a graph
component, not yet the full interval role resolver.
-/
namespace Yulang.CommonRoleRegularGraph

inductive Node (n : Nat) where
  | unresolved
  | scalar (name : Nat)
  | structural (constructor : Nat) (children : List (Fin n))
  | nominal (name : Nat) (arguments : List (Fin n))
  deriving DecidableEq, Repr

abbrev Graph (n : Nat) := Fin n → Node n

def successors (graph : Graph n) (node : Fin n) : List (Fin n) :=
  match graph node with
  | .structural _ children => children
  | .nominal _ arguments => arguments
  | .unresolved | .scalar _ => []

/-- The `n` worklist capacity is the complete finite set of node identities,
not a cutoff on paths or on the depth of a type. -/
def returnsTo (graph : Graph n) (root next : Fin n) : Bool :=
  decide (root ∈ FiniteWorklist.reachable (successors graph) n next)

def recursiveAt (graph : Graph n) (root : Fin n) : Bool :=
  match graph root with
  | .structural _ children => children.any (returnsTo graph root)
  | .unresolved | .scalar _ | .nominal _ _ => false

/-- Independent graph property: the reached root is an anonymous constructor
and there is a nonempty path from it back to the same node identity. -/
def StructuralCycleAt (graph : Graph n) (root : Fin n) : Prop :=
  ∃ constructor children, graph root = .structural constructor children ∧
    ∃ next ∈ children, FiniteWorklist.Path (successors graph) next root

theorem returns_to_exact (graph : Graph n) (root next : Fin n) :
    returnsTo graph root next = true ↔ FiniteWorklist.Path (successors graph) next root := by
  simp only [returnsTo, decide_eq_true_eq]
  apply FiniteWorklist.reachable_exact (successors graph) n (List.finRange n)
  · exact List.mem_finRange
  · simp

theorem recursive_at_exact (graph : Graph n) (root : Fin n) :
    recursiveAt graph root = true ↔ StructuralCycleAt graph root := by
  cases found : graph root with
  | unresolved => simp [recursiveAt, found, StructuralCycleAt]
  | scalar name => simp [recursiveAt, found, StructuralCycleAt]
  | nominal name arguments => simp [recursiveAt, found, StructuralCycleAt]
  | structural constructor children =>
      simp only [recursiveAt, found, List.any_eq_true, returns_to_exact]
      constructor
      · rintro ⟨next, member, path⟩
        exact ⟨constructor, children, found, next, member, path⟩
      · rintro ⟨other, otherChildren, equal, next, member, path⟩
        have sameChildren : children = otherChildren := (Node.structural.inj (found.symm.trans equal)).2
        subst otherChildren
        exact ⟨next, member, path⟩

theorem nominal_not_recursive (graph : Graph n) (root : Fin n) (name : Nat)
    (arguments : List (Fin n)) (found : graph root = .nominal name arguments) :
    recursiveAt graph root = false := by simp [recursiveAt, found]

theorem unresolved_not_recursive (graph : Graph n) (root : Fin n)
    (found : graph root = .unresolved) : recursiveAt graph root = false := by
  simp [recursiveAt, found]

end Yulang.CommonRoleRegularGraph
