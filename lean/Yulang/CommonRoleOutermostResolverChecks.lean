import Yulang.CommonRoleOutermostResolver

/-!
Execution checks of the conditional outer protocol, **not** specification
conformance cases. The artificial two-request protocol below is not a
source interval propagator. Its duplicated child tests that code generation
preserves an entire where list (including duplicates), builds a finite
dictionary, and can actually execute proof-directed recursion.
-/
namespace Yulang.CommonRoleOutermostResolverChecks

open CommonRoleOutermostResolver

inductive Rule : Bool → Frontier Bool → Prop where
  | leaf : Rule false (.selected 0 [])
  | root : Rule true (.selected 1 [false, false])

def frontier : Bool → Frontier Bool
  | false => .selected 0 []
  | true => .selected 1 [false, false]

def protocol : Protocol Bool := ⟨frontier, Rule⟩

theorem frontier_exact : FrontierExact protocol := by
  intro request proposed
  constructor
  · intro computed
    cases request <;> cases computed
    · exact .leaf
    · exact .root
  · intro derivation
    cases derivation <;> rfl

theorem leaf_accessible : Acc (Child Rule) false := by
  constructor
  rintro child ⟨key, children, selected, member⟩
  cases selected
  cases member

theorem root_accessible : Acc (Child Rule) true := by
  constructor
  rintro child ⟨key, children, selected, member⟩
  cases selected
  have same : child = false := by simpa using member
  subst child
  exact leaf_accessible

theorem duplicate_children_retained :
    resolve protocol frontier_exact true root_accessible =
      .selected 1 [.selected 0 [], .selected 0 []] := by
  apply (resolve_tree_exact_of_frontier_exact protocol frontier_exact true root_accessible _).mpr
  exact .selected Rule.root (.cons (.selected Rule.leaf .nil)
    (.cons (.selected Rule.leaf .nil) .nil))

theorem complete_finite_dictionary :
    classification (resolve protocol frontier_exact true root_accessible) =
      .selected (.node 1 [.node 0 [], .node 0 []]) := by
  rw [duplicate_children_retained]
  rfl

theorem independent_classification :
    Classify Rule true (.selected (.node 1 [.node 0 [], .node 0 []])) :=
  (resolve_exact_of_frontier_exact protocol frontier_exact true root_accessible _).mp
    complete_finite_dictionary

/- This is intentionally not named X6 or X8–X12. It checks executable
dictionary construction, not graph propagation or source conformance. -/
#eval classification (resolve protocol frontier_exact true root_accessible)

end Yulang.CommonRoleOutermostResolverChecks
