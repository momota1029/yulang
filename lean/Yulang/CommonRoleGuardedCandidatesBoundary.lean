import Yulang.CommonRoleGuardedEquations
import Yulang.CommonRoleSupportSearchBoundary

/-! Regression for the actual first-hit omission from cycles22/23.
The guarded carrier keeps the later capture candidate at both observations.
This is not a decision to select that candidate or accept the source program. -/
namespace Yulang.CommonRoleGuardedCandidatesBoundary
open CommonRoleFirstHitSupportBoundary
open CommonRoleSourceWorklist (rootNode)
open CommonRoleGuardedCandidates

/-- Retain all alternatives as metadata, without a language choice policy. -/
def allEnabled (_ : CommonRoleMaterializedDomain.SourceRequest 1)
    (_ : CommonRoleSettledSyntax.Declaration) : Bool := true

/-- The checked later capture remains an active individual candidate after
learning int, even though first-hit production changes to the earlier literal. -/
theorem capture_children_survive :
    child ∈ candidateNext capture before root ∧ child ∈ candidateNext capture after root := by
  decide

/-- The same source child is present in both recomputed all-enabled closures.
This repairs the concrete first-hit omission in the metadata carrier only. -/
theorem child_collected_both :
    childNode ∈ collect registry root allEnabled before ∧
    childNode ∈ collect registry root allEnabled after := by
  constructor
  · apply (collect_exact registry root allEnabled before childNode).mpr
    exact .step .root ⟨capture, by decide, rfl, capture_children_survive.1⟩
  · apply (collect_exact registry root allEnabled after childNode).mpr
    exact .step .root ⟨capture, by decide, rfl, capture_children_survive.2⟩

/-- The observation really can arise from the checked associated declaration
in cycle23, not only from an arbitrary synthetic ordinary equality. -/
theorem actual_associated_child_retained :
    childNode ∈ collect registry root allEnabled (CommonRoleSupportSearchBoundary.decode [0]) := by
  rw [CommonRoleSupportSearchBoundary.decode_singleton]
  exact child_collected_both.2

end Yulang.CommonRoleGuardedCandidatesBoundary
