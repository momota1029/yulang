import Yulang.CommonRoleDiagnosticTree
import Yulang.CommonRoleFirstHitSupportBoundary

/-! A retained partial branch after real ordinary narrowing. This is a diagnostic
regression, not a decision to select the capture declaration over another match. -/
namespace Yulang.CommonRoleDiagnosticTreeCheck
open CommonRoleFirstHitSupportBoundary
open CommonRoleCorrelatedPaths (start extend)
open CommonRoleGlobalChoices (Table)
open CommonRoleDiagnosticTree

def partialTable : Table registry root := [(start registry root, capture)]

/-- The candidate has a child with no table choice; that obligation stays in the
actual constructed tree after narrowing, even though the old first-hit source
producer lost it. No successful-child premise is required. -/
theorem missing_child_after_narrowing :
    Visit registry root (diagnose registry root partialTable after)
      (extend registry root (start registry root) capture childNode) ∧
    ¬ ∃ e, (extend registry root (start registry root) capture childNode,e) ∈ partialTable := by
  apply unresolved_child_retained registry root partialTable after
    (start registry root) capture .root
  · simp [registry]
  · simp [partialTable]
  · exact (CommonRoleGuardedEquations.candidate_exact ..).mp (by decide)
  · decide
  · simp [partialTable, extend, start]

/-- This partial tree is useful evidence even though it cannot satisfy the
strong total-certificate contract used by the finite stable search. -/
theorem partial_not_valid : ¬ CommonRoleGlobalChoices.Valid registry root after partialTable := by
  intro h
  exact missing_child_after_narrowing.2
    (valid_tree_total registry root partialTable after h _ missing_child_after_narrowing.1)

end Yulang.CommonRoleDiagnosticTreeCheck
