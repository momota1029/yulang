import Yulang.SemilinearAutomata

/-!
# Exact removal of duplicated semilinear syntax

The examples check the actual normalization output and the existing membership
and comparison APIs. No expected semantic result changes with normalization.
-/

namespace Yulang.SemilinearNormalization.Examples

open SemilinearWeights

def scalar (value : Int) : Weight 1 := fun _ => value

def repeated : List (Weight 1) := [scalar 0, scalar 2, scalar 2, scalar 0, scalar (-3), scalar 2]

theorem repeated_periods_reduce : (periods repeated).length = 2 := by decide
theorem normalized_budget_reduces : BinaryCarries.budget (periods repeated) = 5 := by decide
theorem all_zero_periods_disappear : (periods [scalar 0, scalar 0, scalar 0]).length = 0 := by decide

def repeatedComponents : Semi 1 :=
  [⟨scalar 0, repeated⟩, ⟨scalar 0, [scalar 2, scalar (-3)]⟩,
   ⟨scalar 0, [scalar (-3), scalar 2, scalar 0]⟩]

theorem permuted_duplicate_components_collapse : (normalize repeatedComponents).length = 1 := by decide

set_option maxRecDepth 100000 in
theorem redundant_syntax_keeps_membership : SemilinearDecisions.check repeatedComponents (scalar 1) = true := by
  decide

theorem zero_dimensional_generators_disappear :
    (periods [(zero : Weight 0), zero]).length = 0 := by decide

theorem zero_dimensional_duplicates_collapse :
    (normalize [⟨(zero : Weight 0), [zero]⟩, ⟨zero, []⟩]).length = 1 := by decide

theorem zero_period_component_equals_point :
    SemilinearAutomata.checkEqual [⟨(zero : Weight 0), [zero, zero]⟩] [Linear.point zero] = true := by decide

theorem large_single_period_uses_exact_candidate :
    SemilinearDecisions.checkSpan [scalar (-3), scalar 0, scalar (-3)] (scalar (-3000000)) = true := by decide

theorem empty_span_rejects_large_nonzero_without_box :
    SemilinearDecisions.checkSpan [] (scalar 1000000) = false := by decide

def plane (first second : Int) : Weight 2 := fun coordinate =>
  if coordinate.val = 0 then first else second

theorem single_period_checks_all_coordinates :
    SemilinearDecisions.checkSpan [plane 1 (-2)] (plane 4 (-8)) = true := by decide

theorem one_matching_coordinate_is_insufficient :
    SemilinearDecisions.checkSpan [plane 1 (-2)] (plane 4 (-7)) = false := by decide

def naturals : Semi 1 := [⟨scalar 0, [scalar 1]⟩]
def evens : Semi 1 := [⟨scalar 0, [scalar 2]⟩]
def odds : Semi 1 := [⟨scalar 1, [scalar 2]⟩]

theorem identical_infinite_rays_use_fast_success :
    SemilinearAutomata.checkEqual naturals naturals = true := by decide

theorem proper_infinite_ray_containment_uses_fast_success :
    SemilinearAutomata.checkSubset evens naturals = true := by decide

/-- This answer is "try the complete comparison", not rejection. The existing
`parity_union_exact` regression proves the full comparison accepts the union. -/
theorem joint_residue_coverage_uses_complete_fallback :
    SemilinearFastInclusion.check naturals (evens ++ odds) = false := by decide

end Yulang.SemilinearNormalization.Examples
