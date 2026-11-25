import Yulang.GeneralDeclarativeI65I74ClosedResidualCoherence415

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
open CommonNominalFullCarrier (record Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans record_congr)
open GeneralDeclarativeHead320 (Equation)

/-- The semantic relationship is derivable from the original closed
row and actual residual row alone, with no premise asserting the
split. The executable entry *also* checks the retained split's
unique name to avoid choosing an equal-looking variable itself. -/
theorem split_is_semantically_derived_from_closed_source415 {s : I72.State}
    {root x ix y sy residual : Nat}
    (original : (⟨root,wholeExpr x ix y sy⟩ : Equation) ∈ s.core.current.ordinary.equations)
    (existingRemainder : (⟨residual,residualExpr y sy⟩ : Equation) ∈ s.core.current.ordinary.equations)
    (integer : OpenTail414.intRow ix ∈ s.core.current.ordinary.equations)
    (m : I72.Model) (fit : Fits s m) :
    Equivalent (m.assignment root).1 (record x (.base .int) (m.assignment residual).1) := by
  have originalMeaning := fit.1.1.2 _ original
  change Equivalent (m.assignment root).1
    (record x (m.assignment ix).1 (record y (m.assignment sy).1 .emptyRecord)) at originalMeaning
  have sameInt := fit.1.1.2 _ integer
  change Equivalent (m.assignment ix).1 (.base .int) at sameInt
  have tail := fit.1.1.2 _ existingRemainder
  change Equivalent (m.assignment residual).1 (record y (m.assignment sy).1 .emptyRecord) at tail
  exact eqv_trans originalMeaning (record_congr _ sameInt ⟨tail.2,tail.1⟩)

theorem visible_removed_and_retained_projections_agree415 {s q} (a : ClosedRows s q)
    (m : I72.Model) (fit : Fits s m) :
    Equivalent (m.assignment a.root).1
      (record a.x (.base .int) (record a.y (.base .str) .emptyRecord)) :=
  eqv_trans (split_is_semantically_derived_from_closed_source415 a.whole a.retainedResidual a.integer m fit)
    (record_congr _ (eqv_refl _) (exact_same_model_residual_value415 a m fit))

end Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
