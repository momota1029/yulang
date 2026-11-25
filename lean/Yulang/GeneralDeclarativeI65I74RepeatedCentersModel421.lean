import Yulang.GeneralDeclarativeI65I74RepeatedCentersPriority421

namespace Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
open GeneralDeclarativeI65
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_trans)
open CommonNominalFullCarrier (Equivalent variant)

/-- The exact later center equation preserves this very assignment if
the observed ground payload types agree. This is semantic compatibility,
not a claim that the checker reads a missing row as successful. -/
theorem exact_post_equation_preserves_every_compatible_current_model421 {p} {a : Choice p}
    (after : Compared a) (agree : after.firstCenter.color = after.secondCenter.color)
    (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment) :
    Models (appendFacts p.state.core.current.ordinary [a.tie]) m.assignment := by
  apply (model_append m.assignment).mpr
  refine ⟨fit,?_⟩
  intro row seen
  have h : row = a.tie := by simpa using seen
  subst row
  have first := original_center_type_in_same_model421 after.firstCenter m fit
  have second := original_center_type_in_same_model421 after.secondCenter m fit
  change Equivalent (m.assignment a.second.center).1 (m.assignment a.first.center).1
  exact eqv_trans second (agree ▸ ⟨first.2,first.1⟩)

/-- Existence of one fitting pre-state model rules out a retained
canonical tie when the two actual centers have incompatible types.
The implemented witness still explicitly checks absence. -/
theorem every_incompatible_fitting_snapshot_lacks_the_exact_tie421 {p} {a : Choice p}
    (after : Compared a) (disagree : after.firstCenter.color ≠ after.secondCenter.color)
    (m : I72.Model) (fit : Models p.state.core.current.ordinary m.assignment) :
    a.tie ∉ p.state.core.current.ordinary.equations := by
  intro tied
  have first := original_center_type_in_same_model421 after.firstCenter m fit
  have second := original_center_type_in_same_model421 after.secondCenter m fit
  have eq := fit.2 _ tied
  change Equivalent (m.assignment a.second.center).1 (m.assignment a.first.center).1 at eq
  exact distinct_scalars_in_same_tick_cannot_be_subtypes421 (different_colors421 disagree)
    (CommonNominalFullCarrier.subtype_trans first.2
      (CommonNominalFullCarrier.subtype_trans eq.2 second.1))

end Yulang.GeneralDeclarativeI65.I72.RepeatedCenters421
