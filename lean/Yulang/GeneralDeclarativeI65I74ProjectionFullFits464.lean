import Yulang.GeneralDeclarativeI65I74ProjectedField464

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.NamedProjection464
open Yulang.GeneralDeclarativeI65
open PreparedDeclarations463
open RetainedFull445 (FullProblem)

/-- Explicit, independently supplied frame comparison for two FullStates.
An ordinary entailed equation is not a proof that native syntax, authored
views, or retained mixed-kind outputs agree. The retained condition is
semantic agreement of *already stored* receipts evaluated in the same model. -/
structure SameFitFrame (before after : FullState) : Prop where
  visible : before.base.core.current.visible = after.base.core.current.visible
  native : before.base.core.origins = after.base.core.origins
  retained : ∀ m : I72.Model,
    (∀ e ∈ before.retained, e.Means m) ↔ (∀ e ∈ after.retained, e.Means m)

theorem unchanged_empty_retention_frame {before after : FullState}
    (visible : before.base.core.current.visible = after.base.core.current.visible)
    (native : before.base.core.origins = after.base.core.origins)
    (h : before.retained = []) (k : after.retained = []) :
    SameFitFrame before after := by
  refine ⟨visible,native,?_⟩
  intro m
  constructor
  · intro _ e member
    rw [k] at member
    cases member
  · intro _ e member
    rw [h] at member
    cases member

theorem exact_projection_transfers_full_fits_under_same_stored_frame
    {p : SnapshotPair} {site : Nat} (proof : ProjectionAt p.pre p.post site)
    (frame : SameFitFrame p.before.state p.after.state) (m : I72.Model) :
    FitsFull p.before.state m ↔ FitsFull p.after.state m := by
  have models := exact_projection_keeps_models_in_both_directions proof m.assignment
  constructor
  · intro fit
    refine ⟨⟨⟨models.mpr fit.1.1.1,?_⟩,?_⟩,(frame.retained m).mp fit.2⟩
    · intro row present
      exact fit.1.1.2 row (frame.visible ▸ present)
    · intro origin present
      exact fit.1.2 origin (frame.native ▸ present)
  · intro fit
    refine ⟨⟨⟨models.mp fit.1.1.1,?_⟩,?_⟩,(frame.retained m).mpr fit.2⟩
    · intro row present
      exact fit.1.1.2 row (frame.visible ▸ present)
    · intro origin present
      exact fit.1.2 origin (frame.native ▸ present)

theorem after_read_in_original_fitting_model_under_explicit_stored_frame
    {p : SnapshotPair} {t : CheckedTable p.before.state.base.core.current}
    {site : Nat} {w : ProjectionFieldWire p} {r : ProjectionFieldReceipt}
    (read : readProjectionField p t site w = some r)
    (frame : SameFitFrame p.before.state p.after.state) (m : I72.Model) (fit : FitsFull p.before.state m) :
    FitsFull p.after.state m ∧ r.field.literal ≠ [] ∧
      GeneralDeclarativeK2Alias321.AliasCycle p.pre (GeneralDeclarativeGraphRows321.observed p.pre)
        r.field.terminal ∧
      ∃ o ∈ p.after.state.base.core.origins, o.slot = site ∧
        m.nativeSyntax o.slot = some o.endpoint := by
  have reflected := (exact_projected_field_iff_finite_checked_wire ..).mpr ⟨w,read⟩
  have same := (exact_projection_transfers_full_fits_under_same_stored_frame reflected.1 frame m).mp fit
  obtain ⟨nonempty,cycle,_,_,_,_,_,_,_,_,o,_,_,_,_,_,_,seen,_,physical,origin,_⟩ :=
    literal_post_visit_keeps_an_old_cycle_and_the_exact_issued_native_site reflected m same
  exact ⟨same,nonempty,cycle,o,seen,physical,origin⟩

end Yulang.GeneralDeclarativeI65.I72.NamedProjection464
