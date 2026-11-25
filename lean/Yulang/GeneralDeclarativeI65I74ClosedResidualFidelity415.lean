import Yulang.GeneralDeclarativeI65I74ClosedResidualEntry415

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessDeclaredState357 (point)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_trans record_congr)
open CommonNominalFullCarrier (record Equivalent)
open CommonRoleCanonicalRows (capture lookup)
open Checker408 (Problem)

theorem removed_field_not_in_original_residual415 {s q} (a : ClosedRows s q) :
    lookup a.x (capture [a.x] a.fields) = none := by
  rw [closed_source_subtraction_exact415 a]
  simp [lookup,a.different]

theorem exact_same_model_residual_value415 {s q} (a : ClosedRows s q)
    (m : I72.Model) (fit : Fits s m) :
    Equivalent (m.assignment a.residual).1 (record a.y (.base .str) .emptyRecord) := by
  have atResidual := fit.1.1.2 _ a.retainedResidual
  have actualStr := fit.1.1.2 _ a.string
  change Equivalent (m.assignment a.strSlot).1 (.base .str) at actualStr
  change Equivalent (m.assignment a.residual).1 (record a.y (m.assignment a.strSlot).1 .emptyRecord) at atResidual
  exact eqv_trans atResidual (record_congr _ actualStr (eqv_refl _))

theorem original_coordinate_is_independent_of_wire415 {s q} (a b : ClosedRows s q) :
    a.root = b.root ∧ a.x = b.x ∧ a.intSlot = b.intSlot ∧ a.y = b.y ∧
      a.strSlot = b.strSlot ∧ a.residual = b.residual := by
  have roots : a.root = b.root := congrArg GeneralDeclarativeWhere319.Capture.lower
    (List.cons.inj (a.requested.symm.trans b.requested)).1
  obtain ⟨only,found⟩ := List.length_eq_one_iff.mp a.originalCount
  have aoMem : a.original ∈ s.core.origins.filter (fun r => r.slot == a.root) :=
    List.mem_filter.mpr ⟨a.actualOriginal,by simp [a.originalRoot]⟩
  have boMem : b.original ∈ s.core.origins.filter (fun r => r.slot == a.root) :=
    List.mem_filter.mpr ⟨b.actualOriginal,by simp [b.originalRoot,roots]⟩
  rw [found] at aoMem boMem
  have eqOrigin := (List.mem_singleton.mp aoMem).trans (List.mem_singleton.mp boMem).symm
  have endpoints := a.source.symm.trans ((congrArg Origin.endpoint eqOrigin).trans b.source)
  have parts := CommonRecursiveNominalIntervals.Endpoint.ordinary.inj endpoints
  have outer := Core.PresenceGeneration.TyTerm.record.inj parts
  have inner := Core.PresenceGeneration.TyTerm.record.inj outer.2.2
  have xEq := outer.1
  have iEq := Core.PresenceGeneration.TyTerm.var.inj outer.2.1
  have yEq := inner.1
  have sEq := Core.PresenceGeneration.TyTerm.var.inj inner.2.1
  have other := b.uniqueSplit
  have sameKeys : isSplit415 a.root a.x a.intSlot = isSplit415 b.root b.x b.intSlot := by rw [roots,xEq,iEq]
  rw [← sameKeys] at other
  have recorded := (List.cons.inj (a.uniqueSplit.symm.trans other)).1
  have sameRow := (GeneralDeclarativeHead320.Equation.mk.inj recorded).2
  have rest := GeneralNominalCenteredHeadMatExpressions.Expr.variable.inj
    (GeneralNominalCenteredHeadMatExpressions.Expr.record.inj sameRow).2.2
  exact ⟨roots,xEq,iEq,yEq,sEq,rest⟩

theorem actual_captured_tail_is_original_residual415 {p : Problem}
    (read : VerifiedClosed p) :
    read.parent.event.frame.input read.parent.binder = point read.rows.residual ∧
    read.parent.event.kids = [query415 p.root read.parent.childRole read.rows.residual] ∧
    read.child.event.frame.input read.child.binder = point read.rows.strSlot := by
  refine ⟨?_,parent_emits_actual_residual_child415 read.parent,?_⟩ <;>
    simp [ClosedParent.event,ClosedChild.event,ExactCandidate.frame,pointCapture415]

end Yulang.GeneralDeclarativeI65.I72.ClosedResidual415
