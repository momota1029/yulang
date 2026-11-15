import Yulang.GeneralDictionarySemanticCollapseSchema
import Yulang.GeneralDictionaryDefaultBodyTransport209

/-! Total expressions after a genuine two-to-one nominal capture collapse.
This uses point leaf observations and both actual readbacks, not report equality.
It does not establish availability of the new packet or its child evidence. -/
namespace Yulang.GeneralDictionaryDefaultCollapseExpression210
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseAllocation
open GeneralDictionarySemanticCollapseSchema GeneralNominalReobservationSteps
open GeneralNominalRecursiveInspection GeneralNominalAllocation GeneralDeclarations
open CommonNominalFullCarrier GeneralNominalCenteredHeadMatExpressions
variable {roles : Roles.RoleDecls} {state : GeneralNominalSaturationState.State roles}
variable {revision : Revision state}

 theorem fits_unique {model : GeneralNominalCommonBridge.Assignment}
    {first last : GeneralSourceState.Interval} {a b : Ty}
    (lower : Equivalent (model first.1).1 (model last.1).1)
    (upper : Equivalent (model first.2).1 (model last.2).1)
    (point : Equivalent (model last.1).1 (model last.2).1)
    (fa : GeneralNominalCaptureMerges.Fits model first a)
    (fb : GeneralNominalCaptureMerges.Fits model last b) : Equivalent a b := by
  exact ⟨subtype_trans fa.2 (subtype_trans upper.1 (subtype_trans point.2 fb.1)),
    subtype_trans fb.2 (subtype_trans point.2 (subtype_trans lower.2 fa.1))⟩

 theorem actual_equivalent (s : Shape revision) (registry : Registry)
    (invocation : Nat) (declaration : Declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (declared : s.binder ∈ declaration.inputNames)
    (old : ProjectionModels state.context.state
      (inspect state.context.state (query s) (s.root,s.root) none) model)
    (firstPoint : s.first.1 = s.first.2) (lastPoint : s.last.1 = s.last.2)
    (propagated : GeneralNominalState.Models (propagate state.context.state registry invocation declaration
      (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model)
    (before after : Ty)
    (oldFits : GeneralNominalCaptureMerges.Fits model
      ((oldCapture s registry invocation declaration).inputs s.binder) before)
    (newFits : GeneralNominalCaptureMerges.Fits model
      ((newCapture s registry invocation declaration).inputs s.binder) after) : Equivalent before after := by
  have endpoints := capture_endpoints s registry invocation declaration model declared old firstPoint lastPoint propagated
  apply fits_unique endpoints.1 endpoints.2 ?_ oldFits newFits
  simp only [bindings_after,capture,occurrences]
  simpa [firstPoint] using (show Equivalent (model (state.context.state.base.source s.first.2)).1
    (model (state.context.state.base.source s.first.2)).1 from ⟨subtype_refl _,subtype_refl _⟩)

 theorem expression_equivalent (s : Shape revision) (registry : Registry)
    (invocation : Nat) (declaration : Declaration)
    (model : GeneralNominalCommonBridge.Assignment)
    (declared : s.binder ∈ declaration.inputNames)
    (old : ProjectionModels state.context.state
      (inspect state.context.state (query s) (s.root,s.root) none) model)
    (firstPoint : s.first.1 = s.first.2) (lastPoint : s.last.1 = s.last.2)
    (propagated : GeneralNominalState.Models (propagate state.context.state registry invocation declaration
      (bindings state.context.state (inspect state.context.state (query s) (s.root,s.root) none))) model)
    (before after : GeneralNominalMaterialization.Mode → Nat → Ty)
    (oldFits : GeneralNominalCaptureMerges.Fits model
      ((oldCapture s registry invocation declaration).inputs s.binder) (before .actual s.binder))
    (newFits : GeneralNominalCaptureMerges.Fits model
      ((newCapture s registry invocation declaration).inputs s.binder) (after .actual s.binder))
    (expression : Expr)
    (scope : ∀ name ∈ GeneralNominalCenteredHeadMatExtension.names expression, name = s.binder) :
    Equivalent (value before .actual expression) (value after .actual expression) := by
  apply GeneralDictionaryDefaultBodyTransport209.actual_equivalent expression
  intro name member
  rw [scope name member]
  exact actual_equivalent s registry invocation declaration model declared old firstPoint lastPoint propagated
    _ _ oldFits newFits
end Yulang.GeneralDictionaryDefaultCollapseExpression210
