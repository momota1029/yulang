import Yulang.GeneralDictionaryDefaultCollapseExpression210
import Yulang.GeneralDictionarySemanticCollapseOutputExample

/-! Concrete nested nominal reinspection changes allocation identities while
preserving a total expression with a union, record tail, variant, and nominal.
This is a materializer regression, not a complete operational dictionary node. -/
namespace Yulang.GeneralDictionaryDefaultCollapseRegression210
open GeneralDictionarySemanticCollapseExample
open GeneralDictionarySemanticCollapseOutputExample (registry declaration names outputRoot)
open GeneralDictionarySemanticCollapse GeneralDictionarySemanticCollapseSchema
open GeneralNominalRecursiveInspection GeneralNominalAllocation
open GeneralNominalCenteredHeadMatExpressions CommonNominalFullCarrier

noncomputable def before : GeneralNominalMaterialization.Mode → Nat → Ty :=
  fun _ _ => (model ((oldCapture shape registry outputRoot.identity declaration).inputs 7).1).1
noncomputable def after : GeneralNominalMaterialization.Mode → Nat → Ty :=
  fun _ _ => (model ((newCapture shape registry outputRoot.identity declaration).inputs 7).1).1

def expression : Expr := .join
  (.record 11 (.nominal 12 [.variable 7]) (.variable 7))
  (.variant 13 (.primitive .pair [.variable 7,.variable 7]))

 theorem expression_scope :
    ∀ name ∈ GeneralNominalCenteredHeadMatExtension.names expression, name = shape.binder := by
  simp [expression,GeneralNominalCenteredHeadMatExtension.names,
    GeneralNominalCenteredHeadMatExtension.namesMany,shape]

 theorem old_fits : GeneralNominalCaptureMerges.Fits model
    ((oldCapture shape registry outputRoot.identity declaration).inputs 7) (before .actual 7) := by
  unfold before oldCapture
  have ends := GeneralDictionarySemanticCollapseAllocationExample.endpoints registry outputRoot.identity declaration names
  change GeneralNominalCaptureMerges.Fits model
    ((capture source registry outputRoot.identity declaration.id
      (bindings source (inspect source (query shape) (shape.root,shape.root) none))).inputs 7) _
  rw [bindings_before shape]
  exact ⟨subtype_refl _,subtype_trans ends.1.1 ends.2.2⟩

 theorem new_fits : GeneralNominalCaptureMerges.Fits model
    ((newCapture shape registry outputRoot.identity declaration).inputs 7) (after .actual 7) := by
  unfold after newCapture
  change GeneralNominalCaptureMerges.Fits model
    ((capture revision.snapshot registry outputRoot.identity declaration.id
      (bindings revision.snapshot (inspect revision.snapshot (query shape) (shape.root,shape.root) none))).inputs 7) _
  rw [bindings_after shape]
  exact ⟨subtype_refl _,subtype_refl _⟩

 theorem transported : Equivalent (value before .actual expression) (value after .actual expression) := by
  apply GeneralDictionaryDefaultCollapseExpression210.expression_equivalent shape registry outputRoot.identity
    declaration model (by change 7 ∈ [7]; simp) old_projection rfl rfl
  · rw [bindings_before shape]
    exact GeneralDictionarySemanticCollapseAllocationExample.old_propagation registry outputRoot.identity declaration names
  · exact old_fits
  · exact new_fits
  · exact expression_scope

 theorem source_ids_changed :
    (oldCapture shape registry outputRoot.identity declaration).inputs 7 ≠
      (newCapture shape registry outputRoot.identity declaration).inputs 7 := by
  unfold oldCapture newCapture
  rw [bindings_before shape,bindings_after shape]
  exact GeneralDictionarySemanticCollapseAllocationExample.capture_ids_differ registry outputRoot.identity declaration.id
end Yulang.GeneralDictionaryDefaultCollapseRegression210
