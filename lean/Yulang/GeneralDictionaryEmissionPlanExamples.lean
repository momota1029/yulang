import Yulang.GeneralDictionaryEmissionPlans
import Yulang.GeneralDeclarationExamples

/-! # Actual checked declaration and named-output emission plan
This checks the real general Wrap/Container declaration fixture, with an explicit
fixed frame. It does not infer that frame or claim its source IDs are an allocator. -/
namespace Yulang.GeneralDictionaryEmissionPlanExamples
open GeneralDeclarations GeneralDeclarationDemands GeneralDeclarationExamples
open GeneralSourceDictionaries GeneralDictionaryEmissionPlans GeneralRegistryReordering

abbrev rootDemand : GeneralSourceState.Demand roles where
  role := 1
  arguments := fun _ => (10, 11)
  outputs := []
  declared := by simp

abbrev root : Occurrence roles := ⟨9, rootDemand⟩

abbrev frame : Frame roles where
  capture := fun _ => wrapCapture
  allocation := fun _ _ => ⟨fun _ => (300, 301), fun _ => 400⟩
  identity := fun _ _ clause => clause

/-- Full source occurrence, argument interval and named output are retained. -/
theorem actual_child_plan :
    children frame root wrap wrap_checked =
      [⟨20, childDemand wrap containerChild
        (wrap_checked.signature.2.2.2 containerChild (by simp)) wrapCapture wrapAllocation⟩] := by
  have original : emitAll root.identity wrap wrap_checked.signature
      (frame.capture wrap.id) (frame.allocation wrap.id) =
      [emit 9 wrap containerChild (wrap_checked.signature.2.2.2 containerChild (by simp))
        wrapCapture wrapAllocation] := rfl
  have permuted := GeneralCanonicalChildOrder.canonicalEmit_perm root.identity wrap wrap_checked
    (frame.capture wrap.id) (frame.allocation wrap.id)
  rw [original] at permuted
  have canonical := permuted.symm.eq_singleton
  unfold children
  rw [canonical]
  rfl

theorem wrap_plan : Plan registry registry_checked frame root 2 (children frame root wrap wrap_checked) :=
  visible_plan registry registry_checked frame root wrap (by simp) rfl

theorem wrap_plan_unique (demands : List (Occurrence roles))
    (plan : Plan registry registry_checked frame root 2 demands) :
    demands = children frame root wrap wrap_checked :=
  plan_children_functional registry registry_checked frame root 2 demands _ plan wrap_plan

abbrev reversed : Registry := ⟨constructors, roles, [wrap, display]⟩

theorem reversed_order : Reorders registry reversed := by
  refine ⟨rfl, rfl, [wrap, display], .swap _ _ _, ?_⟩
  exact .cons (declarationReorders_refl wrap) (.cons (declarationReorders_refl display) .nil)

theorem reversed_checked : Checked reversed := reorders_checked reversed_order registry_checked

theorem reversed_same_plan (demands : List (Occurrence roles)) :
    Plan registry registry_checked frame root 2 demands ↔
      Plan reversed reversed_checked frame root 2 demands :=
  plan_reorders_iff constructors roles [display, wrap] [wrap, display]
    registry_checked reversed_checked reversed_order frame root 2 demands

end Yulang.GeneralDictionaryEmissionPlanExamples
