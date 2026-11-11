import Yulang.GeneralDictionaryPlanLookup
import Yulang.GeneralDictionaryEmissionPlanExamples

/-! # Executable source-plan positive, absent-key, and wrong-role checks
These use the checked general declaration fixture and retain its named output.
Lookup failure is not represented as semantic role rejection. -/
namespace Yulang.GeneralDictionaryPlanLookupExamples
open GeneralDeclarations GeneralDeclarationExamples GeneralSourceDictionaries
open GeneralDictionaryEmissionPlans GeneralDictionaryEmissionPlanExamples
open GeneralDictionaryPlanLookup

theorem actual_lookup : lookup registry registry_checked frame root 2 =
    some (children frame root wrap wrap_checked) :=
  (lookup_exact registry registry_checked frame root 2 _).mpr wrap_plan

theorem missing_key : lookup registry registry_checked frame root 99 = none := by
  apply (lookup_none registry registry_checked frame root 99).mpr
  rintro demands ⟨declaration, present, identity, _, _⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl <;> cases identity

theorem wrong_role : lookup registry registry_checked frame root 1 = none := by
  apply (lookup_none registry registry_checked frame root 1).mpr
  rintro demands ⟨declaration, present, identity, role, _⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl
  · cases role
  · cases identity

theorem reversed_lookup : lookup reversed reversed_checked frame root 2 =
    some (children frame root wrap wrap_checked) := by
  rw [← lookup_reorders constructors roles [display, wrap] [wrap, display]
    registry_checked reversed_checked reversed_order frame root 2]
  exact actual_lookup

end Yulang.GeneralDictionaryPlanLookupExamples
