import Yulang.GeneralDictionaryScalarRegistryIntervals
import Yulang.GeneralDictionaryScalarChildReachable
import Yulang.GeneralDictionaryVariableRegistryIntervals

/-! The source-registry condition and resulting generated interval property
hold in the actual scalar compound-child installation, not merely a raw journal. -/
namespace Yulang.GeneralDictionaryScalarRegistryExample
open GeneralDictionaryScalarChildExample GeneralDictionaryScalarChildReachable
open GeneralDictionaryScalarRegistryIntervals
open GeneralNominalSaturationState GeneralSourceDictionaries
open GeneralDeclarationExamples (roles)

theorem fragment : ScalarVariableRegistry registry installed.current.context.interpretation := by
  intro d visible c required pattern present
  have eq := List.mem_singleton.mp visible; subst d
  have eq := List.mem_singleton.mp required; subst c
  have eq := List.mem_singleton.mp present; subst pattern
  exact Or.inr ⟨2,.int,rfl,rfl⟩

theorem all_generated_intervals (focus : Occurrence roles) (generated : Generated installed.current GeneralNominalExamples.displayRoot focus)
    (model : GeneralNominalCommonBridge.Assignment) (valid : Models installed.current model) (index) :
    CommonNominalFullCarrier.Subtype (model (focus.demand.arguments index).1).1
      (model (focus.demand.arguments index).2).1 :=
  generated_intervals fragment reachable generated model valid index

theorem not_variable_registry : ¬ GeneralDictionaryVariableRegistryIntervals.VariableRegistry registry := by
  intro fragment
  obtain ⟨name,equal⟩ := fragment declaration (by simp) clause (by simp) (.app 2 []) (by simp)
  cases equal

/-- A reachable positive scalar-compound example genuinely lies outside the
previous variable-only registry restriction. -/
theorem strict_extension : ScalarVariableRegistry registry installed.current.context.interpretation ∧
    ¬ GeneralDictionaryVariableRegistryIntervals.VariableRegistry registry ∧
    Models installed.current GeneralNominalExamples.model :=
  ⟨fragment,not_variable_registry,installed_model⟩

end Yulang.GeneralDictionaryScalarRegistryExample
