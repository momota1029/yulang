import Yulang.GeneralDeclarativeOrigins321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeSupportedReads321
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeOrigins321 (Supported restriction restrict_models)
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeSubstitution320 (EquationRead equation_read logical logical_value)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeArgumentFacts320 (headFact whereFacts)
open GeneralNominalCenteredHeadMatExpressions (translate)
open GeneralDeclarationPatterns (normalize)

theorem supported_entails (p : Supported s completed)
    (proof : EquationRead (restriction p) capture mode name code) :
    Entails s ⟨name,logical capture mode code⟩ := by
  intro m valid
  simp only [GeneralDeclarativeEntailment320.Holds,logical_value]
  exact equation_read proof m (restrict_models p m valid)

theorem supported_head (p : Supported s completed)
    (translated : translate c interp pattern = some code)
    (proof : EquationRead (restriction p) capture .actual arg.center code) :
    ∃ row, headFact c interp capture arg pattern = some [row] ∧ Entails s row :=
  ⟨⟨arg.center,logical capture .actual code⟩, by simp [headFact,translated],supported_entails p proof⟩

theorem supported_where (p : Supported s completed)
    (translated : translate c interp (normalize pattern) = some code)
    (lo : EquationRead (restriction p) capture .lower arg.lower code)
    (mid : EquationRead (restriction p) capture .actual arg.center code)
    (hi : EquationRead (restriction p) capture .upper arg.upper code) :
    ∃ rows, whereFacts c interp capture arg pattern = some rows ∧ ∀ row ∈ rows, Entails s row := by
  simp only [whereFacts,translated,Option.map_some]
  refine ⟨_,rfl,?_⟩
  intro row member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with h | h | h <;> subst row
  · exact supported_entails p lo
  · exact supported_entails p mid
  · exact supported_entails p hi

end Yulang.GeneralDeclarativeSupportedReads321
