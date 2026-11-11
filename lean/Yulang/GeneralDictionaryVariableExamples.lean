import Yulang.GeneralDictionaryVariableTerms
import Yulang.GeneralDictionaryBinderLocationExamples

/-! # Singleton input, deferred interval, and unchanged output-binder regressions -/
namespace Yulang.GeneralDictionaryVariableExamples
open GeneralDeclarationExamples (roles)
open GeneralDictionaryOutputBinderExamples
open GeneralDictionaryBinderLocationExamples
open GeneralDictionaryVariableTerms

abbrev singletonCapture : GeneralDeclarationDemands.Capture := ⟨fun _ => (12, 12), fun _ => 12⟩

theorem singleton_input_lookup : lookup roles inputWrap singletonCapture 0 = some (.var 12) := rfl

theorem unequal_input_deferred : lookup roles inputWrap shiftedCapture 0 = none := rfl

theorem output_binder_unchanged : lookup roles binderWrap shiftedCapture 0 = some (.var 12) := rfl

theorem compound_deferred : lookup roles GeneralDeclarationExamples.wrap singletonCapture 0 = none := rfl

theorem default_deferred : lookup defaultRoles defaultWrap singletonCapture 0 = none := rfl

theorem nonidentity_input_compiles :
    compile shiftedState roles inputWrap singletonCapture 0 = some (.var 2) := rfl

theorem nonidentity_input_build : build inputWrap singletonCapture shiftedInputs = some shiftedLocated := by
  have compiled : ∀ index : Fin shiftedDemand.outputs.length,
      compile shiftedState roles inputWrap singletonCapture (shiftedDemand.outputs[index]).name = some (.var 2) := by
    rintro ⟨index, bound⟩
    change index < 2 at bound
    have cases : index = 0 ∨ index = 1 := by omega
    rcases cases with rfl | rfl <;> rfl
  have complete : ∀ index : Fin shiftedDemand.outputs.length,
      (compile shiftedState roles inputWrap singletonCapture (shiftedDemand.outputs[index]).name).isSome = true := by
    intro index
    rw [compiled index]
    rfl
  unfold build
  rw [dite_eq_left complete]
  congr 1
  congr
  funext index
  simp only [compiled index, Option.get_some]

end Yulang.GeneralDictionaryVariableExamples
