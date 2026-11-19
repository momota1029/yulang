import Yulang.GeneralNominalVersionedMixedSourceBoundary234
import Yulang.GeneralNominalExamples

/-! Closed checks diagnosing the next adapter task, not an invariance theorem. -/
namespace Yulang.Cycle276EncodingDiagnostic
open GeneralDeclarations
open GeneralDeclarationExamples (display wrap)
open GeneralNominalExamples (registry intDisplay)
open GeneralNominalCenteredHeadAllocEncoding (declaration)
abbrev compiled := GeneralNominalCenteredHeadAllocEncoding.registry registry

example : declaration display = display := rfl
example : declaration intDisplay = intDisplay := rfl
example : compiled.declarations.filter (fun d => d.role == 0) = [intDisplay,display] := rfl
example : (declaration wrap).outputBinders.map (fun b => b.equation) = [1701] := rfl
example : wrap.outputBinders.map (fun b => b.equation) = [21] := rfl
example : compiled ≠ registry := by
  intro same
  have keys := congrArg (fun r : Registry => r.declarations.flatMap (fun d =>
    d.outputBinders.map (fun b => b.equation))) same
  have bad : (1701 : Nat) = 21 := List.cons.inj keys |>.1
  omega

end Yulang.Cycle276EncodingDiagnostic
