import Yulang.GeneralNominalModePattern237
import Yulang.GeneralNominalCenteredHeadMatCompilerSemantics
set_option linter.unusedSimpArgs false
set_option backward.isDefEq.respectTransparency false
/-! Exact compiler semantics and normalization in every mode, preserving actual
mode at invariant nominal applications. -/
namespace Yulang.GeneralNominalModeCompiler237
open GeneralDeclarationPatterns CommonNominalFullCarrier
open GeneralNominalMatchedAssembly (Aligned)
open GeneralNominalCenteredHeadMatCompilerSemantics (application algebra)
open GeneralNominalCenteredHeadMatExpressions (Expr primitiveValue value values)
open GeneralNominalModePattern237 (eval evals)
def next (interpretation : GeneralNominalInspection.Interpretation) (name : Nat)
    (mode : GeneralNominalMaterialization.Mode) : GeneralNominalMaterialization.Mode :=
  match interpretation.primitives name with
  | some _ => mode
  | none => .actual
theorem application_value (mode : GeneralNominalMaterialization.Mode)
    (compiled : GeneralNominalCenteredHeadMatExpressions.application catalogue interpretation name arguments = some expression) :
    value variables mode expression = application catalogue interpretation name (values variables (next interpretation name mode) arguments) := by
  cases declared : catalogue name with
  | none => simp [GeneralNominalCenteredHeadMatExpressions.application,declared] at compiled
  | some declaration =>
      by_cases arity : declaration.parameters.length = arguments.length
      · simp [GeneralNominalCenteredHeadMatExpressions.application,declared,arity] at compiled
        cases primitive : interpretation.primitives name with
        | none =>
            simp only [primitive] at compiled
            split at compiled
            · cases Option.some.inj compiled
              simp only [value,application,primitive,declared,next]
            · cases compiled
        | some primitiveValue =>
            simp only [primitive] at compiled
            split at compiled
            · cases Option.some.inj compiled
              simp only [value,application,primitive,next]
            · cases compiled
      · simp [GeneralNominalCenteredHeadMatExpressions.application,declared,arity] at compiled

mutual
  theorem translate_value (mode : GeneralNominalMaterialization.Mode) (pattern : Pattern)
      (compiled : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation pattern = some expression) :
      value variables mode expression = eval (algebra catalogue interpretation) (next interpretation) variables mode pattern := by
    cases pattern with
    | var name => cases Option.some.inj compiled; rfl
    | app name arguments =>
        cases translated : GeneralNominalCenteredHeadMatExpressions.translateMany catalogue interpretation arguments <;>
          simp only [GeneralNominalCenteredHeadMatExpressions.translate,translated,Option.bind_none,Option.bind_some] at compiled
        · cases compiled
        · rw [application_value mode compiled,translate_values (next interpretation name mode) arguments translated]
          rfl
    | record label payload tail =>
        cases one : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation payload <;>
          simp only [GeneralNominalCenteredHeadMatExpressions.translate,one,Option.bind_none,Option.bind_some] at compiled
        · cases compiled
        · cases two : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation tail <;>
            simp only [two,Option.bind_none,Option.bind_some,Option.pure_def] at compiled
          · cases compiled
          · cases Option.some.inj compiled
            simp only [value,eval,translate_value mode payload one,translate_value mode tail two]
    | variant tag payload =>
        cases one : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation payload <;>
          simp only [GeneralNominalCenteredHeadMatExpressions.translate,one,Option.bind_none,Option.bind_some,Option.pure_def] at compiled
        · cases compiled
        · cases Option.some.inj compiled
          simp only [value,eval,translate_value mode payload one]
    | join first last =>
        cases one : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation first <;>
          simp only [GeneralNominalCenteredHeadMatExpressions.translate,one,Option.bind_none,Option.bind_some] at compiled
        · cases compiled
        · cases two : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation last <;>
            simp only [two,Option.bind_none,Option.bind_some,Option.pure_def] at compiled
          · cases compiled
          · cases Option.some.inj compiled
            simp only [value,eval,translate_value mode first one,translate_value mode last two]
    termination_by sizeOf pattern
  theorem translate_values (mode : GeneralNominalMaterialization.Mode) (patterns : List Pattern)
      (compiled : GeneralNominalCenteredHeadMatExpressions.translateMany catalogue interpretation patterns = some expressions) :
      values variables mode expressions = evals (algebra catalogue interpretation) (next interpretation) variables mode patterns := by
    cases patterns with
    | nil => cases Option.some.inj compiled; rfl
    | cons head tail =>
        cases one : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation head <;>
          simp only [GeneralNominalCenteredHeadMatExpressions.translateMany,one,Option.bind_none,Option.bind_some] at compiled
        · cases compiled
        · cases two : GeneralNominalCenteredHeadMatExpressions.translateMany catalogue interpretation tail <;>
            simp only [two,Option.bind_none,Option.bind_some,Option.pure_def] at compiled
          · cases compiled
          · cases Option.some.inj compiled
            simp only [values,evals,translate_value mode head one,translate_values mode tail two]
    termination_by sizeOf patterns
end

theorem compiled_normalized (mode : GeneralNominalMaterialization.Mode)
    (compiled : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation pattern = some expression) :
    Equivalent (value variables mode expression)
      (eval (algebra catalogue interpretation) (next interpretation) variables mode (normalize pattern)) := by
  rw [translate_value mode pattern compiled]
  exact GeneralNominalModePattern237.normalize_sound mode pattern

end Yulang.GeneralNominalModeCompiler237
