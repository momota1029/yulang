import Yulang.GeneralDeclarativePolarNormalize344

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
namespace Yulang.GeneralDeclarativePolarCompiler344
open GeneralDeclarationPatterns (Pattern Constructors normalize)
open GeneralNominalInspection (Interpretation)
open GeneralNominalMaterialization (Mode)
open GeneralNominalCenteredHeadMatExpressions (Expr value values translate)
open GeneralNominalCenteredHeadMatCompilerSemantics (application)
open GeneralDeclarativePolarNormalize344 (argMode eval evals normalize_sound)
open CommonNominalFullCarrier (Ty Equivalent)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_symm eqv_trans)

variable {catalogue : Constructors} {interpretation : Interpretation} {variables : Mode → Nat → Ty}
theorem application_value (mode : Mode)
    (compiled : GeneralNominalCenteredHeadMatExpressions.application catalogue interpretation name arguments = some expression) :
    value variables mode expression = application catalogue interpretation name
      (values variables (argMode interpretation mode name) arguments) := by
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
              simp [value,application,argMode,primitive,declared]
            · cases compiled
        | some primitiveValue =>
            simp only [primitive] at compiled
            split at compiled
            · cases Option.some.inj compiled
              simp [value,application,argMode,primitive]
            · cases compiled
      · simp [GeneralNominalCenteredHeadMatExpressions.application,declared,arity] at compiled

mutual
  theorem translate_value (mode : Mode) (pattern : Pattern)
      (compiled : GeneralNominalCenteredHeadMatExpressions.translate catalogue interpretation pattern = some expression) :
      value variables mode expression = eval catalogue interpretation variables mode pattern := by
    cases pattern with
    | var name => cases Option.some.inj compiled; rfl
    | app name arguments =>
        cases translated : GeneralNominalCenteredHeadMatExpressions.translateMany catalogue interpretation arguments <;>
          simp only [GeneralNominalCenteredHeadMatExpressions.translate,translated,Option.bind_none,Option.bind_some] at compiled
        · cases compiled
        · exact (application_value mode compiled).trans
            (congrArg (application catalogue interpretation name)
              (translate_values (argMode interpretation mode name) arguments translated))
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
  theorem translate_values (mode : Mode) (patterns : List Pattern)
      (compiled : GeneralNominalCenteredHeadMatExpressions.translateMany catalogue interpretation patterns = some expressions) :
      values variables mode expressions = evals catalogue interpretation variables mode patterns := by
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

theorem normalized_codes {pat : Pattern} {source canonical : Expr}
    (raw : translate catalogue interpretation pat = some source)
    (normal : translate catalogue interpretation (normalize pat) = some canonical)
    (mode : Mode) :
    Equivalent (value variables mode source) (value variables mode canonical) := by
  rw [translate_value mode pat raw,translate_value mode (normalize pat) normal]
  exact normalize_sound mode pat

end Yulang.GeneralDeclarativePolarCompiler344
