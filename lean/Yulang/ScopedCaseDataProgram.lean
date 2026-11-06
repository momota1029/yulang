import Yulang.ScopedCaseEvaluation
import Yulang.ScopedCaseTotal
import Yulang.PatternBindingChecks
import Yulang.CaseDataProgram

/-!
# Concrete case syntax with scoped pattern defaults

The existing `CaseDataProgram.Program` is evaluated with the extended matcher.
Default code is actual `CaseDataTerms` syntax, evaluated in the current
environment. No expression-success oracle is required by the safety theorem.

This minimal typing entry certifies progress with a declaratively irrefutable
unguarded arm. `ScopedCaseCoverageSafety` and `ScopedJointCaseCoverage` connect
the same evaluator to structural coverage and joint polyvariant payload
coverage. `checkBindings` is only a static naming check, not a whole-language
type checker. The old unscoped reference entry and its theorems are retained
unchanged.
-/

namespace Yulang.CaseDataTerms

open CaseValues EvaluationTrace

theorem default_scoped_sound {F : Type} :
    ScopedCasePatterns.DefaultSound (@Typing F) (@defaultEval F) := by
  intro types code target typed environment valid
  exact typing_evaluates typed environment valid

end Yulang.CaseDataTerms

namespace Yulang.ScopedCaseDataProgram

open CaseValues EvaluationTrace

abbrev Program (F : Type) := CaseDataProgram.Program F
abbrev Arm (F : Type) := CaseDataProgram.Arm F
abbrev Result (F : Type) :=
  Logged (CaseEvaluation.Event (CaseDataTerms.Expr F)) CaseDataTerms.Error (Option (Value F))

def eval (floatCheck : F → F → Bool) (outer : Bindings F) (program : Program F) : Result F :=
  ScopedCaseEvaluation.eval floatCheck CaseDataTerms.defaultEval outer (CaseDataTerms.guardEval outer)
    (CaseDataTerms.bodyEval outer) (CaseDataTerms.eval outer program.scrutinee) program.arms

def checkBindings (program : Program F) : Bool :=
  program.arms.all (fun arm => PatternBindingChecks.check arm.pattern)

/-- Naming rejection happens before any scrutinee/default/guard/body runs. -/
def checkedEval (floatCheck : F → F → Bool) (outer : Bindings F) (program : Program F) :
    Option (Result F) :=
  if checkBindings program then some (eval floatCheck outer program) else none

theorem checkBindings_exact (program : Program F) :
    checkBindings program = true ↔
      ∀ arm ∈ program.arms, PatternBindingChecks.NamesValid arm.pattern := by
  simp [checkBindings, List.all_eq_true, PatternBindingChecks.check_exact]

theorem checkedEval_rejects_iff (floatCheck : F → F → Bool) (outer : Bindings F) (program : Program F) :
    checkedEval floatCheck outer program = none ↔
      ∃ arm ∈ program.arms, ¬ PatternBindingChecks.NamesValid arm.pattern := by
  simp [checkedEval, checkBindings_exact]

/-- Every leaf, including each scope-dependent fallback, is independently
typed syntax. The final premise is structural irrefutability, not execution. -/
inductive Typing (types : List (Nat × Ty F)) : Program F → Ty F → Prop where
  | caseE (input : Ty F)
      (scrutinee : CaseDataTerms.Typing types program.scrutinee input)
      (arms : ∀ arm ∈ program.arms,
        PatternBindingChecks.NamesValid arm.pattern ∧
          ScopedCaseEvaluation.ArmTyping CaseDataTerms.Typing (CaseDataTerms.GuardTyped types)
            (CaseDataTerms.BodyTyped types) types arm input target)
      (covered : ∃ arm ∈ program.arms, arm.guard = none ∧ ∃ bindings,
        ScopedCasePatterns.TotalTyping CaseDataTerms.Typing types arm.pattern input bindings) :
      Typing types program target

@[local simp] private theorem except_bind_ok (value : A) (next : A → Except R B) :
    (Except.ok value).bind next = next value := rfl

theorem typing_evaluates (floatCheck : F → F → Bool)
    (typed : Typing types program target)
    (outer : Bindings F) (valid : BindingsHold types outer) :
    ∃ result, (eval floatCheck outer program).result = .ok (some result) ∧ target result := by
  cases typed with
  | caseE input scrutinee arms covered =>
      obtain ⟨value, sourceEval, valueValid⟩ := CaseDataTerms.typing_evaluates scrutinee outer valid
      obtain ⟨totalArm, member, unguarded, bindings, total⟩ := covered
      obtain ⟨matched, patternEval, _⟩ := total.matches floatCheck CaseDataTerms.defaultEval
        CaseDataTerms.default_scoped_sound outer valid value valueValid
      obtain ⟨result, armsEval, resultValid⟩ := ScopedCaseEvaluation.runArms_progress floatCheck
        CaseDataTerms.defaultEval outer (CaseDataTerms.guardEval outer) (CaseDataTerms.bodyEval outer)
        CaseDataTerms.default_scoped_sound (CaseDataTerms.guard_sound outer types valid)
        (CaseDataTerms.body_sound outer types valid) program.arms
        (fun arm member => (arms arm member).2) value valueValid
        ⟨totalArm, member, unguarded, matched, patternEval⟩ 0 valid
      exact ⟨result, by simp [eval, ScopedCaseEvaluation.eval, Logged.bind_result, sourceEval, armsEval],
        resultValid⟩

theorem typed_bindings_accepted (typed : Typing types program target) : checkBindings program = true := by
  apply (checkBindings_exact program).mpr
  cases typed with
  | caseE _ _ arms _ => exact fun arm member => (arms arm member).1

theorem typed_checkedEval (floatCheck : F → F → Bool) (typed : Typing types program target)
    (outer : Bindings F) :
    checkedEval floatCheck outer program = some (eval floatCheck outer program) := by
  simp [checkedEval, typed_bindings_accepted typed]

theorem typed_no_unmatched (floatCheck : F → F → Bool) (typed : Typing types program target)
    (outer : Bindings F) (valid : BindingsHold types outer) :
    (eval floatCheck outer program).result ≠ .ok none := by
  obtain ⟨result, evaluated, _⟩ := typing_evaluates floatCheck typed outer valid
  simp [evaluated]

end Yulang.ScopedCaseDataProgram
