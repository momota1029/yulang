import Yulang.CaseCoverageSafety
import Yulang.CaseDataTerms

/-!
# A concrete checked case program

This wrapper closes every abstract leaf contract with `CaseDataTerms` syntax
and its independent typing theorem. Its main theorem assumes only syntactic
typing/coverage derivations and a typed outer environment, never success of
a particular expression, pattern, guard, body, or complete case execution.

Default annotations are required only for code occurring in the finite arm
syntax. The chosen outer environment is explicit; this is not a new decision
about how surface default expressions resolve names. Nested case expressions
are a separate extension, not a claim of this one-node wrapper.
-/

namespace Yulang.CaseDataProgram

open CaseValues CaseCoverage EvaluationTrace

abbrev Arm (F : Type) := CaseEvaluation.Arm F (CaseDataTerms.Expr F) (CaseDataTerms.Expr F) (CaseDataTerms.Expr F)

structure Program (F : Type) where
  scrutinee : CaseDataTerms.Expr F
  arms : List (Arm F)
  deriving Repr

def eval (floatCheck : F → F → Bool) (outer : Bindings F) (program : Program F) :
    Logged (CaseEvaluation.Event (CaseDataTerms.Expr F)) CaseDataTerms.Error (Option (Value F)) :=
  CaseEvaluation.eval floatCheck (CaseDataTerms.defaultEval outer) (CaseDataTerms.guardEval outer)
    (CaseDataTerms.bodyEval outer) (CaseDataTerms.eval outer program.scrutinee) program.arms

/-- Coverage is an independent inductive judgement, not a Boolean premise.
Every default code actually occurring in any arm has a syntax typing. -/
inductive Typing (types : List (Nat × Ty F)) (defaultDomains : CaseDataTerms.Expr F → Domain) :
    Program F → Ty F → Prop where
  | uniform (input : Domain)
      (scrutinee : CaseDataTerms.Typing types program.scrutinee (input.denote F))
      (defaults : ∀ code ∈ armDefaults (coverageArms program.arms),
        CaseDataTerms.Typing types code ((defaultDomains code).denote F))
      (arms : ∀ arm ∈ program.arms,
        CaseEvaluation.ArmTyping (CaseDataTerms.DefaultTyped types) (CaseDataTerms.GuardTyped types)
          (CaseDataTerms.BodyTyped types) arm (input.denote F) target)
      (coverage : Covered defaultDomains (coverageArms program.arms) input) :
      Typing types defaultDomains program target
  | variants (row : VariantRow)
      (scrutinee : CaseDataTerms.Typing types program.scrutinee (Ty.variants (semanticRow row)))
      (defaults : ∀ code ∈ armDefaults (coverageArms program.arms),
        CaseDataTerms.Typing types code ((defaultDomains code).denote F))
      (arms : ∀ arm ∈ program.arms,
        CaseEvaluation.ArmTyping (CaseDataTerms.DefaultTyped types) (CaseDataTerms.GuardTyped types)
          (CaseDataTerms.BodyTyped types) arm (Ty.variants (semanticRow row)) target)
      (coverage : VariantsCovered defaultDomains (coverageArms program.arms) row) :
      Typing types defaultDomains program target

/-- Concrete typing entails evaluation to a value of the declared result
type. In particular evaluation cannot fail or finish with no matching arm. -/
theorem typing_evaluates (floatCheck : F → F → Bool)
    (typed : Typing types defaultDomains program target)
    (outer : Bindings F) (valid : BindingsHold types outer) :
    ∃ result, (eval floatCheck outer program).result = .ok (some result) ∧ target result := by
  have sourceSound : ScrutineeSound (CaseDataTerms.Typing types) (CaseDataTerms.eval outer) :=
    fun _ _ source => CaseDataTerms.typing_evaluates source outer valid
  cases typed with
  | uniform input scrutinee defaults arms coverage =>
      exact checked_case_evaluates floatCheck (CaseDataTerms.eval outer)
        (CaseDataTerms.defaultEval outer) (CaseDataTerms.guardEval outer) (CaseDataTerms.bodyEval outer)
        defaultDomains sourceSound (CaseDataTerms.default_sound outer types valid)
        (CaseDataTerms.guard_sound outer types valid) (CaseDataTerms.body_sound outer types valid)
        program.scrutinee program.arms input defaults scrutinee arms ((check_exact _ _ _).mpr coverage)
  | variants row scrutinee defaults arms coverage =>
      exact checked_variants_case_evaluates floatCheck (CaseDataTerms.eval outer)
        (CaseDataTerms.defaultEval outer) (CaseDataTerms.guardEval outer) (CaseDataTerms.bodyEval outer)
        defaultDomains sourceSound (CaseDataTerms.default_sound outer types valid)
        (CaseDataTerms.guard_sound outer types valid) (CaseDataTerms.body_sound outer types valid)
        program.scrutinee program.arms row defaults scrutinee arms ((checkVariants_exact _ _ _).mpr coverage)

theorem closed_typing_evaluates (floatCheck : F → F → Bool)
    (typed : Typing [] defaultDomains program target) :
    ∃ result, (eval floatCheck [] program).result = .ok (some result) ∧ target result :=
  typing_evaluates floatCheck typed [] .nil

/-- Executable coverage can discharge the independent coverage premise. -/
theorem checked_evaluates (floatCheck : F → F → Bool)
    (types : List (Nat × Ty F)) (defaultDomains : CaseDataTerms.Expr F → Domain)
    (program : Program F) (input : Domain)
    (scrutinee : CaseDataTerms.Typing types program.scrutinee (input.denote F))
    (defaults : ∀ code ∈ armDefaults (coverageArms program.arms),
      CaseDataTerms.Typing types code ((defaultDomains code).denote F))
    (arms : ∀ arm ∈ program.arms,
      CaseEvaluation.ArmTyping (CaseDataTerms.DefaultTyped types) (CaseDataTerms.GuardTyped types)
        (CaseDataTerms.BodyTyped types) arm (input.denote F) target)
    (checked : check defaultDomains (coverageArms program.arms) input = true)
    (outer : Bindings F) (valid : BindingsHold types outer) :
    ∃ result, (eval floatCheck outer program).result = .ok (some result) ∧ target result :=
  typing_evaluates floatCheck (.uniform input scrutinee defaults arms ((check_exact _ _ _).mp checked)) outer valid

theorem checked_variants_evaluate (floatCheck : F → F → Bool)
    (types : List (Nat × Ty F)) (defaultDomains : CaseDataTerms.Expr F → Domain)
    (program : Program F) (row : VariantRow)
    (scrutinee : CaseDataTerms.Typing types program.scrutinee (Ty.variants (semanticRow row)))
    (defaults : ∀ code ∈ armDefaults (coverageArms program.arms),
      CaseDataTerms.Typing types code ((defaultDomains code).denote F))
    (arms : ∀ arm ∈ program.arms,
      CaseEvaluation.ArmTyping (CaseDataTerms.DefaultTyped types) (CaseDataTerms.GuardTyped types)
        (CaseDataTerms.BodyTyped types) arm (Ty.variants (semanticRow row)) target)
    (checked : checkVariants defaultDomains (coverageArms program.arms) row = true)
    (outer : Bindings F) (valid : BindingsHold types outer) :
    ∃ result, (eval floatCheck outer program).result = .ok (some result) ∧ target result :=
  typing_evaluates floatCheck (.variants row scrutinee defaults arms ((checkVariants_exact _ _ _).mp checked)) outer valid

end Yulang.CaseDataProgram
