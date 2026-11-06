import Yulang.CaseTree

/-!
# Typed finite nesting with concrete binding use

The outer case evaluates a case as its scrutinee, then executes another case
as its selected body. All three cases bind their actual selected value, and
the final body resolves the innermost binding. No default, guard or body
success premise is supplied to the safety theorem.
-/

namespace Yulang.CaseTreeExamples

open CaseValues CaseTree CaseCoverage LiteralValues EvaluationTrace

def floatCheck : Empty → Empty → Bool := Empty.elim

def unusedDomains : Data Empty → Domain := fun _ => .any

def intCode (value : Int) : Data Empty := .value (.literal (.int value))

def identity (name : Nat) (source : Expr Empty) : Expr Empty :=
  .caseE source (.cons (.bind name) none (.leaf (.var name)) .nil)

theorem identity_typed (types : List (Nat × Ty Empty)) (name : Nat) (source : Expr Empty)
    (typed : Typing types source (Ty.literal .int)) :
    Typing types (identity name source) (Ty.literal .int) := by
  apply case_typing_of_checked types source _ (.base .int) _ unusedDomains typed
  · exact .cons .bind (by intro code absent; cases absent)
      (.leaf (.var (by simp [CaseDataTerms.lookupType, Domain.denote]))) .nil
  · intro code used
    simp [Arms.coverage, armDefaults, patternDefaults] at used
  · rfl

def nested (value : Int) : Expr Empty :=
  .caseE (identity 3 (.leaf (intCode value)))
    (.cons (.bind 4) none (identity 5 (.leaf (.var 4))) .nil)

theorem nested_typed (value : Int) : Typing [] (nested value) (Ty.literal .int) := by
  apply case_typing_of_checked [] _ _ (.base .int) _ unusedDomains
  · apply identity_typed
    exact .leaf (.widen .value (by intro item same; cases same; rfl))
  · exact .cons .bind (by intro code absent; cases absent)
      (identity_typed _ _ _ (.leaf (.var rfl))) .nil
  · intro code used
    simp [Arms.coverage, armDefaults, patternDefaults] at used
  · rfl

theorem nested_evaluates_from_typing (value : Int) :
    ∃ result, (eval floatCheck [] (nested value)).result = .ok (some result) ∧
      Ty.literal .int result :=
  closed_typing_evaluates floatCheck _ _ (nested_typed value)

/-- Evaluation visits a complete inner scrutinee case before the outer arm,
then evaluates the nested body using the bindings that arm actually produced. -/
theorem nested_written_order (value : Int) :
    eval floatCheck [] (nested value) =
      ⟨[.scrutinee, .scrutinee, .source (intCode value), .arm 0, .body 0, .source (.var 3),
        .arm 0, .body 0, .scrutinee, .source (.var 4), .arm 0, .body 0, .source (.var 5)],
        .ok (some (.literal (.int value)))⟩ := rfl

/-- The raw syntax contains failing cases; their success is not smuggled into
the theorem as a universal evaluator contract. -/
theorem uncovered_cannot_be_typed (value : Int) (target : Ty Empty) :
    ¬ Typing [] (.caseE (.leaf (intCode value)) .nil) target := by
  intro typed
  exact typed_no_unmatched floatCheck [] [] .nil _ target typed rfl

end Yulang.CaseTreeExamples
