import Yulang.ScopedCaseDataProgram

/-!
# Scope and control regressions for answered pattern questions

The integer examples are quantified over their actual values. They establish
complete observations, not just final result shapes. No floating-point or
arithmetic evaluator is assumed by these regressions.
-/

namespace Yulang.ScopedCaseExamples

open CaseValues LiteralValues EvaluationTrace

abbrev Data := CaseDataTerms.Expr Empty
abbrev Pat := CasePatterns.Pattern Empty Data

def floatCheck : Empty → Empty → Bool := fun value => nomatch value
def integer (value : Int) : Value Empty := .literal (.int value)
def intType : Ty Empty := Ty.literal .int

def sequentialPattern : Pat :=
  .field 0 (.bind 0) (.defaultField 1 (.var 0) (.bind 1) .recordEnd)

def sequentialInput : Ty Empty := Ty.inter (Ty.required 0 intType) (Ty.optional 1 intType)

theorem sequential_total :
    ScopedCasePatterns.TotalTyping CaseDataTerms.Typing [(0, intType)] sequentialPattern
      sequentialInput [(0, intType), (1, Ty.union intType intType)] := by
  have records : Ty.Le sequentialInput Ty.records :=
    fun value valid => Ty.optional_records 1 intType value valid.2
  refine .field (fun _ valid => valid.1) .bind ?_
  exact .defaultField (fun _ valid => valid.2) (.var rfl) .bind (.narrow records .recordEnd)

def program (inside : Int) : ScopedCaseDataProgram.Program Empty :=
  ⟨.value (.record [(0, integer inside)]), [⟨sequentialPattern, none, .var 1⟩]⟩

theorem program_typed (inside : Int) :
    ScopedCaseDataProgram.Typing [(0, intType)] (program inside) intType := by
  refine .caseE sequentialInput (.widen .value ?_) ?_ ?_
  · intro value valid
    cases valid
    constructor
    · exact ⟨integer inside, rfl, rfl⟩
    · intro value found
      cases found
  · intro arm member
    have same : arm = ⟨sequentialPattern, none, .var 1⟩ := by simpa [program] using member
    subst arm
    refine ⟨(PatternBindingChecks.check_exact _).mp (by decide),
      .arm sequential_total.typing (fun code absent => by cases absent) ?_⟩
    exact .widen (.var rfl) (fun value valid => valid.elim id id)
  · exact ⟨⟨sequentialPattern, none, .var 1⟩, by simp [program], rfl, _, sequential_total⟩

/-- Q4: a previously bound name shadows its namesake in the outer scope. -/
theorem shadowed_outer_written_order (inside outside : Int) :
    ScopedCaseDataProgram.eval floatCheck [(0, integer outside)] (program inside) =
      ⟨[.scrutinee, .source (.value (.record [(0, integer inside)])), .arm 0,
        .source (.var 0), .body 0, .source (.var 1)], .ok (some (integer inside))⟩ := rfl

theorem shadowed_outer_from_typing (inside outside : Int) :
    ∃ value, (ScopedCaseDataProgram.eval floatCheck [(0, integer outside)] (program inside)).result =
      .ok (some value) ∧ intType value :=
  ScopedCaseDataProgram.typing_evaluates floatCheck (program_typed inside) _ (.cons rfl .nil)

/-- A surrounding tuple component is also earlier in the same pattern. -/
theorem nested_default_sees_preceding_binding (inside outside : Int) :
    ScopedCasePatterns.run floatCheck CaseDataTerms.defaultEval [(0, integer outside)]
      (.pair (.bind 0) (.defaultField 1 (.var 0) (.bind 1) .recordEnd))
      (.pair (integer inside) (.record [])) =
      ⟨[.source (.var 0)], .ok (some [(0, integer inside), (1, integer inside)])⟩ := rfl

def branchLocal : Pat :=
  .or
    (.field 0 (.bind 0) (.field 1 (.literal (.bool true)) (.field 2 (.bind 1) .recordEnd)))
    (.defaultField 9 (.var 0) (.bind 0) (.field 2 (.bind 1) .recordEnd))

theorem branch_local_names_valid : PatternBindingChecks.check branchLocal = true := rfl

/-- A binder produced before a failed left branch's later mismatch must not
be visible to a default in the right branch. -/
theorem failed_branch_does_not_leak (inside outside last : Int) :
    ScopedCasePatterns.run floatCheck CaseDataTerms.defaultEval [(0, integer outside)] branchLocal
      (.record [(0, integer inside), (1, .literal (.bool false)), (2, integer last)]) =
      ⟨[.source (.var 0)], .ok (some [(0, integer outside), (1, integer last)])⟩ := rfl

/-- Q5: even arbitrary observable fallback code is not invoked after miss. -/
theorem preceding_miss_skips_default (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F)) (outer : Bindings F) (code : D) :
    ScopedCasePatterns.run floatCheck defaultEval outer
      (.field 0 (.literal (.bool true)) (.defaultField 1 code (.bind 1) .recordEnd))
      (.record [(0, .literal (.bool false))]) = CasePatterns.miss := rfl

def falseGuardProgram (first last : Int) : ScopedCaseDataProgram.Program Empty :=
  ⟨.value (.pair (integer first) (integer last)),
    [⟨.or (.pair (.bind 0) .wildcard) (.pair .wildcard (.bind 0)),
      some (.value (.literal (.bool false))), .var 0⟩,
     ⟨.wildcard, none, .value (integer 0)⟩]⟩

/-- Q6: the first successful or branch is fixed before the guard. A false
guard visits the next arm once, with no second branch or second guard. -/
theorem false_guard_moves_to_next_arm (first last : Int) :
    ScopedCaseDataProgram.eval floatCheck [] (falseGuardProgram first last) =
      ⟨[.scrutinee, .source (.value (.pair (integer first) (integer last))),
        .arm 0, .guard 0, .source (.value (.literal (.bool false))),
        .arm 1, .body 1, .source (.value (integer 0))], .ok (some (integer 0))⟩ := rfl

end Yulang.ScopedCaseExamples
