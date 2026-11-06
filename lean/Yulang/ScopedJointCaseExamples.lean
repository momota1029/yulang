import Yulang.ScopedJointCaseCoverage
import Yulang.ScopedCaseExamples

/-!
# Q4 and Q8 in the same concrete execution

Two refutable arms split the Boolean half of one polyvariant payload. In
each arm, the record pattern binds an integer and uses that binding as a
later field's fallback. Its outer namesake is deliberately different.
-/

namespace Yulang.ScopedJointCaseExamples

open CaseValues CaseCoverage EvaluationTrace
open ScopedCaseExamples (integer intType floatCheck sequentialPattern)

abbrev Data := CaseDataTerms.Expr Empty

def recordDomain : Domain := .required 0 (.base .int) (.optional 1 (.base .int) .records)
def payloadDomain : Domain := .pair (.base .bool) recordDomain
def row : VariantRow := Variants.Merged.normalize Domain.union [(0, payloadDomain)]
def domains : Data → Domain := fun _ => .base .int

def arm (wanted : Bool) : CaseDataProgram.Arm Empty :=
  ⟨.variant 0 (.pair (.literal (.bool wanted)) sequentialPattern), none, .var 1⟩

def program (flag : Bool) (inside : Int) : CaseDataProgram.Program Empty :=
  ⟨.value (.variant 0 (.pair (.literal (.bool flag)) (.record [(0, integer inside)]))),
    [arm false, arm true]⟩

theorem record_pattern_typed :
    ScopedCasePatterns.Typing (ScopedJointCaseCoverage.BoundedDefaultTyping domains)
      [(0, intType)] sequentialPattern (recordDomain.denote Empty)
      [(0, intType), (1, Ty.union intType intType)] := by
  refine .field (fun _ valid => valid.1) .bind ?_
  refine .defaultField (fun _ valid => valid.2.1) ?_ .bind ?_
  · exact ⟨.var rfl, fun _ valid => valid⟩
  · exact .narrow (fun _ valid => valid.2.2) .recordEnd

theorem arm_typed (wanted : Bool) :
    ScopedCaseEvaluation.ArmTyping (ScopedJointCaseCoverage.BoundedDefaultTyping domains)
      (CaseDataTerms.GuardTyped [(0, intType)]) (CaseDataTerms.BodyTyped [(0, intType)])
      [(0, intType)] (arm wanted) (Ty.variants (semanticRow row)) intType := by
  refine .arm (.mergedVariant (semanticRow row) rfl
    (.pair (.literal (fun _ valid => valid)) record_pattern_typed)) ?_ ?_
  · intro code impossible; cases impossible
  · exact .widen (.var rfl) (fun value valid => valid.elim id id)

theorem joint_coverage_checked (flag : Bool) (inside : Int) :
    JointCaseCoverage.checkRow domains (coverageArms (program flag inside).arms) row = true := rfl

theorem whole_payload_checker_rejects (flag : Bool) (inside : Int) :
    CaseCoverage.checkVariants domains (coverageArms (program flag inside).arms) row = false := rfl

theorem program_typed (flag : Bool) (inside : Int) :
    ScopedJointCaseCoverage.Typing domains [(0, intType)] (program flag inside) intType := by
  refine .caseE row (.widen .value ?_) ?_
    ((JointCaseCoverage.checkRow_exact _ _ _).mp (joint_coverage_checked flag inside))
  · intro value valid
    cases valid
    refine ⟨payloadDomain.denote Empty, rfl, ?_⟩
    exact ⟨rfl, ⟨integer inside, rfl, rfl⟩, (fun _ impossible => by cases impossible), trivial⟩
  · intro selected member
    have alternatives : selected = arm false ∨ selected = arm true := by simpa [program] using member
    rcases alternatives with rfl | rfl
    all_goals exact ⟨(PatternBindingChecks.check_exact _).mp (by decide), arm_typed _⟩

/-- The jointly covered program executes with the scoped default semantics
for either Boolean payload and every inner/outer integer pair. -/
theorem typed_program_progress (flag : Bool) (inside outside : Int) :
    ∃ result, (ScopedCaseDataProgram.eval floatCheck [(0, integer outside)] (program flag inside)).result =
      .ok (some result) ∧ intType result :=
  ScopedJointCaseCoverage.typing_evaluates floatCheck (program_typed flag inside) _ (.cons rfl .nil)

theorem default_uses_pattern_binding (flag : Bool) (inside outside : Int) :
    (ScopedCaseDataProgram.eval floatCheck [(0, integer outside)] (program flag inside)).result =
      .ok (some (integer inside)) := by cases flag <;> rfl

end Yulang.ScopedJointCaseExamples
