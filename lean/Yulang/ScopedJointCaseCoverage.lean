import Yulang.JointCaseCoverage
import Yulang.ScopedCaseCoverageSafety
import Yulang.ScopedCaseDataProgram

/-!
# Joint payload coverage reaches the scoped concrete case evaluator

Q4's lexical defaults and Q8's jointly exhaustive refutable payload arms use
one runtime. Default domains are upper bounds on independently typed data
expressions in each actual scope. The hypotheses contain no successful
evaluation or already-matching arm assumption.
-/

namespace Yulang.ScopedJointCaseCoverage

open CaseValues CaseCoverage LiteralValues EvaluationTrace
open ScopedCasePatterns (DefaultSound)
open ScopedCaseCoverage (DefaultBounded)
open JointCaseCoverage (TagCovered RowCovered)

theorem tag_covered_arms_match (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval) (domains : D → Domain)
    (bounded : DefaultBounded DefaultTyped domains)
    (arms : List (CaseEvaluation.Arm F D G B))
    (typed : ∀ arm ∈ arms,
      ∃ bindings, ScopedCasePatterns.Typing DefaultTyped types arm.pattern input bindings)
    (tag : Nat) (payload : Domain) (coverage : TagCovered domains (coverageArms arms) tag payload)
    (environment : Bindings F) (valid : BindingsHold types environment)
    (value : Value F) (valueValid : input (.variant tag value)) (domainValid : payload.denote F value) :
    ∃ arm ∈ arms, arm.guard = none ∧
      ∃ matched, (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern
        (.variant tag value)).result = .ok (some matched) := by
  cases coverage with
  | whole total =>
      exact ScopedCaseCoverage.covered_arms_match floatCheck defaultEval defaults domains bounded arms
        typed _ total environment valid (.variant tag value) valueValid ⟨rfl, domainValid⟩
  | parts total =>
      obtain ⟨cell, partition, cellValid⟩ := domain_has_cell payload value domainValid
      exact ScopedCaseCoverage.covered_arms_match floatCheck defaultEval defaults domains bounded arms
        typed _ (total cell partition) environment valid (.variant tag value) valueValid ⟨rfl, cellValid⟩

theorem row_covered_arms_match (floatCheck : F → F → Bool)
    (defaultEval : Bindings F → D → Logged E R (Value F))
    (defaults : DefaultSound DefaultTyped defaultEval) (domains : D → Domain)
    (bounded : DefaultBounded DefaultTyped domains)
    (arms : List (CaseEvaluation.Arm F D G B)) (row : VariantRow)
    (typed : ∀ arm ∈ arms, ∃ bindings,
      ScopedCasePatterns.Typing DefaultTyped types arm.pattern (Ty.variants (semanticRow row)) bindings)
    (coverage : RowCovered domains (coverageArms arms) row)
    (environment : Bindings F) (valid : BindingsHold types environment)
    (value : Value F) (valueValid : Ty.variants (semanticRow row) value) :
    ∃ arm ∈ arms, arm.guard = none ∧
      ∃ matched, (ScopedCasePatterns.run floatCheck defaultEval environment arm.pattern value).result =
        .ok (some matched) := by
  have rowValid := (variantHolds_semanticRow row value).mpr valueValid
  cases value with
  | variant tag item =>
      obtain ⟨payload, found, payloadValid⟩ := rowValid
      exact tag_covered_arms_match floatCheck defaultEval defaults domains bounded arms typed tag payload
        ((JointCaseCoverage.rowCovered_iff _ _ _).mp coverage tag payload
          ((Variants.Merged.mem_iff_lookup _ _ _).mpr found)) environment valid item valueValid payloadValid
  | _ => cases rowValid

/-- A coverage approximation is certified at each default's current type
environment. The expression still has an independent syntax derivation. -/
def BoundedDefaultTyping (domains : CaseDataTerms.Expr F → Domain)
    (types : List (Nat × Ty F)) (code : CaseDataTerms.Expr F) (target : Ty F) : Prop :=
  CaseDataTerms.Typing types code target ∧ Ty.Le target ((domains code).denote F)

theorem bounded_defaults_sound (domains : CaseDataTerms.Expr F → Domain) :
    DefaultSound (BoundedDefaultTyping domains) CaseDataTerms.defaultEval :=
  fun _ _ _ typed environment valid => CaseDataTerms.typing_evaluates typed.1 environment valid

theorem bounded_defaults_domain (domains : CaseDataTerms.Expr F → Domain) :
    DefaultBounded (BoundedDefaultTyping domains) domains := fun _ _ _ typed => typed.2

inductive Typing (domains : CaseDataTerms.Expr F → Domain) (types : List (Nat × Ty F)) :
    CaseDataProgram.Program F → Ty F → Prop where
  | caseE (row : VariantRow)
      (scrutinee : CaseDataTerms.Typing types program.scrutinee (Ty.variants (semanticRow row)))
      (arms : ∀ arm ∈ program.arms,
        PatternBindingChecks.NamesValid arm.pattern ∧
          ScopedCaseEvaluation.ArmTyping (BoundedDefaultTyping domains) (CaseDataTerms.GuardTyped types)
            (CaseDataTerms.BodyTyped types) types arm (Ty.variants (semanticRow row)) target)
      (coverage : RowCovered domains (coverageArms program.arms) row) :
      Typing domains types program target

/-- Independent data typing, static name validity and joint row coverage
imply successful evaluation of the actual scoped program on every valid
outer environment. Every produced value has the declared result type. -/
theorem typing_evaluates (floatCheck : F → F → Bool)
    (typed : Typing domains types program target)
    (outer : Bindings F) (valid : BindingsHold types outer) :
    ∃ result, (ScopedCaseDataProgram.eval floatCheck outer program).result = .ok (some result) ∧
      target result := by
  cases typed with
  | caseE row source arms coverage =>
      obtain ⟨value, evaluated, valueValid⟩ := CaseDataTerms.typing_evaluates source outer valid
      have patternTyped : ∀ arm ∈ program.arms, ∃ bindings,
          ScopedCasePatterns.Typing (BoundedDefaultTyping domains) types arm.pattern
            (Ty.variants (semanticRow row)) bindings := by
        intro arm member
        cases (arms arm member).2 with
        | arm pattern _ _ => exact ⟨_, pattern⟩
      have matching := row_covered_arms_match floatCheck CaseDataTerms.defaultEval
        (bounded_defaults_sound domains) domains (bounded_defaults_domain domains) program.arms row
        patternTyped coverage outer valid value valueValid
      obtain ⟨result, selected, resultValid⟩ := ScopedCaseEvaluation.runArms_progress floatCheck
        CaseDataTerms.defaultEval outer (CaseDataTerms.guardEval outer) (CaseDataTerms.bodyEval outer)
        (bounded_defaults_sound domains) (CaseDataTerms.guard_sound outer types valid)
        (CaseDataTerms.body_sound outer types valid) program.arms (fun arm member => (arms arm member).2)
        value valueValid matching 0 valid
      exact ⟨result, by simpa [ScopedCaseDataProgram.eval, ScopedCaseEvaluation.eval, Logged.bind_result,
        evaluated, Except.bind] using selected, resultValid⟩

theorem typed_bindings_accepted (typed : Typing domains types program target) :
    ScopedCaseDataProgram.checkBindings program = true := by
  apply (ScopedCaseDataProgram.checkBindings_exact program).mpr
  cases typed with
  | caseE _ _ arms _ => exact fun arm member => (arms arm member).1

theorem typed_checkedEval (floatCheck : F → F → Bool) (typed : Typing domains types program target)
    (outer : Bindings F) :
    ScopedCaseDataProgram.checkedEval floatCheck outer program =
      some (ScopedCaseDataProgram.eval floatCheck outer program) := by
  simp [ScopedCaseDataProgram.checkedEval, typed_bindings_accepted typed]

theorem typed_no_unmatched (floatCheck : F → F → Bool) (typed : Typing domains types program target)
    (outer : Bindings F) (valid : BindingsHold types outer) :
    (ScopedCaseDataProgram.eval floatCheck outer program).result ≠ .ok none := by
  obtain ⟨value, evaluated, _⟩ := typing_evaluates floatCheck typed outer valid
  simp [evaluated]

end Yulang.ScopedJointCaseCoverage
