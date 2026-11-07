import Yulang.CommonCaseBaseCoverage

/-! Joint tuple/variant coverage over all literal bases reaches source evaluation.
Constructor-tree Common bounds supply the domain premise internally. A
choice of multiple variant tags still needs the separate merged-row bridge. -/

namespace Yulang.CommonCaseBaseOrdered

open CaseValues EvaluationTrace
open CaseEvaluation (Arm Event ResultHolds)
open CommonCaseBaseCells (Shape InShape)

theorem covered_not_unmatched (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → D → Logged (Event E) R (Value Empty)) (environment : Bindings Empty)
    (guardEval : G → Bindings Empty → Logged (Event E) R Bool)
    (bodyEval : B → Bindings Empty → Logged (Event E) R (Value Empty))
    (shape : Shape) (arms : List (Arm Empty D G B)) (coverage : CommonCaseBaseCoverage.check shape arms = true)
    (value : Value Empty) (domainValid : InShape shape value) (index : Nat) :
    (ScopedCaseEvaluation.runArms floatCheck defaultEval environment guardEval bodyEval value index arms).result ≠ .ok none := by
  intro unmatched
  have misses := (CommonCaseOrderedPaths.runArms_unmatched_exact floatCheck defaultEval environment guardEval bodyEval
    value index arms).mp unmatched
  obtain ⟨arm, member, unguarded, bindings, matched⟩ :=
    (CommonCaseBaseCoverage.check_matches_exact floatCheck defaultEval environment shape arms).mp coverage value domainValid
  exact CommonCaseIntegerOrdered.allMiss_no_unguarded_match floatCheck defaultEval environment guardEval
    misses arm member unguarded bindings matched

inductive Tree where
  | base : Inference.Base → Tree
  | pair : Tree → Tree → Tree
  | variant : Nat → Tree → Tree
  deriving DecidableEq, Repr

def Tree.shape : Tree → Shape
  | .base kind => .base kind
  | .pair first last => .pair first.shape last.shape
  | .variant tag child => .variant tag child.shape

def Tree.type : Tree → Common.Ty
  | .base kind => .base kind
  | .pair first last => Common.pair first.type last.type
  | .variant tag child => Common.variant tag child.type

open Core
open PresenceGeneration (Comp)

/-- Arbitrary Common subjects, including regular types and arbitrary rows.
No successful match, source support check or domain oracle is assumed. -/
theorem Tree.readout (tree : Tree) (typed : CommonData.ValueTyping Common.model value result)
    (below : Common.Subtype result.1 tree.type) : InShape tree.shape value := by
  induction tree generalizing value result with
  | base base =>
      obtain ⟨literal, rfl, scalar⟩ := CommonPatternLookup.literal_of_base typed base below
      exact .base scalar
  | pair first last ihf ihl =>
      obtain ⟨left, right, rfl, leftType, rightType⟩ := CommonPatternLookup.pair_components typed first.type last.type below
      exact .pair (ihf leftType (Common.subtype_refl _)) (ihl rightType (Common.subtype_refl _))
  | variant tag payload ih =>
      obtain ⟨item, rfl, itemType⟩ := CommonPatternLookup.variant_payload typed tag payload.type below
      exact .variant (ih itemType (Common.subtype_refl _))

open CommonPatternDataSafety (EnvironmentHolds)
open CommonPatternSourceArmGeneration (EnvironmentTyping)
open CommonPatternSourceArmsSolved (SourceArm)
open CommonPatternTyping (valueAt)

theorem runArms_progress (outer : EnvironmentHolds outerNames environment actualOuter)
    (shape : Shape) (arms : List SourceArm)
    (typed : ∀ arm ∈ arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body input guardRow result)
    (coverage : CommonCaseBaseCoverage.check shape arms = true)
    (floatCheck : Empty → Empty → Bool) (value : CommonData.Value) (valid : valueAt input value)
    (domainValid : InShape shape value) (index : Nat) :
    ∃ output, (ScopedCaseEvaluation.runArms floatCheck CaseDataTerms.defaultEval actualOuter
        (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) value index arms).result = .ok (some output) ∧
      valueAt result.1 output := by
  have safe := CommonPatternConcreteCaseTotal.actual_runArms_safe outer arms typed floatCheck value valid index
  have selected := covered_not_unmatched floatCheck CaseDataTerms.defaultEval actualOuter
    (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) shape arms coverage value domainValid index
  cases observed : (ScopedCaseEvaluation.runArms floatCheck CaseDataTerms.defaultEval actualOuter
      (CaseDataTerms.guardEval actualOuter) (CaseDataTerms.bodyEval actualOuter) value index arms).result with
  | error => rw [observed] at safe; cases safe
  | ok option =>
      cases option with
      | none => exact False.elim (selected observed)
      | some output => exact ⟨output, rfl, by simpa only [observed, ResultHolds] using safe⟩

/-- A real typed source subject bounded by an base constructor tree, all
finite typed source arms, and the real finite joint-cell check suffice for
successful actual Program evaluation. The type/domain bridge is internal. -/
theorem tree_program_progress (outer : EnvironmentHolds outerNames environment actualOuter)
    (program : CaseDataProgram.Program Empty) (subject : Comp Common.model)
    (subjectTyped : CommonSyntax.Typing Common.model environment (Data.embed outerNames program.scrutinee) subject)
    (typed : ∀ arm ∈ program.arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body subject.1 guardRow result)
    (tree : Tree) (inputTree : Common.Subtype subject.1 tree.type)
    (coverage : CommonCaseBaseCoverage.check tree.shape program.arms = true) (floatCheck : Empty → Empty → Bool) :
    ∃ output, (ScopedCaseDataProgram.eval floatCheck actualOuter program).result = .ok (some output) ∧ valueAt result.1 output := by
  obtain ⟨value, evaluated, safe⟩ := CommonPatternDataSafety.typing_evaluates program.scrutinee outerNames environment
    actualOuter subject outer subjectTyped
  have valueTyped := CommonPatternLookup.typing_change_result safe (Comp.pure Common.model subject.1) (Common.subtype_refl _)
  obtain ⟨output, selected, outputType⟩ := runArms_progress outer tree.shape program.arms typed coverage
    floatCheck value valueTyped (tree.readout safe inputTree) 0
  exact ⟨output, by simpa only [ScopedCaseDataProgram.eval, ScopedCaseEvaluation.eval, Logged.prepend_result,
    Logged.bind_result, evaluated, Except.bind] using selected, outputType⟩

end Yulang.CommonCaseBaseOrdered
