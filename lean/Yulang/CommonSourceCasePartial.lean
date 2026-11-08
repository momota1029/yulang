import Yulang.CommonSourceArmGeneration
import Yulang.CommonSourcePatternPartialSafety
import Yulang.CommonAlignedCaseEvaluation

/-! Source arm environments imply partial value safety of ordered execution,
given the exact successful-return contracts still required from source leaf
evaluation. Default, guard and body errors remain possible; this is neither
an effect-row bound nor a coverage/termination theorem. -/

namespace Yulang.CommonSourceCasePartial

open Core
open PresenceGeneration (Comp)
open CommonPatternEnvironment (NamedTypes)
open CommonPatternTyping (valueAt bindingTypes)
open CommonPatternPartialSafety (PartialHolds DefaultPartialSound)
open CommonPatternSourceScope (corePrefix)
open CommonPatternSourceElaboration (DefaultTyped)
open CommonSourceArmGeneration (EnvironmentTyping)
open CaseValues EvaluationTrace
open CaseEvaluation (Arm Event)

def PartialResult (target : Common.Ty) : Except R (Option (Value Empty)) → Prop
  | .error _ => True
  | .ok none => True
  | .ok (some value) => valueAt target value

def BodyPartialSound (outerNames : List Nat) (environment : List (CommonSyntax.Binding Common.model))
    (bodyEval : CaseDataTerms.Expr Empty → Bindings Empty → Logged (Event E) R (Value Empty)) : Prop :=
  ∀ bindings code result,
    CommonSyntax.Typing Common.model (corePrefix bindings ++ environment)
      (Data.embed (bindings.map Prod.fst ++ outerNames) code) result →
    ∀ actual, BindingsHold (bindingTypes bindings) actual →
      ∀ value, (bodyEval code actual).result = .ok value → valueAt result.1 value

theorem testArm_partial (floatCheck : Empty → Empty → Bool)
    {patternDefaults : NamedTypes → D → Common.Ty → Prop}
    (defaultEval : Bindings Empty → D → Logged (Event E) R (Value Empty))
    (defaults : DefaultPartialSound patternDefaults defaultEval)
    (guardEval : G → Bindings Empty → Logged (Event E) R Bool)
    (arm : Arm Empty D G B)
    (typed : CommonSourcePatternTyping.Typing patternDefaults [] arm.pattern input bindings)
    (value : Value Empty) (valid : valueAt input value) (index : Nat) :
    PartialHolds bindings
      (CommonAlignedCaseEvaluation.testArm floatCheck defaultEval [] guardEval index arm value).result := by
  have safe := CommonSourcePatternPartialSafety.typing_matches_partial floatCheck defaultEval defaults
    typed.2 typed.1 [] .nil value valid
  simp only [CommonAlignedCaseEvaluation.testArm, Logged.bind_result]
  cases observed : (CommonPatternAlignedMatcher.run floatCheck defaultEval [] arm.pattern value).result with
  | error => trivial
  | ok option =>
      rw [observed] at safe
      cases option with
      | none => trivial
      | some matched =>
          cases guard : arm.guard with
          | none => exact safe
          | some code =>
              simp only [Except.bind, Logged.prepend_result, Logged.bind_result]
              cases returned : (guardEval code matched).result with
              | error => trivial
              | ok accepted => cases accepted <;> first | trivial | exact safe

theorem runArms_partial (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → CaseDataTerms.Expr Empty → Logged (Event E) R (Value Empty))
    (defaults : DefaultPartialSound (DefaultTyped outerNames environment) defaultEval)
    (guardEval : CaseDataTerms.Expr Empty → Bindings Empty → Logged (Event E) R Bool)
    (bodyEval : CaseDataTerms.Expr Empty → Bindings Empty → Logged (Event E) R (Value Empty))
    (bodies : BodyPartialSound outerNames environment bodyEval)
    (arms : List (Arm Empty (CaseDataTerms.Expr Empty) (CaseDataTerms.Expr Empty) (CaseDataTerms.Expr Empty)))
    (typed : ∀ arm ∈ arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body input guardRow result)
    (value : Value Empty) (valid : valueAt input value) (index : Nat) :
    PartialResult result.1
      (CommonAlignedCaseEvaluation.runArms floatCheck defaultEval [] guardEval bodyEval value index arms).result := by
  induction arms generalizing index with
  | nil => trivial
  | cons arm rest ih =>
      obtain ⟨guardRow, armTyped⟩ := typed arm List.mem_cons_self
      cases armTyped with
      | arm patternTyped guardTyped bodyTyped =>
          have safe := testArm_partial floatCheck defaultEval defaults guardEval arm patternTyped value valid index
          simp only [CommonAlignedCaseEvaluation.runArms, Logged.prepend_result, Logged.bind_result]
          cases observed : (CommonAlignedCaseEvaluation.testArm floatCheck defaultEval [] guardEval index arm value).result with
          | error => trivial
          | ok option =>
              rw [observed] at safe
              cases option with
              | none => exact ih (fun arm member => typed arm (List.mem_cons_of_mem _ member)) (index + 1)
              | some matched =>
                  have bodySafe := bodies _ _ _ bodyTyped matched safe
                  simp only [Except.bind, Logged.prepend_result, Logged.bind_result]
                  cases returned : (bodyEval arm.body matched).result with
                  | error => trivial
                  | ok output => exact bodySafe output returned

/-- The original actual source evaluator has the same partial value safety
when callbacks depend on names, as already proved for concrete data leaves.
No callback is required to return successfully; guards may also fail. -/
theorem actual_runArms_partial (floatCheck : Empty → Empty → Bool)
    (defaultEval : Bindings Empty → CaseDataTerms.Expr Empty → Logged (Event E) R (Value Empty))
    (defaults : DefaultPartialSound (DefaultTyped outerNames environment) defaultEval)
    (defaultNames : CommonPatternAlignedMatcher.DefaultInvariant defaultEval)
    (guardEval : CaseDataTerms.Expr Empty → Bindings Empty → Logged (Event E) R Bool)
    (guardNames : CommonAlignedCaseEvaluation.NamedInvariant guardEval)
    (bodyEval : CaseDataTerms.Expr Empty → Bindings Empty → Logged (Event E) R (Value Empty))
    (bodies : BodyPartialSound outerNames environment bodyEval)
    (bodyNames : CommonAlignedCaseEvaluation.NamedInvariant bodyEval)
    (arms : List (Arm Empty (CaseDataTerms.Expr Empty) (CaseDataTerms.Expr Empty) (CaseDataTerms.Expr Empty)))
    (typed : ∀ arm ∈ arms, ∃ guardRow,
      EnvironmentTyping outerNames environment arm.pattern arm.guard arm.body input guardRow result)
    (value : Value Empty) (valid : valueAt input value) (index : Nat) :
    PartialResult result.1
      (ScopedCaseEvaluation.runArms floatCheck defaultEval [] guardEval bodyEval value index arms).result := by
  have sourceValid : ∀ arm ∈ arms, PatternBindingChecks.NamesValid arm.pattern := by
    intro arm member
    obtain ⟨guardRow, armTyped⟩ := typed arm member
    cases armTyped with | arm patternTyped guardTyped bodyTyped => exact patternTyped.1
  rw [← CommonAlignedCaseEvaluation.runArms_eq floatCheck defaultEval defaultNames [] []
    (fun _ => rfl) guardEval guardNames bodyEval bodyNames value index arms sourceValid]
  exact runArms_partial floatCheck defaultEval defaults guardEval bodyEval bodies arms typed value valid index

end Yulang.CommonSourceCasePartial
