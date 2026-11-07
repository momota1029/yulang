import Yulang.CommonArmEnvironmentGeneration
import Yulang.CommonPatternPartialSafety
import Yulang.PatternBindingChecks

/-!
# Source binding validation and actual successful match bindings

The static gate is the existing Q7/name-set check. The positional or-alignment
boundary of the intermediate Common judgment is retained explicitly.
Partial runtime correctness admits errors; it does not assert their row bounds.
-/

namespace Yulang.CommonPatternSourceChecks

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGeneration
open CommonPatternAllocation
open CommonPatternPartialSafety
open CasePatterns (Pattern)

def generateCheckedPattern (pattern : Pattern Empty Inference.Expr) (environment : SchemeEnv α)
    (priorBindings : NamedTerms α) (input : TyTerm α) : Formula α :=
  if PatternBindingChecks.check pattern then
    generateAllocatedPattern pattern environment priorBindings input
  else .bot

theorem generateCheckedPattern_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α) :
    (generateCheckedPattern pattern symbolic priorBindings input).Holds Common.model ρ ↔
      PatternBindingChecks.NamesValid pattern ∧
        ∃ bindings, CommonPatternTyping.Typing (DefaultTyping semantic) (evalTypes ρ priorBindings)
          pattern (input.eval Common.model ρ) bindings := by
  simp only [generateCheckedPattern]
  split
  · rename_i valid
    simp only [generateAllocatedPattern_exact pattern ρ symbolic semantic outer,
      (PatternBindingChecks.check_exact pattern).mp valid, true_and]
  · rename_i invalid
    have notValid : ¬ PatternBindingChecks.NamesValid pattern :=
      fun h => invalid ((PatternBindingChecks.check_exact pattern).mpr h)
    simp only [Formula.Holds, notValid, false_and]

/-- Every generated shared assignment has the actual scoped matcher's declared
binding types on success. Default errors remain possible under the explicit
partial-success premise; no termination/success assumption is hidden. -/
theorem generated_matches_partial (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α)
    (values : Fin pattern.names.length → Comp Common.model)
    (generated : (constraints pattern symbolic priorBindings input).Holds Common.model (assignment ρ values))
    (floatCheck : Empty → Empty → Bool)
    (defaultEval : CaseValues.Bindings Empty → Inference.Expr →
      EvaluationTrace.Logged E R Core.CommonData.Value)
    (defaults : DefaultPartialSound (DefaultTyping semantic) defaultEval)
    (environment : CaseValues.Bindings Empty)
    (environmentValid : CaseValues.BindingsHold
      (CommonPatternTyping.bindingTypes (evalTypes ρ priorBindings)) environment)
    (value : Core.CommonData.Value)
    (valueValid : CommonPatternTyping.valueAt (input.eval Common.model ρ) value) :
    PartialHolds (bindingValues pattern.names values)
      (ScopedCasePatterns.run floatCheck defaultEval environment pattern value).result :=
  typing_matches_partial floatCheck defaultEval defaults
    ((constraints_exact pattern ρ symbolic semantic outer priorBindings input values).mp generated)
    environment environmentValid value valueValid

/-- A prescribed actual returned binding list is admitted by generated slots
iff it is admitted by an independent pattern environment. All assigned types
are recovered literally in the completeness direction. This does not assert
that matching succeeds or that every error is permitted by an effect row. -/
theorem returned_bindings_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α) (returned : CaseValues.Bindings Empty) :
    (∃ values : Fin pattern.names.length → Comp Common.model,
      (constraints pattern symbolic priorBindings input).Holds Common.model (assignment ρ values) ∧
        CaseValues.BindingsHold (CommonPatternTyping.bindingTypes (bindingValues pattern.names values)) returned) ↔
      ∃ bindings, CommonPatternTyping.Typing (DefaultTyping semantic) (evalTypes ρ priorBindings)
        pattern (input.eval Common.model ρ) bindings ∧
        CaseValues.BindingsHold (CommonPatternTyping.bindingTypes bindings) returned := by
  constructor
  · rintro ⟨values, generated, returnedValid⟩
    exact ⟨_, (constraints_exact pattern ρ symbolic semantic outer priorBindings input values).mp generated,
      returnedValid⟩
  · rintro ⟨bindings, typed, returnedValid⟩
    obtain ⟨values, generated, same⟩ :=
      (allocated_bindings_exact pattern ρ symbolic semantic outer priorBindings input bindings).mpr typed
    exact ⟨values, generated, same.symm ▸ returnedValid⟩

end Yulang.CommonPatternSourceChecks
