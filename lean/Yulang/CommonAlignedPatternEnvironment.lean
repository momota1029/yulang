import Yulang.CommonAlignedPatternAllocation
import Yulang.CommonAlignedPatternPartialSafety

/-! Source-checked shared pattern environments and actual successful aligned
match bindings. Default partial correctness is explicit; row/presence and
full source default evaluation remain separate B3/B5 integration obligations. -/

namespace Yulang.CommonAlignedPatternEnvironment

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGeneration (DefaultTyping)
open CommonPatternAllocation (Slots assignment bindingValues bindingValues_complete)
open CommonAlignedPatternAllocation (constraints)
open CasePatterns (Pattern)

def checkedConstraints (pattern : Pattern Empty Inference.Expr) (environment : SchemeEnv α)
    (priorBindings : NamedTerms α) (input : TyTerm α) : Formula (Slots α pattern.names.length) :=
  if PatternBindingChecks.check pattern then constraints pattern environment priorBindings input else .bot

theorem checked_constraints_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α)
    (values : Fin pattern.names.length → Comp Common.model) :
    (checkedConstraints pattern symbolic priorBindings input).Holds Common.model (assignment ρ values) ↔
      CommonAlignedPatternTyping.Typing (DefaultTyping semantic) (evalTypes ρ priorBindings)
        pattern (input.eval Common.model ρ) (bindingValues pattern.names values) := by
  unfold checkedConstraints
  split
  · rename_i valid
    simp only [CommonAlignedPatternTyping.Typing,
      (PatternBindingChecks.check_exact pattern).mp valid, true_and,
      CommonAlignedPatternAllocation.constraints_exact pattern ρ symbolic semantic outer priorBindings input]
  · rename_i invalid
    have notValid : ¬ PatternBindingChecks.NamesValid pattern :=
      fun h => invalid ((PatternBindingChecks.check_exact pattern).mpr h)
    simp only [Formula.Holds, CommonAlignedPatternTyping.Typing, notValid, false_and]

/-- Prescribed ordered binding types are recovered literally by one shared
allocation, including both alternatives of an accepted reordered or pattern. -/
theorem checked_bindings_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α) (bindings : NamedTypes) :
    (∃ values : Fin pattern.names.length → Comp Common.model,
      (checkedConstraints pattern symbolic priorBindings input).Holds Common.model (assignment ρ values) ∧
        bindingValues pattern.names values = bindings) ↔
      CommonAlignedPatternTyping.Typing (DefaultTyping semantic) (evalTypes ρ priorBindings)
        pattern (input.eval Common.model ρ) bindings := by
  simp only [checked_constraints_exact pattern ρ symbolic semantic outer priorBindings input]
  constructor
  · rintro ⟨values, typed, same⟩; exact same ▸ typed
  · intro typed
    obtain ⟨values, same⟩ := bindingValues_complete pattern.names bindings typed.2.binding_names.symm
    exact ⟨values, same.symm ▸ typed, same⟩

/-- Any actual aligned match success has exactly the types of its generated
shared slot list. Defaults need only preserve successful returned values;
errors and non-success are not ruled out by this theorem. -/
theorem generated_match_bindings (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (priorBindings : NamedTerms α) (input : TyTerm α)
    (values : Fin pattern.names.length → Comp Common.model)
    (generated : (checkedConstraints pattern symbolic priorBindings input).Holds Common.model (assignment ρ values))
    (floatCheck : Empty → Empty → Bool)
    (defaultEval : CaseValues.Bindings Empty → Inference.Expr → EvaluationTrace.Logged E R Core.CommonData.Value)
    (defaults : CommonPatternPartialSafety.DefaultPartialSound (DefaultTyping semantic) defaultEval)
    (environment : CaseValues.Bindings Empty)
    (environmentValid : CaseValues.BindingsHold
      (CommonPatternTyping.bindingTypes (evalTypes ρ priorBindings)) environment)
    (value : Core.CommonData.Value)
    (valueValid : CommonPatternTyping.valueAt (input.eval Common.model ρ) value)
    (returned : CaseValues.Bindings Empty)
    (matched : (CommonPatternAlignedMatcher.run floatCheck defaultEval environment pattern value).result =
      .ok (some returned)) :
    CaseValues.BindingsHold (CommonPatternTyping.bindingTypes (bindingValues pattern.names values)) returned := by
  have typed := (checked_constraints_exact pattern ρ symbolic semantic outer priorBindings input values).mp generated
  have safe := CommonAlignedPatternPartialSafety.typing_matches_partial floatCheck defaultEval defaults typed.2 typed.1
    environment environmentValid value valueValid
  rw [matched] at safe
  exact safe

end Yulang.CommonAlignedPatternEnvironment
