import Yulang.CommonAlignedPatternAllocation
import Yulang.CommonArmEnvironmentGeneration

/-! Real guard/body generation in the source-checked canonical pattern
environment. Aggregate default/failure rows and coverage are separate. -/

namespace Yulang.CommonAlignedArmGeneration

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGeneration (DefaultTyping)
open CommonPatternAllocation (Slots assignment bindingValues bindingValues_complete)
open CommonAlignedPatternAllocation (withPattern)
open CommonArmEnvironmentGeneration (GuardTyping consumer consumer_exact)
open CasePatterns (Pattern)

inductive EnvironmentTyping (environment : List (Binding Common.model))
    (pattern : Pattern Empty Inference.Expr) (guard : Option Inference.Expr)
    (body : Inference.Expr) (input : Common.Ty) (guardRow : Common.Row)
    (result : Comp Common.model) : Prop where
  | arm {bindings : NamedTypes} :
      CommonAlignedPatternTyping.Typing (DefaultTyping environment) [] pattern input bindings →
      GuardTyping (semanticPrefix bindings ++ environment) guard guardRow →
      Typing Common.model (semanticPrefix bindings ++ environment) body result →
      EnvironmentTyping environment pattern guard body input guardRow result

def generateEnvironments (pattern : Pattern Empty Inference.Expr) (environment : SchemeEnv α)
    (guard : Option Inference.Expr) (body : Inference.Expr) (input : TyTerm α)
    (guardRow : RowTerm α) (result : CompTerm α) : Formula α :=
  if PatternBindingChecks.check pattern then
    withPattern pattern environment [] input (consumer pattern environment guard body guardRow result)
  else .bot

/-- Arbitrary source patterns/defaults, guard/body expressions, captured
environments, result computations and free assignments. Q7 and source
or-name sets are checked by the actual finite gate, without extra premises. -/
theorem generateEnvironments_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (guard : Option Inference.Expr) (body : Inference.Expr) (input : TyTerm α)
    (guardRow : RowTerm α) (result : CompTerm α) :
    (generateEnvironments pattern symbolic guard body input guardRow result).Holds Common.model ρ ↔
      EnvironmentTyping semantic pattern guard body (input.eval Common.model ρ)
        (guardRow.eval Common.model ρ) (result.eval Common.model ρ) := by
  cases checked : PatternBindingChecks.check pattern with
  | false =>
      simp only [generateEnvironments, checked, Bool.false_eq_true, ↓reduceIte, Formula.Holds]
      constructor
      · exact False.elim
      · intro typed
        cases typed with
        | arm patternTyped guardTyped bodyTyped =>
            have accepted := (PatternBindingChecks.check_exact pattern).mpr patternTyped.1
            rw [checked] at accepted
            cases accepted
  | true =>
      have valid := (PatternBindingChecks.check_exact pattern).mp checked
      simp only [generateEnvironments, checked, ↓reduceIte,
        CommonAlignedPatternAllocation.withPattern_exact pattern ρ symbolic semantic outer,
        consumer_exact pattern ρ symbolic semantic outer, evalTypes, List.map_nil]
      constructor
      · rintro ⟨values, patternTyped, guardTyped, bodyTyped⟩
        exact .arm ⟨valid, patternTyped⟩ guardTyped bodyTyped
      · intro typed
        cases typed with
        | arm patternTyped guardTyped bodyTyped =>
          obtain ⟨values, same⟩ := bindingValues_complete pattern.names _ patternTyped.2.binding_names.symm
          exact ⟨values, same.symm ▸ patternTyped.2, same.symm ▸ guardTyped, same.symm ▸ bodyTyped⟩

end Yulang.CommonAlignedArmGeneration
