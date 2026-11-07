import Yulang.CommonPatternAllocation

/-!
# Guard and body environments share the actual pattern allocation

These are the environment premises of an arm, not the full ordered-case
typing rule. Pattern-default rows, failure rows, coverage, and execution order
are deliberately not inferred by this intermediate relation.
-/

namespace Yulang.CommonArmEnvironmentGeneration

set_option backward.isDefEq.respectTransparency false

open Core.PresenceGeneration
open CommonPatternEnvironment
open CommonPatternGeneration
open CommonPatternAllocation
open CasePatterns (Pattern)

def GuardTyping (environment : List (Binding Common.model))
    (guard : Option Inference.Expr) (row : Common.Row) : Prop :=
  match guard with
  | none => Common.rowLe Common.rowEmpty row
  | some code => Typing Common.model environment code (.base .bool, row)

def generateGuard (environment : SchemeEnv α) (guard : Option Inference.Expr)
    (row : RowTerm α) : Formula α :=
  match guard with
  | none => .rowLe .empty row
  | some code => generate environment code ⟨.base .bool, row⟩

theorem generateGuard_exact (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (guard : Option Inference.Expr) (row : RowTerm α) :
    (generateGuard symbolic guard row).Holds Common.model ρ ↔
      GuardTyping semantic guard (row.eval Common.model ρ) := by
  cases guard with
  | none => rfl
  | some code =>
      exact generate_models_iff_typing Common.model code symbolic semantic ρ ⟨.base .bool, row⟩ outer

/-- Independent environment premises, with the same monomorphic pattern
bindings supplied to the guard and body. No constraint formula occurs here. -/
inductive EnvironmentTyping (environment : List (Binding Common.model))
    (pattern : Pattern Empty Inference.Expr) (guard : Option Inference.Expr)
    (body : Inference.Expr) (input : Common.Ty) (guardRow : Common.Row)
    (result : Comp Common.model) : Prop where
  | arm {bindings : NamedTypes} :
      CommonPatternTyping.Typing (DefaultTyping environment) [] pattern input bindings →
      GuardTyping (semanticPrefix bindings ++ environment) guard guardRow →
      Typing Common.model (semanticPrefix bindings ++ environment) body result →
      EnvironmentTyping environment pattern guard body input guardRow result

def consumer (pattern : Pattern Empty Inference.Expr) (environment : SchemeEnv α)
    (guard : Option Inference.Expr) (body : Inference.Expr) (guardRow : RowTerm α)
    (result : CompTerm α) : Formula (Slots α pattern.names.length) :=
  let inner := symbolicPrefix (bindingSlots pattern.names) ++
    environment.rename (ambient pattern.names.length)
  .and (generateGuard inner guard (guardRow.rename (ambient pattern.names.length)))
    (generate inner body (result.rename (ambient pattern.names.length)))

theorem consumer_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (guard : Option Inference.Expr) (body : Inference.Expr) (guardRow : RowTerm α)
    (result : CompTerm α) (values : Fin pattern.names.length → Comp Common.model) :
    (consumer pattern symbolic guard body guardRow result).Holds Common.model (assignment ρ values) ↔
      GuardTyping (semanticPrefix (bindingValues pattern.names values) ++ semantic) guard
        (guardRow.eval Common.model ρ) ∧
      Typing Common.model (semanticPrefix (bindingValues pattern.names values) ++ semantic) body
        (result.eval Common.model ρ) := by
  have related := monomorphic_prefix_environment_exact (assignment ρ values)
    (bindingSlots pattern.names) (symbolic.rename (ambient pattern.names.length)) semantic
    (outer.rename _ _ (assignment_ambient ρ values))
  rw [bindingSlots_eval] at related
  have guardExact := generateGuard_exact (assignment ρ values) _ _ related guard
    (guardRow.rename (ambient pattern.names.length))
  have bodyExact := generate_models_iff_typing Common.model body _ _ (assignment ρ values)
    (result.rename (ambient pattern.names.length)) related
  simp only [consumer, Formula.Holds, guardExact, bodyExact, RowTerm.eval_rename,
    CompTerm.eval_rename, assignment_ambient]

def generateEnvironments (pattern : Pattern Empty Inference.Expr) (environment : SchemeEnv α)
    (guard : Option Inference.Expr) (body : Inference.Expr) (input : TyTerm α)
    (guardRow : RowTerm α) (result : CompTerm α) : Formula α :=
  withPattern pattern environment [] input (consumer pattern environment guard body guardRow result)

/-- Arbitrary actual structural pattern/default code, guard/body expressions,
outer environments, result computations, and ambient assignments. The only
premise is the interpretation of the captured original environment. -/
theorem generateEnvironments_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (semantic : List (Binding Common.model)) (outer : EnvRel Common.model ρ symbolic semantic)
    (guard : Option Inference.Expr) (body : Inference.Expr) (input : TyTerm α)
    (guardRow : RowTerm α) (result : CompTerm α) :
    (generateEnvironments pattern symbolic guard body input guardRow result).Holds Common.model ρ ↔
      EnvironmentTyping semantic pattern guard body (input.eval Common.model ρ)
        (guardRow.eval Common.model ρ) (result.eval Common.model ρ) := by
  simp only [generateEnvironments, withPattern_exact pattern ρ symbolic semantic outer,
    consumer_exact pattern ρ symbolic semantic outer, evalTypes, List.map_nil]
  constructor
  · rintro ⟨values, patternTyped, guardTyped, bodyTyped⟩
    exact .arm patternTyped guardTyped bodyTyped
  · intro typed
    cases typed with
    | arm patternTyped guardTyped bodyTyped =>
      obtain ⟨values, same⟩ := bindingValues_complete pattern.names _ patternTyped.binding_names.symm
      exact ⟨values, same.symm ▸ patternTyped, same.symm ▸ guardTyped, same.symm ▸ bodyTyped⟩

end Yulang.CommonArmEnvironmentGeneration
