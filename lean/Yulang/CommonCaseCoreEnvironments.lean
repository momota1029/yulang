import Yulang.CommonPatternCoreDefaults
import Yulang.CommonPatternSourceArmSolved

/-! Independent Core subject/guard/body environment factors. Core arm terms
are already resolved at their final pure monomorphic pattern prefix. Ordered
runtime observations, coverage and aggregate default/failure rows are separate
from these static premises. -/

namespace Yulang.CommonCaseCoreEnvironments

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternAllocation (Slots ambient assignment assignment_ambient bindingSlots bindingSlots_eval
  bindingValues bindingValues_complete)
open CommonPatternSourceScope (corePrefix core_prefix_related)
open CommonPatternCoreDefaults (DefaultTyped lower covered names_lower)
open CasePatterns (Pattern)

def generateTerm (environment : SchemeEnv α) (code : Required.Term) (result : CompTerm α) : Formula α :=
  if CommonSyntax.covered code then generate environment (CommonSyntax.lower code) result else .bot

theorem generateTerm_exact (code : Required.Term) (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic) (result : CompTerm α) :
    (generateTerm symbolic code result).Holds Common.model ρ ↔
      CommonSyntax.Typing Common.model environment code (result.eval Common.model ρ) := by
  cases within : CommonSyntax.covered code with
  | false =>
      simp only [generateTerm, within, Bool.false_eq_true, ↓reduceIte, Formula.Holds]
      exact ⟨False.elim, fun typed => by simpa [within] using CommonSyntax.typing_covered typed⟩
  | true =>
      simp only [generateTerm, within, ↓reduceIte]
      exact (generate_models_iff_typing Common.model _ _ _ ρ result symbolicRelated).trans
        (CommonSyntax.lowering_exact code within coreRelated _).symm

def GuardTyping (environment : List (CommonSyntax.Binding Common.model))
    (guard : Option Required.Term) (row : Common.Row) : Prop :=
  match guard with
  | none => Common.rowLe Common.rowEmpty row
  | some code => CommonSyntax.Typing Common.model environment code (.base .bool, row)

def generateGuard (environment : SchemeEnv α) (guard : Option Required.Term) (row : RowTerm α) : Formula α :=
  match guard with
  | none => .rowLe .empty row
  | some code => generateTerm environment code ⟨.base .bool, row⟩

theorem generateGuard_exact (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (guard : Option Required.Term) (row : RowTerm α) :
    (generateGuard symbolic guard row).Holds Common.model ρ ↔ GuardTyping environment guard (row.eval Common.model ρ) := by
  cases guard with
  | none => rfl
  | some code => exact generateTerm_exact code ρ symbolic environment semantic coreRelated symbolicRelated _

def consumer (pattern : Pattern Empty Inference.Expr) (environment : SchemeEnv α)
    (guard : Option Required.Term) (body : Required.Term) (guardRow : RowTerm α)
    (result : CompTerm α) : Formula (Slots α pattern.names.length) :=
  let inner := symbolicPrefix (bindingSlots pattern.names) ++ environment.rename (ambient pattern.names.length)
  .and (generateGuard inner guard (guardRow.rename (ambient pattern.names.length)))
    (generateTerm inner body (result.rename (ambient pattern.names.length)))

theorem consumer_exact (pattern : Pattern Empty Inference.Expr)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (guard : Option Required.Term) (body : Required.Term) (guardRow : RowTerm α) (result : CompTerm α)
    (values : Fin pattern.names.length → Comp Common.model) :
    (consumer pattern symbolic guard body guardRow result).Holds Common.model (assignment ρ values) ↔
      GuardTyping (corePrefix (bindingValues pattern.names values) ++ environment) guard (guardRow.eval Common.model ρ) ∧
      CommonSyntax.Typing Common.model (corePrefix (bindingValues pattern.names values) ++ environment)
        body (result.eval Common.model ρ) := by
  have related := monomorphic_prefix_environment_exact (assignment ρ values) (bindingSlots pattern.names)
    (symbolic.rename (ambient pattern.names.length)) semantic
    (symbolicRelated.rename _ _ (assignment_ambient ρ values))
  rw [bindingSlots_eval] at related
  have guardExact := generateGuard_exact (assignment ρ values) _ _ _
    (core_prefix_related (bindingValues pattern.names values) coreRelated) related
    guard (guardRow.rename (ambient pattern.names.length))
  have bodyExact := generateTerm_exact body (assignment ρ values) _ _ _
    (core_prefix_related (bindingValues pattern.names values) coreRelated) related
    (result.rename (ambient pattern.names.length))
  simp only [consumer, Formula.Holds, guardExact, bodyExact, RowTerm.eval_rename, CompTerm.eval_rename, assignment_ambient]

inductive EnvironmentTyping (environment : List (CommonSyntax.Binding Common.model))
    (pattern : Pattern Empty Required.Term) (guard : Option Required.Term) (body : Required.Term)
    (input : Common.Ty) (guardRow : Common.Row) (result : Comp Common.model) : Prop where
  | arm {bindings : NamedTypes} :
      CommonAlignedPatternTyping.Typing (DefaultTyped environment) [] pattern input bindings →
      GuardTyping (corePrefix bindings ++ environment) guard guardRow →
      CommonSyntax.Typing Common.model (corePrefix bindings ++ environment) body result →
      EnvironmentTyping environment pattern guard body input guardRow result

def generateEnvironments (environment : SchemeEnv α) (pattern : Pattern Empty Required.Term)
    (guard : Option Required.Term) (body : Required.Term) (input : TyTerm α)
    (guardRow : RowTerm α) (result : CompTerm α) : Formula α :=
  if PatternBindingChecks.check pattern && covered pattern then
    let lowered := lower pattern
    CommonAlignedPatternAllocation.withPattern lowered environment [] input
      (consumer lowered environment guard body guardRow result)
  else .bot

theorem generateEnvironments_exact (pattern : Pattern Empty Required.Term)
    (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (guard : Option Required.Term) (body : Required.Term)
    (input : TyTerm α) (guardRow : RowTerm α) (result : CompTerm α) :
    (generateEnvironments symbolic pattern guard body input guardRow result).Holds Common.model ρ ↔
      EnvironmentTyping environment pattern guard body (input.eval Common.model ρ)
        (guardRow.eval Common.model ρ) (result.eval Common.model ρ) := by
  have patternExact := CommonPatternCoreDefaults.raw_typing_exact coreRelated pattern [] (input.eval Common.model ρ)
  cases checked : PatternBindingChecks.check pattern && covered pattern with
  | false =>
      simp only [generateEnvironments, checked, Bool.false_eq_true, ↓reduceIte, Formula.Holds]
      constructor
      · exact False.elim
      · intro typed
        cases typed with
        | arm patternTyped guardTyped bodyTyped =>
            have valid := (PatternBindingChecks.check_exact pattern).mpr patternTyped.1
            have within := (patternExact _).mp patternTyped.2
            simp [valid, within.1] at checked
  | true =>
      have gate := Bool.and_eq_true_iff.mp checked
      have valid := (PatternBindingChecks.check_exact pattern).mp gate.1
      simp only [generateEnvironments, checked, ↓reduceIte,
        CommonAlignedPatternAllocation.withPattern_exact _ ρ symbolic semantic symbolicRelated,
        consumer_exact _ ρ symbolic environment semantic coreRelated symbolicRelated, evalTypes, List.map_nil]
      constructor
      · rintro ⟨values, patternTyped, guardTyped, bodyTyped⟩
        exact .arm ⟨valid, (patternExact _).mpr ⟨gate.2, patternTyped⟩⟩ guardTyped bodyTyped
      · intro typed
        cases typed with
        | arm patternTyped guardTyped bodyTyped =>
            have raw := ((patternExact _).mp patternTyped.2).2
            obtain ⟨values, same⟩ := bindingValues_complete (lower pattern).names _
              (by simpa only [names_lower] using patternTyped.2.binding_names.symm)
            exact ⟨values, same.symm ▸ raw, same.symm ▸ guardTyped, same.symm ▸ bodyTyped⟩

end Yulang.CommonCaseCoreEnvironments
