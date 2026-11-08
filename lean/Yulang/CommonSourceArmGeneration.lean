import Yulang.CommonSourcePatternElaboration
import Yulang.CommonPatternSourceArmGeneration
import Yulang.CommonArmEnvironmentGeneration

/-! Source guard/body generation shares the actual source pattern slots.
These are the environment premises of a case arm. Aggregate match/default
effects, failure rows and ordered coverage are not defined by these premises. -/

namespace Yulang.CommonSourceArmGeneration

set_option backward.isDefEq.respectTransparency false

open Core
open PresenceGeneration
open CommonPatternEnvironment
open CommonPatternAllocation (Slots ambient assignment assignment_ambient bindingSlots bindingSlots_eval
  bindingValues bindingValues_names bindingValues_complete)
open CommonPatternSourceElaboration (DefaultTyped elaborate covered names_elaborate)
open CommonPatternSourceScope (corePrefix core_prefix_related generateData generateData_exact)
open CasePatterns (Pattern)

open CommonPatternSourceArmGeneration (GuardTyping generateGuard generateGuard_exact consumer consumer_exact)

inductive EnvironmentTyping (outerNames : List Nat) (environment : List (CommonSyntax.Binding Common.model))
    (pattern : Pattern Empty (CaseDataTerms.Expr Empty)) (guard : Option (CaseDataTerms.Expr Empty))
    (body : CaseDataTerms.Expr Empty) (input : Common.Ty) (guardRow : Common.Row)
    (result : Comp Common.model) : Prop where
  | arm {bindings : NamedTypes} :
      CommonSourcePatternTyping.Typing (DefaultTyped outerNames environment) [] pattern input bindings →
      GuardTyping (corePrefix bindings ++ environment) (bindings.map Prod.fst ++ outerNames) guard guardRow →
      CommonSyntax.Typing Common.model (corePrefix bindings ++ environment)
        (Data.embed (bindings.map Prod.fst ++ outerNames) body) result →
      EnvironmentTyping outerNames environment pattern guard body input guardRow result

def generateEnvironments (outerNames : List Nat) (environment : SchemeEnv α)
    (pattern : Pattern Empty (CaseDataTerms.Expr Empty)) (guard : Option (CaseDataTerms.Expr Empty))
    (body : CaseDataTerms.Expr Empty) (input : TyTerm α) (guardRow : RowTerm α) (result : CompTerm α) : Formula α :=
  if PatternBindingChecks.check pattern && covered outerNames pattern then
    let lowered := elaborate outerNames pattern
    CommonSourcePatternAllocation.withPattern lowered environment [] input
      (consumer lowered environment outerNames guard body guardRow result)
  else .bot

/-- Source default/guard/body expressions are elaborated at their actual Q4
scopes; one finite allocator supplies the same pure mono bindings to all.
Arbitrary symbolic environments, captured polymorphic environments, Common
inputs, guard rows and result computations are retained. -/
theorem generateEnvironments_exact (pattern : Pattern Empty (CaseDataTerms.Expr Empty))
    (outerNames : List Nat) (ρ : α → Comp Common.model) (symbolic : SchemeEnv α)
    (environment : List (CommonSyntax.Binding Common.model)) (semantic : List (Binding Common.model))
    (coreRelated : CommonSyntax.EnvRel Common.model environment semantic)
    (symbolicRelated : EnvRel Common.model ρ symbolic semantic)
    (guard : Option (CaseDataTerms.Expr Empty)) (body : CaseDataTerms.Expr Empty)
    (input : TyTerm α) (guardRow : RowTerm α) (result : CompTerm α) :
    (generateEnvironments outerNames symbolic pattern guard body input guardRow result).Holds Common.model ρ ↔
      EnvironmentTyping outerNames environment pattern guard body (input.eval Common.model ρ)
        (guardRow.eval Common.model ρ) (result.eval Common.model ρ) := by
  have patternExact := CommonSourcePatternElaboration.raw_typing_exact (outerNames := outerNames)
    coreRelated pattern [] (input.eval Common.model ρ)
  simp only [List.map_nil, List.nil_append] at patternExact
  cases checked : PatternBindingChecks.check pattern && covered outerNames pattern with
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
        CommonSourcePatternAllocation.withPattern_exact _ ρ symbolic semantic symbolicRelated,
        consumer_exact _ ρ symbolic environment semantic coreRelated symbolicRelated, evalTypes, List.map_nil]
      constructor
      · rintro ⟨values, patternTyped, guardTyped, bodyTyped⟩
        exact .arm ⟨valid, (patternExact _).mpr ⟨gate.2, patternTyped⟩⟩ guardTyped bodyTyped
      · intro typed
        cases typed with
        | arm patternTyped guardTyped bodyTyped =>
          have raw := ((patternExact _).mp patternTyped.2).2
          obtain ⟨values, same⟩ := bindingValues_complete (elaborate outerNames pattern).names _
            (by simpa only [names_elaborate] using patternTyped.2.binding_names.symm)
          exact ⟨values, same.symm ▸ raw, same.symm ▸ guardTyped, same.symm ▸ bodyTyped⟩

end Yulang.CommonSourceArmGeneration
