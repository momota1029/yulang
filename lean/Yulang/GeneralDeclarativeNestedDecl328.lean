import Yulang.GeneralDeclarativeOpaqueNested328
import Yulang.GeneralDeclarativeRepeatDecl327
import Yulang.GeneralDeclarativeHiddenDecl324
import Yulang.GeneralDeclarativePairCut321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedDecl328
open GeneralDeclarations (Clause Declaration Registry Checked DeclarationChecked)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs ArgsWellScoped WellScoped
  checkSmaller_exact ConservativeSmaller counted encodeArgs substArgs)
open GeneralDeclarationExamples (roles constructors containerChild itemBinder)
open GeneralDeclarativeExampleSource320 (leaf leaf_checked)
open GeneralDeclarativeHiddenDecl324 (out)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativeWhere319 (Capture)

abbrev interpret : Interpretation := GeneralDeclarativeRepeatDecl327.interp
abbrev raw : Pattern := .app 5 [.variant 4 (.var 0),.app 0 [.var 1]]
abbrev normalCode : Expr := pair (.variant 4 (.variable 0)) (.nominal 0 [.variable 1])
/-- Input-name 1 is a real head binder, so the output-only binder uses
2, not the original fixture's 1. -/
abbrev produced : GeneralDeclarations.OutputBinder := ⟨2,containerChild.id,21⟩
abbrev eqOut : GeneralDeclarations.Equation := ⟨21,1,.var 2⟩
abbrev clause : Clause := ⟨containerChild.id,2,[.var 0],[eqOut]⟩
abbrev body : GeneralDeclarations.Equation := ⟨out.id,0,.var 2⟩
abbrev impl : Declaration := ⟨97,1,[raw],[clause],[body],[produced]⟩
abbrev reg : Registry := ⟨constructors,roles,[impl,leaf]⟩
abbrev rootArg : Capture := ⟨0,1,2⟩
abbrev root : Demand := ⟨1,[rootArg],[⟨0,6⟩]⟩
theorem normalized : translate constructors interpret (normalize raw) = some normalCode := rfl

theorem impl_checked : DeclarationChecked constructors roles impl := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro equation belongs
      cases List.mem_singleton.mp belongs
      exact ⟨none,rfl⟩
    · intro key rhs want
      change (if key = 0 then some none else none) = some rhs at want
      split at want
      · rename_i h
        exact .inl ⟨body,List.mem_cons_self,h.symm⟩
      · cases want
    · intro req h
      cases List.mem_singleton.mp h
      refine ⟨rfl,?_⟩
      intro eq whereEq
      cases List.mem_singleton.mp whereEq
      exact ⟨none,rfl⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames,Pattern.variables,variablesArgs]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,
      Pattern.variables,variablesArgs,normalize]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro req h
    cases List.mem_singleton.mp h
    exact ⟨rfl,rfl⟩
  · intro req h
    cases List.mem_singleton.mp h
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro req h
    cases List.mem_singleton.mp h
    unfold ConservativeSmaller
    decide +kernel
  · intro req h cap
    cases List.mem_singleton.mp h
    constructor
    · simp [substArgs,Pattern.subst,normalize,normalizeArgs,counted,encodeArgs,Pattern.encode,
        Roles.argsSize,Roles.Term.size]
      omega
    · intro n
      simp [substArgs,Pattern.subst,normalize,normalizeArgs,counted,encodeArgs,Pattern.encode,
        Roles.argsOccurrences,Roles.Term.occurrences]

theorem checked : Checked reg := by
  constructor
  · decide +kernel
  · intro impl x
    rcases List.mem_cons.mp x with rfl|tail
    · exact impl_checked
    · cases List.mem_singleton.mp tail
      exact leaf_checked

end Yulang.GeneralDeclarativeNestedDecl328
