import Yulang.GeneralDeclarativePairDecl326
import Yulang.GeneralDeclarativeFreshTail326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeInlineDecl331
open GeneralDeclarations (Declaration Clause Checked Registry DeclarationChecked NormalizationDeferred)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs ArgsWellScoped WellScoped
  checkSmaller_exact ConservativeSmaller counted encodeArgs substArgs)
open GeneralDeclarationExamples (roles constructors)
open GeneralDeclarativeExampleSource320 (point leaf leaf_checked)
open GeneralDeclarativePairDecl326 (clause produced eqOut)
open GeneralDeclarativeHiddenDecl324 (interpretation catalogue)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeDemand320 (Demand)

abbrev pat : Pattern := .record 7 (.var 0) (.record 8 (.var 3) (.var 1))
abbrev normalizedExpr : Expr := .record 7 (.variable 0) (.record 8 (.variable 3) (.variable 1))
abbrev body : GeneralDeclarations.Equation := ⟨96,0,.var 1⟩
abbrev decl : Declaration := ⟨97,1,[pat],[clause],[body],[produced]⟩
abbrev registry : Registry := ⟨catalogue,roles,[decl,leaf]⟩
abbrev root : Demand := ⟨1,[point 0],[⟨0,6⟩]⟩
abbrev child : Demand := ⟨2,[point 3],[⟨1,5⟩]⟩
theorem normal : translate catalogue interpretation (normalize pat) = some normalizedExpr := rfl

theorem checked_decl : DeclarationChecked catalogue roles decl := by
  have previous := GeneralDeclarativePairDecl326.impl_checked
  constructor
  · refine ⟨rfl,?_,?_,previous.signature.2.2.2⟩
    · intro req present
      cases List.mem_singleton.mp present
      exact ⟨none,rfl⟩
    · intro key rhs known
      change (if key = 0 then some none else none) = some rhs at known
      split at known
      · rename_i same
        exact .inl ⟨body,List.mem_cons_self,same.symm⟩
      · cases known
  · exact previous.identified
  · exact previous.produced
  · simp [Declaration.OutputOnly,Declaration.outputNames,Pattern.variables,variablesArgs]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,
      Pattern.variables,variablesArgs,normalize,GeneralDeclarationPatterns.hide]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]
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

theorem checked : Checked registry := by
  constructor
  · decide +kernel
  · intro d appears
    rcases List.mem_cons.mp appears with rfl|tail
    · exact checked_decl
    · cases List.mem_singleton.mp tail
      refine ⟨leaf_checked.signature,leaf_checked.identified,leaf_checked.produced,
        leaf_checked.outputOnly,leaf_checked.scope,?_,leaf_checked.countsCovered,leaf_checked.paterson,
        leaf_checked.conservative,leaf_checked.captureStable⟩
      simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]

end Yulang.GeneralDeclarativeInlineDecl331
