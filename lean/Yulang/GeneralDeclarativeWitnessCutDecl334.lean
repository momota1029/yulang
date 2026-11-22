import Yulang.GeneralDeclarativeWitnessCorrespond334
import Yulang.GeneralDeclarativeNestedFrame332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCutDecl334
open GeneralDeclarations (Declaration Checked Registry DeclarationChecked)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs ArgsWellScoped WellScoped)
open GeneralDeclarationExamples (roles constructors)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)

abbrev pat : Pattern := .record 7 (.var 0) (.var 1)
abbrev wanted : Expr := .record 7 (.variable 0) (.variable 1)
abbrev body : GeneralDeclarations.Equation := ⟨91,0,.var 0⟩
abbrev impl : Declaration := ⟨92,1,[pat],[],[body],[]⟩
abbrev registry : Registry := ⟨constructors,roles,[impl]⟩
abbrev arg : Capture := ⟨0,1,2⟩
abbrev root : Demand := ⟨1,[arg],[⟨0,5⟩]⟩

theorem normal : translate constructors interpretation (normalize pat) = some wanted := rfl

theorem check_decl : DeclarationChecked constructors roles impl := by
  constructor
  · refine ⟨rfl,?_,?_,fun _ impossible => False.elim (List.not_mem_nil impossible)⟩
    · intro eq present
      cases List.mem_singleton.mp present
      exact ⟨none,rfl⟩
    · intro k rhs atRole
      change (if k = 0 then some none else none) = some rhs at atRole
      split at atRole
      · rename_i equal
        exact .inl ⟨body,List.mem_cons_self,equal.symm⟩
      · cases atRole
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,
    Pattern.variables,variablesArgs,normalize]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]
  · intro _ impossible
    cases impossible
  · intro _ impossible
    cases impossible
  · intro _ impossible
    cases impossible
  · intro _ impossible
    cases impossible

theorem checked : Checked registry := by
  constructor
  · decide +kernel
  · intro decl member
    cases List.mem_singleton.mp member
    exact check_decl

theorem covered : Coverage registry interpretation := by
  constructor
  · intro d visible
    cases List.mem_singleton.mp visible
    exact ⟨⟨⟨trivial,trivial⟩,trivial⟩,fun _ h => False.elim (List.not_mem_nil h),
      fun _ member => by cases List.mem_singleton.mp member; trivial⟩
  · exact (GeneralDeclarativeNestedFrame332.covered).2

theorem declared : Declared registry root := by
  intro requested member
  cases List.mem_singleton.mp member
  exact ⟨none,rfl⟩

end Yulang.GeneralDeclarativeWitnessCutDecl334
