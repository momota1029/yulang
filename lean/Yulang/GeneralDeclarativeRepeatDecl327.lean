import Yulang.GeneralDeclarativePairDecl326
import Yulang.GeneralDeclarativeCompoundDecl325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeRepeatDecl327
open GeneralDeclarations (Declaration Clause Registry Checked DeclarationChecked)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs ArgsWellScoped WellScoped
  checkSmaller_exact ConservativeSmaller counted encodeArgs substArgs)
open GeneralDeclarationExamples (roles constructors itemBinder itemEquation)
open GeneralDeclarativeExampleSource320 (leaf leaf_checked)
open GeneralDeclarativeDemand320 (Demand)
open GeneralNominalCenteredHeadMatExpressions (Expr translate translateMany)
open GeneralNominalInspection (Interpretation)
open GeneralDeclarativePairCenters326 (pair)
open GeneralDeclarativeWhere319 (Capture)

def interp : Interpretation :=
  ⟨fun n => if n = 5 then some .pair else none,fun n => n == 0,by
    intro n hnom
    have z : n = 0 := by simpa using hnom
    subst n
    rfl⟩

abbrev headPat : Pattern := .app 5 [.var 0,.var 0]
abbrev headCode := pair (.variable 0) (.variable 0)
abbrev compound : Pattern := .app 0 [.var 0]
abbrev compoundCode : Expr := .nominal 0 [.variable 0]
abbrev clause : Clause := ⟨20,2,[compound],[itemEquation]⟩
abbrev body : GeneralDeclarations.Equation := ⟨22,0,.var 1⟩
abbrev impl : Declaration := ⟨97,1,[headPat],[clause],[body],[itemBinder]⟩
abbrev reg : Registry := ⟨constructors,roles,[impl,leaf]⟩
abbrev arg : Capture := ⟨0,1,2⟩
abbrev root : Demand := ⟨1,[arg],[⟨0,6⟩]⟩

theorem normal_head : translate constructors interp (normalize headPat) = some headCode := rfl
theorem normal_child : translateMany constructors interp (clause.arguments.map normalize) = some [compoundCode] := rfl

theorem impl_checked : DeclarationChecked constructors roles impl := by
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro eq member
      cases List.mem_singleton.mp member
      exact ⟨none,rfl⟩
    · intro key rhs known
      change (if key = 0 then some none else none) = some rhs at known
      split at known
      · rename_i here
        exact .inl ⟨body,List.mem_cons_self,here.symm⟩
      · cases known
    · intro cl known
      cases List.mem_singleton.mp known
      exact ⟨rfl,fun eq present => by cases List.mem_singleton.mp present; exact ⟨none,rfl⟩⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames,Pattern.variables,variablesArgs]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro cl known
    cases List.mem_singleton.mp known
    exact ⟨rfl,rfl⟩
  · intro cl known
    cases List.mem_singleton.mp known
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro cl known
    cases List.mem_singleton.mp known
    unfold ConservativeSmaller
    decide +kernel
  · intro cl known cap
    cases List.mem_singleton.mp known
    constructor
    · simp [substArgs,Pattern.subst,normalize,normalizeArgs,counted,encodeArgs,Pattern.encode,
        Roles.argsSize,Roles.Term.size]
      exact Roles.Term.size_pos _
    · intro n
      simp [substArgs,Pattern.subst,normalize,normalizeArgs,counted,encodeArgs,Pattern.encode,
        Roles.argsOccurrences,Roles.Term.occurrences]

theorem checked : Checked reg := by
  constructor
  · decide +kernel
  · intro decl here
    rcases List.mem_cons.mp here with rfl|next
    · exact impl_checked
    · cases List.mem_singleton.mp next
      exact leaf_checked

end Yulang.GeneralDeclarativeRepeatDecl327
