import Yulang.GeneralDeclarativeAlternativeMixedReplay333
import Yulang.GeneralDeclarativeNestedFrame332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAlternativeMixedDecl333
open GeneralDeclarations (Declaration Clause Checked Registry DeclarationChecked)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs ArgsWellScoped WellScoped
  checkSmaller_exact ConservativeSmaller counted encodeArgs substArgs)
open GeneralDeclarationExamples (roles constructors binaryRole outputRole bareRole)
open GeneralDeclarativeExampleSource320 (leaf leaf_checked)
open GeneralDeclarativePairDecl326 (clause produced)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWhere319 (Capture)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeOutputSource323 (Declared)

abbrev first : Pattern := .record 7 (.var 0) (.var 1)
abbrev second : Pattern := .variant 4 (.app 5 [.var 3,.var 4])
abbrev firstCode : Expr := .record 7 (.variable 0) (.variable 1)
abbrev secondCode : Expr := .variant 4 (.primitive .pair [.variable 3,.variable 4])
abbrev decl : Declaration := ⟨97,4,[first,second],[clause],[],[produced]⟩
abbrev registry : Registry := ⟨constructors,roles,[decl,leaf]⟩
abbrev firstArg : Capture := ⟨2,0,9⟩
abbrev secondArg : Capture := ⟨6,8,10⟩
abbrev root : Demand := ⟨4,[firstArg,secondArg],[]⟩

theorem normal_first : translate constructors interpretation (normalize first) = some firstCode := rfl
theorem normal_second : translate constructors interpretation (normalize second) = some secondCode := rfl

theorem check_decl : DeclarationChecked constructors roles decl := by
  have earlier := GeneralDeclarativeNestedDecl332.checked_decl
  constructor
  · refine ⟨rfl,fun _ no => False.elim (List.not_mem_nil no),?_,earlier.signature.2.2.2⟩
    intro key rhs absent
    cases absent
  · simp [Declaration.Identified,Declaration.outputNames]
  · exact earlier.produced
  · simp [Declaration.OutputOnly,Declaration.outputNames,Pattern.variables,variablesArgs]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,
      Pattern.variables,variablesArgs,normalize,GeneralDeclarationPatterns.hide]
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
      omega

theorem checked : Checked registry := by
  constructor
  · decide +kernel
  · intro d appears
    rcases List.mem_cons.mp appears with rfl|tail
    · exact check_decl
    · cases List.mem_singleton.mp tail
      refine ⟨leaf_checked.signature,leaf_checked.identified,leaf_checked.produced,
        leaf_checked.outputOnly,leaf_checked.scope,?_,leaf_checked.countsCovered,leaf_checked.paterson,
        leaf_checked.conservative,leaf_checked.captureStable⟩
      simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped]

theorem covered : Coverage registry interpretation := by
  constructor
  · intro d visible
    rcases List.mem_cons.mp visible with rfl|last
    · refine ⟨?_,?_,fun _ absent => False.elim (List.not_mem_nil absent)⟩
      · exact (GeneralDeclarativeVisibleCode325.codes_were_covered (xs := [firstCode,secondCode])
          (show GeneralNominalCenteredHeadMatExpressions.translateMany constructors interpretation [first,second] = _ from rfl)).1
      · intro cl known
        cases List.mem_singleton.mp known
        refine ⟨⟨trivial,trivial⟩,?_⟩
        intro eq member
        cases List.mem_singleton.mp member
        trivial
    · cases List.mem_singleton.mp last
      exact ⟨⟨trivial,trivial⟩,fun _ absent => False.elim (List.not_mem_nil absent),
        fun eq found => by cases List.mem_singleton.mp found; trivial⟩
  · intro role name term h
    by_cases isP : role = 1
    · subst role
      by_cases eq : name = 0 <;> simp [roles,outputRole,eq] at h
    by_cases isC : role = 2
    · subst role
      by_cases eq : name = 1 <;> simp [roles,outputRole,eq] at h
    by_cases isB : role = 4 <;>
      simp [roles,bareRole,binaryRole,isP,isC,isB] at h

theorem declared : Declared registry root := by
  intro _ impossible
  cases impossible

end Yulang.GeneralDeclarativeAlternativeMixedDecl333
