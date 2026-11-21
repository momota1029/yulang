import Yulang.GeneralDeclarativeNFComplete324
import Yulang.GeneralDeclarativeHiddenDecl324
import Yulang.GeneralDeclarativeHiddenProbe324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeHiddenWhere324
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation raw normal normCode empty normal_compiles)
open GeneralDeclarativeHiddenState324 (direct)
open GeneralDeclarativeHiddenProbe324 (root_bounds)
open GeneralDeclarationExamples (roles constructors containerChild)
open GeneralDeclarativeExampleSource320 (point int)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs ArgsWellScoped WellScoped)
open GeneralDeclarations (Declaration Clause Registry DeclarationChecked Checked)
open GeneralDeclarativeSourceEmission322 (Names demand)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeEntailment320 (literal)
open GeneralDeclarativeNFWhere324 (namedFact clauseFacts)
open GeneralDeclarativeNFEmit324 (Read ordinary_clause)
open GeneralDeclarativeNFComplete324 (ReadBack facts produces local_sound)
open GeneralDeclarativeNFHead324 (Scan)
open GeneralDeclarativeNFNode324 (BodyCoverage)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeAssocRule323 (SourceEquation)
open GeneralDeclarativeModelStable324 (StableUnder stable_exact)
open GeneralDeclarativeNormalizeAssoc324 (one row_iff)
open GeneralDeclarativeAssembly320 (Meaning)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (record emptyRecord)
open CommonRoleOutermostResolver (All₂ Dictionary)

abbrev rhs : Pattern := .record 7 (.var 0) (.record 7 (.app 9 [.var 0]) (.app 4 []))
abbrev named : GeneralDeclarations.Equation := ⟨100,1,rhs⟩
abbrev clause : Clause := ⟨101,2,[.var 0],[named]⟩
abbrev returned : GeneralDeclarations.Equation := ⟨102,0,.var 0⟩
abbrev childReturn : GeneralDeclarations.Equation := ⟨103,1,normal⟩
abbrev parent : Declaration := ⟨104,1,[raw],[clause],[returned],[]⟩
abbrev implementation : Declaration := ⟨105,2,[.var 0],[],[childReturn],[]⟩
abbrev registry : Registry := ⟨catalogue,roles,[parent,implementation]⟩
abbrev root : Demand := ⟨1,[point 0],[⟨0,6⟩]⟩
abbrev child : Demand := ⟨2,[point 3],[⟨1,55⟩]⟩
abbrev capture : Names := ⟨fun _ => point 3,fun _ => 399⟩
abbrev place : Placement := ⟨fun _ _ => point 400,fun _ _ => 55⟩

theorem root_check : DeclarationChecked catalogue roles parent := by
  have old := GeneralDeclarativeHiddenDecl324.declaration_checked
  constructor
  · refine ⟨rfl,?_,?_,?_⟩
    · intro eq h
      cases List.mem_singleton.mp h
      exact ⟨none,rfl⟩
    · intro name body wanted
      change (if name = 0 then some none else none) = some body at wanted
      split at wanted
      · rename_i same
        exact .inl ⟨returned,List.mem_cons_self,same.symm⟩
      · cases wanted
    · intro row there
      cases List.mem_singleton.mp there
      refine ⟨rfl,?_⟩
      intro eq member
      cases List.mem_singleton.mp member
      exact ⟨none,rfl⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,
      normalizeArgs,normalize,GeneralDeclarationPatterns.hide,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,catalogue,constructors]
  · intro c found
    cases List.mem_singleton.mp found
    exact old.countsCovered containerChild List.mem_cons_self
  · intro c found
    cases List.mem_singleton.mp found
    exact old.paterson containerChild List.mem_cons_self
  · intro c found
    cases List.mem_singleton.mp found
    exact old.conservative containerChild List.mem_cons_self
  · intro c found
    cases List.mem_singleton.mp found
    exact old.captureStable containerChild List.mem_cons_self

theorem child_check : DeclarationChecked catalogue roles implementation := by
  constructor
  · refine ⟨rfl,?_,?_,by simp⟩
    · intro eq h
      cases List.mem_singleton.mp h
      exact ⟨none,rfl⟩
    · intro name body wanted
      change (if name = 1 then some none else none) = some body at wanted
      split at wanted
      · rename_i same
        exact .inl ⟨childReturn,List.mem_cons_self,same.symm⟩
      · cases wanted
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,
      normalizeArgs,normalize,GeneralDeclarationPatterns.hide,variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,catalogue,constructors]
  all_goals intro c found; cases found

theorem checked : Checked registry := by
  refine ⟨by decide +kernel,?_⟩
  intro decl found
  rcases List.mem_cons.mp found with rfl|later
  · exact root_check
  · cases List.mem_singleton.mp later
    exact child_check

theorem ordinary_named_erasure : translate catalogue interpretation rhs = none ∧
    translate catalogue interpretation (normalize rhs) = some normCode := ⟨rfl,rfl⟩

theorem exact_emission : children parent capture place = [child] := rfl

abbrev row : Equation := ⟨55,direct⟩
abbrev state : State := ⟨⟨[],[]⟩,[⟨0,direct⟩,⟨3,.primitive (.scalar .int) []⟩,⟨6,.variable 3⟩,row]⟩

theorem where_read : Read state registry interpretation parent clause capture (place.compound clause) (place.targets clause) := by
  constructor
  · refine ⟨[.variable 0],.cons rfl .nil,?_⟩
    intro i p code found printed compound
    cases List.mem_singleton.mp (List.mem_of_getElem? found)
    exact False.elim (compound 0 rfl)
  · intro equation found
    cases List.mem_singleton.mp found
    exact ⟨normCode,rfl,fun _ => .row (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

theorem exact_normal_row :
    namedFact catalogue interpretation capture.input named ⟨1,55⟩ = some [row] := rfl

theorem old_named_unavailable :
    GeneralDeclarativeOutputFacts320.childFact catalogue interpretation capture.input named ⟨1,55⟩ = none := rfl

theorem where_produced : Result state (clauseFacts registry interpretation capture.input clause child) :=
  ordinary_clause (fun _ bad => False.elim (List.not_mem_nil bad)) where_read

end Yulang.GeneralDeclarativeHiddenWhere324
