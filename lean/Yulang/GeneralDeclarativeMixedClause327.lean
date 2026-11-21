import Yulang.GeneralDeclarativeAppliedClause327
import Yulang.GeneralDeclarativeRepeatModels327

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15000
set_option maxHeartbeats 7600000
namespace Yulang.GeneralDeclarativeMixedClause327
open GeneralDeclarativeRepeatDecl327 (headPat interp body clause compoundCode)
open GeneralDeclarativeRepeatState327 (mergedState base)
open GeneralDeclarations (Declaration Clause Registry DeclarationChecked Checked)
open GeneralDeclarationExamples (constructors roles itemBinder)
open GeneralDeclarativeExampleSource320 (leaf leaf_checked)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeClauseBatch327 (Port prepare Input)
open GeneralDeclarativeClausePlacement327 (placement portAt)
open GeneralDeclarativeAppliedClause327 (targetsOnly)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeWhereOutputBatch327 (whole)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarationPatterns (Pattern normalize normalizeArgs variablesArgs ArgsWellScoped WellScoped
  checkSmaller_exact ConservativeSmaller counted encodeArgs substArgs)

abbrev payload : Pattern := .variant 4 (.var 0)
abbrev quoted : GeneralDeclarations.Equation := ⟨41,1,payload⟩
abbrev secondClause : Clause := ⟨40,2,[payload],[quoted]⟩
abbrev impl : Declaration := ⟨97,1,[headPat],[clause,secondClause],[body],[itemBinder]⟩
abbrev reg : Registry := ⟨constructors,roles,[impl,leaf]⟩

theorem checked_impl : DeclarationChecked constructors roles impl := by
  have prior := GeneralDeclarativeRepeatDecl327.impl_checked
  constructor
  · refine ⟨rfl,prior.signature.2.1,prior.signature.2.2.1,?_⟩
    intro cl found
    rcases List.mem_cons.mp found with rfl|later
    · exact prior.signature.2.2.2 clause List.mem_cons_self
    cases List.mem_singleton.mp later
    exact ⟨rfl,fun eq member => by cases List.mem_singleton.mp member; exact ⟨none,rfl⟩⟩
  · simp [Declaration.Identified,Declaration.outputNames]
  · simp [Declaration.Produced]
  · simp [Declaration.OutputOnly,Declaration.outputNames,Pattern.variables,variablesArgs]
  · simp [Declaration.Scoped,Declaration.inputNames,Declaration.outputNames,normalizeArgs,normalize,
      variablesArgs,Pattern.variables]
  · simp [Declaration.ConstructorScoped,ArgsWellScoped,WellScoped,constructors]
  · intro cl found
    rcases List.mem_cons.mp found with rfl|later
    · exact prior.countsCovered clause List.mem_cons_self
    cases List.mem_singleton.mp later
    exact ⟨rfl,rfl⟩
  · intro cl found
    rcases List.mem_cons.mp found with rfl|later
    · exact prior.paterson clause List.mem_cons_self
    cases List.mem_singleton.mp later
    exact (checkSmaller_exact _ _).mp (by decide +kernel)
  · intro cl found
    rcases List.mem_cons.mp found with rfl|later
    · exact prior.conservative clause List.mem_cons_self
    cases List.mem_singleton.mp later
    unfold ConservativeSmaller
    decide +kernel
  · intro cl found cap
    rcases List.mem_cons.mp found with rfl|later
    · exact prior.captureStable clause List.mem_cons_self cap
    cases List.mem_singleton.mp later
    constructor
    · simp [substArgs,Pattern.subst,normalize,normalizeArgs,counted,encodeArgs,Pattern.encode,
        Roles.argsSize,Roles.Term.size]
      exact Roles.Term.size_pos _
    · intro n
      simp [substArgs,Pattern.subst,normalize,normalizeArgs,counted,encodeArgs,Pattern.encode,
        Roles.argsOccurrences,Roles.Term.occurrences]

theorem checked : Checked reg := by
  refine ⟨by decide +kernel,?_⟩
  intro d known
  rcases List.mem_cons.mp known with rfl|rest
  · exact checked_impl
  · cases List.mem_singleton.mp rest
    exact leaf_checked

abbrev targets (c : Clause) (_ : Nat) : Nat := if c.id = 20 then 5 else 8
abbrev names := sourceNames impl (targetsOnly targets) base
abbrev keep := stateNames mergedState ++ [5,6,8]
abbrev plan := prepare constructors interp keep names.input mergedState impl.requirements
abbrev sample := plan.getD (mergedState,[])
abbrev preparedSample := sample.1
abbrev ports := sample.2
abbrev placed := placement impl.requirements ports targets

theorem successful : plan = some (preparedSample,ports) := rfl
theorem ordered_child_names :
    children impl (sourceNames impl placed base) placed =
      [(⟨2,[⟨20,21,22⟩],[⟨1,5⟩]⟩ : Demand),⟨2,[⟨23,24,25⟩],[⟨1,8⟩]⟩] := rfl
theorem fixed_selected_where :
    whole reg interp impl (sourceNames impl placed base) targets =
      some [⟨8,.variant 4 (.variable 13)⟩] := rfl
theorem fixed_parent :
    collect (one reg interp impl GeneralDeclarativeRepeatDecl327.root
      (sourceNames impl placed base).input) GeneralDeclarativeRepeatDecl327.root.outputs =
      some [⟨6,.variable 5⟩] := rfl

end Yulang.GeneralDeclarativeMixedClause327
