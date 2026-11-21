import Yulang.GeneralDeclarativeMixedClause327
import Yulang.GeneralDeclarativeInPlace327

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 15000
set_option maxHeartbeats 7800000
namespace Yulang.GeneralDeclarativeMixedReplay327
open GeneralDeclarativeMixedClause327
open GeneralDeclarativeRepeatDecl327 (headPat headCode root interp clause compoundCode body)
open GeneralDeclarativeRepeatState327 (mergedState base aggregate)
open GeneralDeclarativeAppliedClause327 (compiler_projection)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralDeclarativeHead320 (Models)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalCenteredHeadMatExpressions (translate translateMany Expr)
open GeneralDeclarativeVisibleCode325 (code_was_covered codes_were_covered)
open GeneralDeclarativeExampleSource320 (leaf association)
open GeneralDeclarationExamples (constructors roles bareRole binaryRole outputRole itemEquation)

theorem covered : Coverage reg interp := by
  constructor
  · intro d visible
    rcases List.mem_cons.mp visible with rfl|rest
    · refine ⟨(codes_were_covered (xs := [headCode])
        (show translateMany constructors interp [headPat] = _ from rfl)).1,?_,?_⟩
      · intro cl needed
        rcases List.mem_cons.mp needed with rfl|second
        · refine ⟨(codes_were_covered (xs := [compoundCode])
            (show translateMany constructors interp clause.arguments = _ from rfl)).1,?_⟩
          intro eq requested
          cases List.mem_singleton.mp requested
          exact (code_was_covered (exp := .variable 1)
            (show translate constructors interp itemEquation.rhs = _ from rfl))
        · cases List.mem_singleton.mp second
          refine ⟨(codes_were_covered (xs := [.variant 4 (.variable 0)])
            (show translateMany constructors interp secondClause.arguments = _ from rfl)).1,?_⟩
          intro eq used
          cases List.mem_singleton.mp used
          exact (code_was_covered (exp := .variant 4 (.variable 0))
            (show translate constructors interp quoted.rhs = _ from rfl))
      · intro eq present
        cases List.mem_singleton.mp present
        trivial
    · cases List.mem_singleton.mp rest
      exact ⟨⟨trivial,trivial⟩,fun _ absent => False.elim (List.not_mem_nil absent),
        fun eq found => by cases List.mem_singleton.mp found; trivial⟩
  · intro role name term declared
    by_cases isP : role = 1
    · subst role
      by_cases eq : name = 0 <;> simp [roles,outputRole,eq] at declared
    by_cases isC : role = 2
    · subst role
      by_cases eq : name = 1 <;> simp [roles,outputRole,eq] at declared
    by_cases isB : role = 4 <;> simp [roles,bareRole,binaryRole,isP,isC,isB] at declared

theorem retains_actual_names (m) :
    Models mergedState m ↔ ∃ next, Models preparedSample next ∧ ∀ n ∈ keep, next n = m n :=
  compiler_projection checked List.mem_cons_self targets base [5,6,8]
    (fun _ _ => aggregate.1) successful m

open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeRepeatState327 (initial protect leftView rightView root_bounds lower shared_root upper exactly_views)
open GeneralDeclarativeRepeatedHead327 (compiled_head original_grows)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeGrowth327 (Extends trans restrict facts fits)
open GeneralDeclarativeClauseBatch327 (read_order)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeNFHead324 (fact)
open GeneralDeclarativeDemand320 (Bounds)
open CommonRoleOutermostResolver (All₂)
open GeneralDeclarativeAssembly320 (Meaning)

abbrev whereRow : Equation := ⟨8,.variant 4 (.variable 13)⟩
abbrev returnRow : Equation := ⟨6,.variable 5⟩
abbrev beforeReturn := appendFacts preparedSample [whereRow]
abbrev current := appendFacts beforeReturn [returnRow]
abbrev actualNames := sourceNames impl placed base

theorem extensions : Extends mergedState current :=
  trans (read_order successful).1 (trans (facts preparedSample [whereRow]) (facts beforeReturn [returnRow]))

theorem actual_head :
    All₂ (fun a p => Bounds current a ∧ Result current (fact reg.constructors interp actualNames.input a p))
      root.arguments impl.head := by
  have bounds := fits (trans (original_grows initial protect leftView rightView) extensions) root_bounds
  have written := compiled_head root_bounds lower shared_root upper exactly_views protect
    (cap := actualNames.input) (binder := 0) GeneralDeclarativeRepeatDecl327.normal_head rfl
  obtain ⟨rows,tag,sound⟩ := written
  exact .cons ⟨bounds,rows,tag,fun row included m valid => sound row included m (restrict extensions m valid)⟩ .nil

theorem assembled :
    Result current (GeneralDeclarativeNFComplete324.facts reg interp actualNames.input impl root
      (children impl actualNames placed)) ∧
    ∀ m, Models current m → Meaning reg interp m root impl actualNames.input (children impl actualNames placed) :=
  GeneralDeclarativeInPlace327.current_sound checked covered List.mem_cons_self rfl
    GeneralDeclarativeRepeatResolve327.declared successful
    (trans (facts preparedSample [whereRow]) (facts beforeReturn [returnRow]))
    fixed_selected_where (fun _ included => List.mem_append_left _ (List.mem_append_right _ included))
    fixed_parent (fun _ included => List.mem_append_right _ included)
    (fun _ _ => fits extensions aggregate.1) actual_head


end Yulang.GeneralDeclarativeMixedReplay327
