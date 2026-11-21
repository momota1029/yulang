import Yulang.GeneralDeclarativeStableSelect329
import Yulang.GeneralDeclarativeOpaqueRepeatCut328
import Yulang.GeneralDeclarativeRepeatDecl327
import Yulang.GeneralDeclarativeVisibleCode325

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeStableFixture329
open GeneralDeclarativeRepeatDecl327
open GeneralDeclarativeOpaqueFixture328 (initial prepared oldRows leftCapture rightCapture root_range)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeHead320 (State Models Equation)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeStableTies329 (Consequence rows pairOf present_entails)
open GeneralDeclarativeStableReads329 (Heads)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeClauseBatch327 (prepare make)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeAppliedClause327 (targetsOnly)
open GeneralDeclarativeEntailment320 (appendFacts)
open GeneralDeclarativeGrowth327 (Extends trans facts fits)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarations (Clause)
open GeneralDeclarationExamples (constructors roles bareRole binaryRole outputRole itemEquation)
open GeneralNominalCenteredHeadMatExpressions (translateMany)
open GeneralDeclarativeVisibleCode325 (codes_were_covered)
open GeneralDeclarativeOpaqueBatch328 (check)
open GeneralDeclarativeOutputSource323 (Declared)

abbrev spans : List (Nat × Capture) := [(0,leftCapture),(0,rightCapture)]
abbrev base (_ : Nat) := leftCapture
abbrev tie : Equation := ⟨7,.variable 8⟩
abbrev tied := appendFacts prepared (rows base (spans.map pairOf))
abbrev keep : List Nat := [5,6]
abbrev targets (_ : Clause) (_ : Nat) : Nat := 5
abbrev cap := (sourceNames impl (targetsOnly targets) base).input
abbrev jobs := GeneralDeclarativeSparseWhere325.plan clause.arguments [compoundCode]
abbrev inputState := GeneralDeclarativeFreshInputs325.prepared tied keep cap jobs
abbrev ports := [make tied keep cap clause [compoundCode]]
abbrev place := placement impl.requirements ports targets
abbrev names := sourceNames impl place base
abbrev cas : Capture := ⟨9,10,11⟩
abbrev child : Demand := ⟨2,[cas],[⟨1,5⟩]⟩
abbrev inputRows : List Equation := [⟨9,.nominal 0 [.variable 7]⟩,
    ⟨10,.nominal 0 [.variable 7]⟩,⟨11,.nominal 0 [.variable 7]⟩]
abbrev returnRow : Equation := ⟨6,.variable 5⟩
abbrev childRow : Equation := ⟨5,.variable 10⟩
abbrev final := appendFacts (appendFacts inputState [returnRow]) [childRow]
abbrev pairRow : Equation := ⟨1,GeneralDeclarativePairCenters326.pair (.variable 7) (.variable 8)⟩

theorem tie_exact : rows base (spans.map pairOf) = [tie] := rfl
theorem prior_untied : tie ∉ prepared.equations := by
  change tie ∉ oldRows ++ [pairRow]
  simp only [oldRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
  rintro (h|h|h|h) <;> have impossible := congrArg Equation.left h <;> cases impossible
theorem generated : prepare reg.constructors interp keep cap tied impl.requirements = some (inputState,ports) := rfl
theorem exact_input : inputState.equations = oldRows ++ [pairRow,tie] ++ inputRows := rfl
theorem exact_child : children impl names place = [child] := rfl
theorem exact_return : GeneralDeclarativeBatch320.collect
    (GeneralDeclarativeNormalizeAssoc324.one reg interp impl root names.input) root.outputs = some [returnRow] := rfl
theorem wrong_return_rejected : check (children impl names place) [⟨2,[cas],[⟨1,6⟩]⟩] = false := rfl

theorem ordinary_rows {e : Equation} (h : e ∈ oldRows ++ [pairRow,tie] ++ inputRows) : e ∈ final.equations :=
  List.mem_append_left _ (List.mem_append_left _ (exact_input.symm ▸ h))
theorem where_grows : Extends inputState final := trans (facts _ _) (facts _ _)
theorem pre_grows : Extends prepared final := by
  refine ⟨?_,?_,?_⟩
  · intro a h; exact h
  · intro a h; exact List.mem_append_left _ h
  · intro e h
    apply ordinary_rows
    rcases List.mem_append.mp h with old|one
    · exact List.mem_append_left _ (List.mem_append_left _ old)
    · cases List.mem_singleton.mp one
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)

theorem current_tie : Consequence final base (spans.map pairOf) := by
  apply present_entails
  intro e used
  rw [tie_exact] at used
  cases List.mem_singleton.mp used
  exact ordinary_rows (List.mem_append_left _ (List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)))

theorem root_range_now : Bounds final arg :=
  fits pre_grows ⟨.interval List.mem_cons_self,.interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩
theorem capture_range : Bounds final leftCapture :=
  fits pre_grows (GeneralDeclarativeOpaqueIntervals328.bounds (s := initial) 1 [5,6]
    GeneralDeclarativeOpaqueFixture328.endpoints).1
theorem child_range : Bounds final cas :=
  fits where_grows (GeneralDeclarativeFreshInputs325.names_bounded (s := tied) (protect := keep) (cap := cap) (jobs := jobs) (j := 0) (e := compoundCode) rfl)

theorem parent_observed : Heads final reg.constructors interp root.arguments impl.head spans := by
  change Heads final reg.constructors interp [arg] [headPat] (spans ++ [])
  apply Heads.cons (rest := [])
  · refine ⟨root_range_now,headCode,pairRow.right,rfl, .row (ordinary_rows
      (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))),?_⟩
    exact .primitive (.cons .capture (.cons .capture .nil))
  · exact .nil

theorem child_observed : Heads final reg.constructors interp child.arguments leaf.head [(0,cas)] := by
  change Heads final reg.constructors interp [cas] [.var 0] ([(0,cas)] ++ [])
  exact .cons ⟨child_range,.variable 0,.variable 10,rfl,.refl _,.capture⟩ .nil

theorem coverage : Coverage reg interp := by
  constructor
  · intro d visible
    rcases List.mem_cons.mp visible with rfl|rest
    · refine ⟨(codes_were_covered (xs := [headCode])
        (show translateMany constructors interp [headPat] = _ from rfl)).1,?_,?_⟩
      · intro cl needed
        cases List.mem_singleton.mp needed
        refine ⟨(codes_were_covered (xs := [compoundCode])
          (show translateMany constructors interp clause.arguments = _ from rfl)).1,?_⟩
        intro eq wanted
        cases List.mem_singleton.mp wanted
        trivial
      · intro eq present
        cases List.mem_singleton.mp present
        trivial
    · cases List.mem_singleton.mp rest
      exact ⟨⟨trivial,trivial⟩,fun _ absent => False.elim (List.not_mem_nil absent),
        fun eq found => by cases List.mem_singleton.mp found; trivial⟩
  · intro role name term h
    by_cases isP : role = 1
    · subst role
      by_cases eq : name = 0 <;> simp [roles,outputRole,eq] at h
    by_cases isC : role = 2
    · subst role
      by_cases eq : name = 1 <;> simp [roles,outputRole,eq] at h
    by_cases isB : role = 4 <;> simp [roles,bareRole,binaryRole,isP,isC,isB] at h

def frame : Frame final reg interp root impl [child] :=
  ⟨base,spans,parent_observed,current_tie,fun _ _ => capture_range,targets,keep,tied,inputState,ports,
    generated,where_grows,[],rfl,fun _ h => False.elim (List.not_mem_nil h),[returnRow],
    exact_return,fun _ h => List.mem_append_left _ (List.mem_append_right _ h),rfl⟩

def leafBase (_ : Nat) := cas
def childFrame : Frame final reg interp child leaf [] :=
  ⟨leafBase,[(0,cas)],child_observed,(by
    intro _ h; cases h),fun _ _ => child_range,targets,keep,final,final,[],rfl,⟨fun _ h => h,fun _ h => h,fun _ h => h⟩,
    [],rfl,fun _ h => False.elim (List.not_mem_nil h),[childRow],rfl,
    fun _ h => List.mem_append_right _ h,rfl⟩

end Yulang.GeneralDeclarativeStableFixture329
