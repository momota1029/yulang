import Yulang.GeneralDeclarativeStableSelect329
import Yulang.GeneralDeclarativeArityCompiler330
import Yulang.GeneralDeclarativeRepeatDecl327
import Yulang.GeneralDeclarativeVisibleCode325

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 10000000
namespace Yulang.GeneralDeclarativeArityFixture330
open GeneralDeclarativeRepeatDecl327 (reg impl headPat compoundCode compound clause body root arg checked)
open GeneralDeclarativeArityRun330 (run build)
open GeneralDeclarativeArityPlan330 (Reads Plan Plans Shape Shapes)
open GeneralDeclarativeArityNominal330 (row)
open GeneralDeclarativeOpaqueNominal328 (point)
open GeneralDeclarativeAritySource330 (Source)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeLowerKnown321 (alias_refl)
open GeneralNominalInspection (Interpretation)
open GeneralNominalCenteredHeadMatExpressions (Expr)
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

def interp : Interpretation := ⟨fun _ => none,fun n => n == 0 || n == 5,by simp⟩
abbrev headCode : Expr := .nominal 5 [.variable 0,.variable 0]
abbrev lower := row 0 5 [3,4]
abbrev upper := row 2 5 [7,8]
abbrev scalar : Equation := ⟨3,.primitive (.scalar .int) []⟩
abbrev oldRows := [lower,upper,scalar]
abbrev initial : State := ⟨⟨[],[(0,1),(1,2)]⟩,oldRows⟩
abbrev plan : Plan := .nominal 5 [7,8] (.cons 3 (.capture 0) (.cons 4 (.capture 0) .nil))
abbrev prepResult := run [5,6] initial arg plan
abbrev prepared := prepResult.state
abbrev spans : List (Nat × Capture) := [(0,point 3),(0,point 4)]
abbrev base (_ : Nat) := point 3
abbrev tie : Equation := ⟨3,.variable 4⟩
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
abbrev inputRows : List Equation := [⟨9,.nominal 0 [.variable 3]⟩,
    ⟨10,.nominal 0 [.variable 3]⟩,⟨11,.nominal 0 [.variable 3]⟩]
abbrev returnRow : Equation := ⟨6,.variable 5⟩
abbrev childRow : Equation := ⟨5,.variable 10⟩
abbrev final := appendFacts (appendFacts inputState [returnRow]) [childRow]
abbrev pairRow := row 1 5 [3,4]

theorem tie_exact : rows base (spans.map pairOf) = [tie] := rfl
theorem prior_untied : tie ∉ prepared.equations := by
  change tie ∉ oldRows ++ [pairRow]
  simp only [oldRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false]
  rintro (h|h|h|h)
  · cases congrArg Equation.left h
  · cases congrArg Equation.left h
  · cases congrArg Equation.right h
  · cases congrArg Equation.left h

def priorSupport (done : Nat → Prop) : Supported initial done :=
  ⟨fun e o => e ∈ oldRows ∧ o = .source,fun h => h.1⟩
theorem covered_shape : Shape headCode := .nominal (.cons .capture (.cons .capture .nil))
theorem root_range : Bounds initial arg := ⟨.interval List.mem_cons_self,
  .interval (List.mem_cons_of_mem _ List.mem_cons_self)⟩

theorem actual_source (done : Nat → Prop) :
    Source initial reg.constructors interp (priorSupport done) root.arguments impl.head := by
  refine .concealed ⟨root_range,headCode,[⟨0,.actual,3⟩,⟨0,.actual,4⟩],
    [⟨0,.actual,7⟩,⟨0,.actual,8⟩],rfl,?_,?_⟩ ?_ .nil
  · exact .nominal (args := [3,4]) (alias_refl _)
      (from_source _ ⟨List.mem_cons_self,rfl⟩) (.cons .capture (.cons .capture .nil))
  · exact .nominal (args := [7,8]) (alias_refl _)
      (from_source _ ⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩) (.cons .capture (.cons .capture .nil))
  · intro code h
    change some headCode = some code at h
    cases Option.some.inj h
    exact covered_shape

theorem actual_plan : Reads initial 0 2 plan :=
  .nominal (.row List.mem_cons_self) (.row (List.mem_cons_of_mem _ List.mem_cons_self))
    (.cons .capture (.cons .capture .nil))

theorem actual_pack : GeneralDeclarativeArityRun330.Builds [5,6] initial arg plan :=
  build [5,6] arg plan root_range actual_plan

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
theorem capture_range : Bounds final (point 3) := ⟨.refl _,.refl _⟩

theorem child_range : Bounds final cas :=
  fits where_grows (GeneralDeclarativeFreshInputs325.names_bounded (s := tied) (protect := keep) (cap := cap) (jobs := jobs) (j := 0) (e := compoundCode) rfl)

theorem parent_observed : Heads final reg.constructors interp root.arguments impl.head spans := by
  change Heads final reg.constructors interp [arg] [headPat] (spans ++ [])
  apply Heads.cons (rest := [])
  · refine ⟨root_range_now,headCode,pairRow.right,rfl, .row (ordinary_rows
      (List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self))),?_⟩
    exact .nominal (.cons .capture (.cons .capture .nil))
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

end Yulang.GeneralDeclarativeArityFixture330
