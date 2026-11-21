import Yulang.GeneralDeclarativeObserverSource330
import Yulang.GeneralDeclarativeRecordResolve326

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeclarativeRecordReplay330
open GeneralDeclarativeRecordDecl326 (decl root child registry checked pat normalizedExpr normal)
open GeneralDeclarativeRecordResolve326 (declared)
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl)
open GeneralDeclarativeRecordSpine330 (Spine)
open GeneralDeclarativeRecordFieldRead330 (Fields one)
open GeneralDeclarativeRecordMaterial330 (tailRow readingRow ready preserved)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeStableReads329 (Heads)
open GeneralDeclarativeStableAssemble329 (frame_after)
open GeneralDeclarativeStableCompiler329 (Frame read)
open GeneralDeclarativeGrowth327 (trans)
open GeneralDeclarativeOpaqueConserve328 (Retains)
open GeneralDeclarativeEmissionForest322 (children)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDeclarations (Clause)
open GeneralDeclarativeRecordResidual323 (withTail)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralDeclarativeNFComplete324 (facts)
open GeneralDeclarativeCompileLists321 (Result)
open GeneralDeclarativeAssembly320 (Meaning)

abbrev endCode : Expr := .primitive .exactEmpty []
abbrev rows : List Equation :=
  [⟨0,.variable 12⟩,⟨12,.record 7 (.variable 3) (.variable 13)⟩,
   ⟨13,.record 7 (.variable 4) (.variable 14)⟩,
   ⟨14,.record 8 (.variable 4) (.variable 15)⟩,⟨15,endCode⟩,
   ⟨3,.primitive (.scalar .int) []⟩,⟨4,.primitive (.scalar .bool) []⟩]
abbrev input : State := ⟨⟨[],[]⟩,rows⟩
abbrev raw : List (Nat × Expr) := [(7,.variable 3),(7,.variable 4),(8,.variable 4)]
abbrev selected : List (Nat × Expr) := [(7,.variable 3)]
abbrev shape : List (Nat × Expr) := [(7,.variable 0)]
abbrev keep := [5,6]
abbrev actualTail := tailRow input 0 keep raw [7] endCode
abbrev rebuilt := ready input 0 keep raw selected [7] endCode
abbrev uses := [(0,point 3),(1,point actualTail.left)]

def support (done : Nat → Prop) : Supported input done :=
  ⟨fun eq origin => eq ∈ rows ∧ origin = .source,fun h => h.1⟩

theorem known (done : Nat → Prop) {row : Equation} (part : row ∈ rows) :
    row ∈ (restriction (support done)).equations :=
  from_source _ ⟨part,rfl⟩

theorem spine (done : Nat → Prop) : Spine (restriction (support done)) 0 raw endCode := by
  refine .cons (rest := 13) (.forward (known done (show (⟨0,.variable 12⟩ : Equation) ∈ rows from List.mem_cons_self)))
    (known done (List.mem_cons_of_mem _ List.mem_cons_self)) ?_
  refine .cons (rest := 14) (alias_refl _) (known done (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))) ?_
  refine .cons (rest := 15) (alias_refl _) (known done (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))) ?_
  exact .exactEnd (alias_refl _) (known done (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))

theorem fields (done : Nat → Prop) : Fields (support done) selected shape [(0,point 3)] := by
  exact .cons (here := [(0,point 3)]) .capture (.cons ⟨rfl,rfl,point_bounded input 3⟩ .nil) .nil

theorem exact_tail : actualTail = ⟨16,.record 8 (.variable 4) endCode⟩ := rfl
theorem exact_remainder_name : readingRow input 0 keep raw selected [7] endCode =
    ⟨0,.record 7 (.variable 3) (.variable 16)⟩ := rfl
theorem actual_observation :
    Retains input rebuilt keep ∧ Heads rebuilt catalogue interpretation root.arguments decl.head uses ∧
      ∀ use ∈ uses, Bounds rebuilt use.2 := by
  obtain ⟨lift,actual,span⟩ := one (p := support (fun _ => False)) (point_bounded input 0)
    (spine _) (keyList := [7]) (by decide) (show GeneralDeclarativeOrderedRecord326.order
      (CommonRoleCanonicalRows.normalize raw) [7] = some selected from rfl)
    (fields _) normal keep
  exact ⟨lift,.cons (rest := []) actual .nil,span⟩

def fallback (_ : Nat) : Capture := point 3
def target (_ : Clause) (_ : Nat) : Nat := 5

open GeneralDeclarativeEntailment320 (appendFacts model_append)
open GeneralDeclarativeStableTies329 (rows pairOf Consequence)
open GeneralDeclarativeOpaqueCapture328 (choose)
open GeneralDeclarativeAppliedClause327 (targetsOnly)
open GeneralDeclarativeClauseBatch327 (prepare make Port)
open GeneralDeclarativeClausePlacement327 (placement)
open GeneralDeclarativeFrameReadback325 (sourceNames)
open GeneralDeclarativeGrowth327 (Extends fits)
open GeneralDeclarativeStableReads329 (weakened)
open GeneralDeclarativeBatch320 (collect)
open GeneralDeclarativeNormalizeAssoc324 (one)
open GeneralDeclarativePairDecl326 (clause)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeOutputSource323 (Declared)

abbrev base (n : Nat) : Capture := choose fallback n uses
abbrev cap := (sourceNames decl (targetsOnly target) base).input
abbrev ports : List Port := [make rebuilt keep cap clause [.variable 0]]
abbrev place := placement decl.requirements ports target
abbrev named := sourceNames decl place base
abbrev returned : Equation := ⟨6,.variable 16⟩
abbrev childWrite : Equation := ⟨5,.variable 3⟩
abbrev final := appendFacts (appendFacts rebuilt [returned]) [childWrite]

theorem calc_children : children decl named place = [child] := rfl
theorem only_output : collect (one registry interpretation decl root named.input) root.outputs = some [returned] := rfl
theorem prepare_exact : prepare catalogue interpretation keep cap rebuilt decl.requirements = some (rebuilt,ports) := rfl
theorem old_grows : Extends rebuilt final := trans (GeneralDeclarativeGrowth327.facts _ _) (GeneralDeclarativeGrowth327.facts _ _)

def frame : Frame final registry interpretation root decl [child] :=
  ⟨base,uses,weakened old_grows actual_observation.2.1,(by
    intro _ h
    have empty : GeneralDeclarativeStableTies329.rows base (uses.map pairOf) = [] := rfl
    rw [empty] at h
    cases h), (by
      intro n h
      have isInput : n ∈ [0,1] := h
      rcases List.mem_cons.mp isInput with rfl|other
      · exact point_bounded final 3
      · cases List.mem_singleton.mp other
        exact point_bounded final 16),
    target,keep,rebuilt,rebuilt,ports,prepare_exact,old_grows,[],rfl,
    fun _ h => False.elim (List.not_mem_nil h),[returned],only_output,
    fun _ h => List.mem_append_left _ (List.mem_append_right _ h),rfl⟩

theorem user_readback (coverage : Coverage registry interpretation) :
    Result final (facts registry interpretation frame.capture decl root [child]) ∧
      (∀ m, Models final m → Meaning registry interpretation m root decl frame.capture [child]) ∧
      ∀ child' ∈ [child], Declared registry child' :=
  read checked coverage List.mem_cons_self rfl declared frame

open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (Ty record exactEmpty)
open GeneralNominalCenteredHeadMatPatternSemantics (eqv_refl eqv_symm eqv_trans)
open GeneralDeclarativeExampleSource320 (int)
open GeneralNominalCenteredHeadWFSource (DeclarationCovered)

theorem covered : Coverage registry interpretation := by
  constructor
  · intro d inRegistry
    rcases List.mem_cons.mp inRegistry with rfl|rest
    · refine ⟨⟨⟨trivial,trivial⟩,trivial⟩,?_,?_⟩
      · intro cl needed
        cases List.mem_singleton.mp needed
        refine ⟨⟨trivial,trivial⟩,?_⟩
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
      by_cases eq : name = 0 <;>
        simp [GeneralDeclarationExamples.roles,GeneralDeclarationExamples.outputRole,eq] at h
    by_cases isC : role = 2
    · subst role
      by_cases eq : name = 1 <;>
        simp [GeneralDeclarationExamples.roles,GeneralDeclarationExamples.outputRole,eq] at h
    by_cases isB : role = 4 <;> simp [GeneralDeclarationExamples.roles,GeneralDeclarationExamples.bareRole,
      GeneralDeclarationExamples.binaryRole,isP,isC,isB] at h

abbrev flag : Ty := .base .bool
abbrev residualTy := record 8 flag exactEmpty
abbrev hiddenRowTy := record 7 flag residualTy
abbrev rootTy := record 7 int hiddenRowTy

def witness : Assignment := fun n =>
  (if n = 0 ∨ n = 12 then rootTy else if n = 13 then hiddenRowTy else
    if n = 6 ∨ n = 14 ∨ n = 16 then residualTy else if n = 15 then exactEmpty else
    if n = 4 then flag else int, Common.rowEmpty)

theorem root_model : Models input witness := by
  refine ⟨⟨PresenceNormalForm.all_nil _ _,fun _ h => False.elim (List.not_mem_nil h)⟩,?_⟩
  intro e used
  change e ∈ rows at used
  simp only [rows,List.mem_cons,List.not_mem_nil,or_false] at used
  rcases used with h|h|h|h|h|h|h <;> cases h
  all_goals exact eqv_refl _

theorem rebuilt_model : Models rebuilt witness := by
  let ts := GeneralDeclarativeRecordMaterial330.namedTail input 0 keep raw [7] endCode
  have tail_model : Models ts witness := (model_append _).mpr ⟨root_model,fun e its => by
    cases List.mem_singleton.mp its
    exact eqv_refl _⟩
  apply (model_append _).mpr
  refine ⟨tail_model,fun e inRows => ?_⟩
  cases List.mem_singleton.mp inRows
  exact GeneralDeclarativeRecordMaterial330.right (spine (fun _ => False)) (keys := [7])
    (by decide) (show GeneralDeclarativeOrderedRecord326.order (CommonRoleCanonicalRows.normalize raw)
      [7] = some selected from rfl) keep _ tail_model

theorem populated : Models final witness := by
  apply (model_append _).mpr
  refine ⟨(model_append _).mpr ⟨rebuilt_model,?_⟩,?_⟩
  all_goals
    intro e shown
    cases List.mem_singleton.mp shown
    exact eqv_refl _

end Yulang.GeneralDeclarativeRecordReplay330
