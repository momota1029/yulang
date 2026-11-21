import Yulang.GeneralDeclarativeWhereLayouts325
import Yulang.GeneralDeclarativeNamedTree320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeFreshInputs325
open GeneralDeclarations (DeclarationChecked)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeSparseWhere325 (plan atPosition planned allocated compound_job)
open GeneralDeclarativeWhereLayouts325 (links spans accounted of_compound find_position)
open GeneralDeclarativeFreshWhere325 (seed newState projection compound_reads)
open GeneralDeclarativeWhereIntervals325 (semantic_bounds)
open GeneralDeclarativeReadScope320 (tracked_from_declared_inputs)
open GeneralDeclarativeClauseOrigins325 (Origin normalized_order)
open GeneralDeclarativeNamedTree320 (position)
open GeneralDeclarativeSubstitution320 (logical)
open GeneralDeclarativeEntailment320 (model_append)
open GeneralDeclarativeFootprint321 (stateNames)
open GeneralNominalCenteredHeadMatExpressions (Expr translateMany)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCommonBridge (Assignment)

def prepared (s : State) (protect : List Nat) (cap : Nat → Capture) (jobs : List (Option Expr)) : State :=
  let t := newState s protect cap jobs
  ⟨⟨t.normal.ordinary,t.normal.intervals ++ spans (seed s protect cap jobs) jobs⟩,t.equations⟩

theorem names_bounded {s : State} {j : Nat} (printed : jobs[j]? = some (some e)) :
    Bounds (prepared s protect cap jobs) (atPosition (seed s protect cap jobs) jobs j) := by
  have rows := accounted (start := seed s protect cap jobs) printed
  exact ⟨.interval (List.mem_append_right _ (rows List.mem_cons_self)),
    .interval (List.mem_append_right _ (rows (List.mem_cons_of_mem _ List.mem_cons_self)))⟩

theorem names_observed {s : State} {j : Nat} (printed : jobs[j]? = some (some e)) :
    let arg := atPosition (seed s protect cap jobs) jobs j
    let t := prepared s protect cap jobs
    Origin t arg.lower (logical cap .lower e) ∧ Origin t arg.center (logical cap .actual e) ∧
      Origin t arg.upper (logical cap .upper e) := by
  dsimp
  apply allocated ?_ printed
  intro row stored
  exact List.mem_append_right _ stored

theorem models_equal {s : State}
    (which : DeclarationChecked c roles decl) (inside : clause ∈ decl.requirements)
    (printed : translateMany c i (clause.arguments.map normalize) = some codes)
    (bound : ∀ key ∈ decl.inputNames, Bounds s (cap key)) (protect : List Nat) (m : Assignment) :
    let jobs := plan clause.arguments codes
    Models (prepared s protect cap jobs) m ↔ Models (newState s protect cap jobs) m := by
  dsimp
  constructor
  · intro valid
    exact ⟨⟨valid.1.1,fun link h => valid.1.2 link (List.mem_append_left _ h)⟩,valid.2⟩
  · intro valid
    refine ⟨⟨valid.1.1,?_⟩,valid.2⟩
    intro link h
    rcases List.mem_append.mp h with already|fresh
    · exact valid.1.2 link already
    · obtain ⟨j,e,read,located⟩ := of_compound fresh
      obtain ⟨p,sourcePos,codePos,nonDirect⟩ := find_position read
      have translations := position (normalized_order printed) sourcePos codePos
      have tracked := tracked_from_declared_inputs which inside (List.mem_of_getElem? sourcePos) translations bound
      have eqns := compound_reads s protect cap sourcePos codePos nonDirect
      have span := semantic_bounds tracked m ((model_append m).mp valid).1 valid eqns.1 eqns.2.1 eqns.2.2
      simp only [links,List.mem_cons,List.not_mem_nil,or_false] at located
      rcases located with rfl|rfl
      · exact span.1
      · exact span.2

/-- Every actual compound operand in one checked where clause receives
its three named values and two interval facts together. No fresh name
is used for a bare binder. The resulting state has exactly the old
model projection, including caller-protected fixed output names. -/
theorem whole_input_projection {s : State}
    (which : DeclarationChecked c roles decl) (inside : clause ∈ decl.requirements)
    (printed : translateMany c i (clause.arguments.map normalize) = some codes)
    (bound : ∀ key ∈ decl.inputNames, Bounds s (cap key)) (protect : List Nat) (m : Assignment) :
    let jobs := plan clause.arguments codes
    Models s m ↔ ∃ next, Models (prepared s protect cap jobs) next ∧
      ∀ n ∈ stateNames s ++ protect, next n = m n := by
  dsimp
  exact (projection s protect cap _ m).trans
    (exists_congr (fun next => and_congr_left' ((models_equal which inside printed bound protect next).symm)))

end Yulang.GeneralDeclarativeFreshInputs325
