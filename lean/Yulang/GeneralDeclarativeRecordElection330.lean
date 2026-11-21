import Yulang.GeneralDeclarativeRecordReplay330
import Yulang.GeneralDeclarativeRank321

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 12000
set_option maxHeartbeats 9000000
namespace Yulang.GeneralDeclarativeRecordElection330
open GeneralDeclarativeRecordDecl326 (decl root child registry checked pat normalizedExpr normal)
open GeneralDeclarativeRecordReplay330
open GeneralDeclarativeHiddenDecl324 (catalogue interpretation)
open GeneralDeclarativeHead320 (State Equation Models)
open GeneralDeclarativeDemand320 (Demand Bounds)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeLowerKnown321 (Alias alias_refl Ready knows_alias knows_row)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeGrowth327 (Extends)
open GeneralDeclarativeStableCompiler329 (Frame)
open GeneralDeclarativeStableSelect329 (Rule sound)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeEvidence320 (Evidence)
open GeneralDeclarativeRecordResolve326 (root_only child_only declared dictionary)
open CommonRoleOutermostResolver (Classify)

-- The generated ordinary read rows are deliberately not admitted as
-- source origins for this current election.
def current (done : Nat → Prop) : Supported final done :=
  ⟨fun e o => e ∈ rows ∧ o = .source,by
    intro e o h
    exact old_grows.equations (actual_observation.1.grows.equations h.1)⟩

theorem backed (done : Nat → Prop) {e : Equation} (part : e ∈ rows) :
    e ∈ (restriction (current done)).equations := from_source _ ⟨part,rfl⟩

theorem starts (done : Nat → Prop) : Alias (restriction (current done)) 0 12 :=
  .forward (backed done (show (⟨0,.variable 12⟩ : Equation) ∈ rows from List.mem_cons_self))

theorem root_ready (done : Nat → Prop) : Ready (current done) root := by
  intro a chosen
  cases List.mem_singleton.mp chosen
  exact ⟨_,knows_alias (starts done) (knows_row
    (backed done (show (⟨12,.record 7 (.variable 3) (.variable 13)⟩ : Equation) ∈ rows from
      List.mem_cons_of_mem _ List.mem_cons_self)) rfl)⟩

theorem child_ready (done : Nat → Prop) : Ready (current done) child := by
  intro a chosen
  cases List.mem_singleton.mp chosen
  exact ⟨_,knows_row (backed done (show (⟨3,.primitive (.scalar .int) []⟩ : Equation) ∈ rows from
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))))) rfl⟩

theorem endpoint_trace (done : Nat → Prop) (mode) :
    Trace (restriction (current done)) mode 0 normalizedExpr [⟨0,mode,3⟩,⟨1,mode,13⟩] :=
  .record (starts done) (backed done (List.mem_cons_of_mem _ List.mem_cons_self)) .capture .capture

theorem root_matches (done : Nat → Prop) :
    HeadMatches (restriction (current done)) catalogue interpretation root decl :=
  .cons ⟨point_bounded _ 0,normalizedExpr,_,_,normal,endpoint_trace done _,endpoint_trace done _⟩ .nil

theorem child_matches (done : Nat → Prop) :
    HeadMatches (restriction (current done)) catalogue interpretation child leaf :=
  .cons ⟨point_bounded _ 3,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,3⟩],rfl,.capture,.capture⟩ .nil

def rank (n : Nat) : Nat :=
  if n = 0 ∨ n = 12 then 4 else if n = 13 then 3 else
  if n = 6 ∨ n = 14 ∨ n = 16 then 2 else if n = 15 then 1 else 0

theorem table : final.equations = rows ++ [actualTail,⟨0,.record 7 (.variable 3) (.variable 16)⟩,
    returned,childWrite] := rfl

theorem alias_rank {a b} (seen : Alias final a b) : rank a = rank b := by
  have rowsAre {a b : Nat} (alias : (⟨a,.variable b⟩ : Equation) ∈ final.equations) :
      rank a = rank b := by
    rw [table] at alias
    simp only [rows,exact_tail,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at alias
    rcases alias with h|h|h|h|h|h|h|h|h|h|h <;> cases h <;> rfl
  have boundsAre {a b} (bound : GeneralDeclarativeBounds319.Bound final.normal a b) :
      rank a = rank b := by
    induction bound with
    | refl => rfl
    | interval impossible => cases impossible
    | constraint impossible => cases impossible
    | trans _ _ x y => exact x.trans y
  induction seen with
  | bounds h _ => exact boundsAre h
  | forward h => exact rowsAre h
  | backward h => exact (rowsAre h).symm
  | trans _ _ x y => exact x.trans y

theorem no_cycles : ∀ n, ¬AliasCycle final (observed final) n := by
  apply graph_no_cycle rank (fun _ _ h => alias_rank h)
  rintro n shape child ⟨code,submitted,read⟩ part
  rw [table] at submitted
  simp only [rows,exact_tail,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at submitted
  rcases submitted with h|h|h|h|h|h|h|h|h|h|h <;> cases h
  all_goals cases read
  all_goals simp [GeneralDeclarativeK2Graph321.Shape.children] at part
  all_goals first
    | (rcases part with rfl|rfl; all_goals decide +kernel)
    | (subst child; decide +kernel)

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (current done)) catalogue interpretation,
    fun d impl => ¬ HeadMatches (restriction (current done)) catalogue interpretation d impl⟩

theorem safe (done : Nat → Prop) (d : Demand) : ¬ Recurs final registry interpretation (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles site cycle

abbrev branch (done : Nat → Prop) := Rule final registry interpretation (current done) (tests done)
def leafBase (_ : Nat) := point 3

def leafFrame : Frame final registry interpretation child leaf [] :=
  ⟨leafBase,[(0,point 3)],
    (by
      change GeneralDeclarativeStableReads329.Heads final catalogue interpretation [point 3] [.var 0] ([(0,point 3)] ++ [])
      exact .cons ⟨point_bounded _ 3,.variable 0,.variable 3,rfl,.refl _,.capture⟩ .nil),
    (by intro _ impossible; cases impossible),fun _ _ => point_bounded _ 3,
    target,keep,final,final,[],rfl,⟨fun _ h => h,fun _ h => h,fun _ h => h⟩,
    [],rfl,fun _ impossible => False.elim (List.not_mem_nil impossible),
    [childWrite],rfl,fun _ h => List.mem_append_right _ h,rfl⟩

theorem root_selected (done : Nat → Prop) : branch done root (.selected decl.id [child]) := by
  refine .selected (root_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_self,rfl⟩,root_matches done⟩ ?_ ⟨frame⟩
  · rintro ⟨d,⟨visible,role⟩,wait⟩
    cases root_only d visible role
    exact wait (root_matches done)
  · rintro d ⟨⟨visible,role⟩,_⟩
    rw [root_only d visible role]

theorem child_selected (done : Nat → Prop) : branch done child (.selected leaf.id []) := by
  refine .selected (child_ready done) (safe done _) ?_
    ⟨⟨List.mem_cons_of_mem _ List.mem_cons_self,rfl⟩,child_matches done⟩ ?_ ⟨leafFrame⟩
  · rintro ⟨d,⟨visible,role⟩,wait⟩
    cases child_only d visible role
    exact wait (child_matches done)
  · rintro d ⟨⟨visible,role⟩,_⟩
    rw [child_only d visible role]

theorem tree (done : Nat → Prop) : Classify (branch done) root (.selected dictionary) :=
  ⟨.selected decl.id [.selected leaf.id []],
    .selected (root_selected done) (.cons (.selected (child_selected done) .nil) .nil),
    .selected (.cons (.selected .nil (.selected rfl)) .nil) (.selected rfl)⟩

/-- The raw endpoint says tail 13, while the compiler captures name 16
from actual subtraction: hidden label 7 is removed, label 8 and the
exact closed terminator remain. The actual child consumes the payload,
whereas target 6 receives the computed remainder. -/
theorem protected_tail :
    frame.capture 1 = point 16 ∧ frame.rootRows = [⟨6,.variable 16⟩] ∧
      Models final witness ∧ (∀ m : GeneralNominalCommonBridge.Assignment, Models final m → Evidence registry interpretation m root dictionary) :=
  ⟨rfl,rfl,populated,fun _ valid => sound checked covered declared valid (tree (fun _ => False))⟩

end Yulang.GeneralDeclarativeRecordElection330
