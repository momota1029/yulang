import Yulang.GeneralDeclarativeArityFixture330
import Yulang.GeneralDeclarativeRank321
import Yulang.GeneralDeclarativeOutputOrigins323

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralDeclarativeArityProbe330
open GeneralDeclarativeRepeatDecl327 (reg impl root)
open GeneralDeclarativeArityFixture330
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (Supported restriction from_source)
open GeneralDeclarativeOutputOrigins323 (emit)
open GeneralDeclarativeLowerKnown321 (Ready Alias knows_row alias_refl)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)

def source (done : Nat → Prop) : Supported inputState done :=
  ⟨fun e o => e ∈ oldRows ++ inputRows ∧ o = .source,by
    intro e o h
    rw [exact_input]
    rcases List.mem_append.mp h.1 with before|generated
    · exact List.mem_append_left _ (List.mem_append_left _ before)
    · exact List.mem_append_right _ generated⟩

abbrev support (done : Nat → Prop) := emit (emit (source done) 1 [returnRow]) 2 [childRow]

theorem authorized (done : Nat → Prop) {e : Equation} (row : e ∈ oldRows ++ inputRows) :
    e ∈ (restriction (support done)).equations :=
  from_source _ (.inl (.inl ⟨row,rfl⟩))

theorem root_ready (done : Nat → Prop) : Ready (support done) root := by
  intro a chosen
  cases List.mem_singleton.mp chosen
  exact ⟨_,knows_row (authorized done (List.mem_append_left _
    (show (lower : Equation) ∈ oldRows from List.mem_cons_self))) rfl⟩

theorem child_ready (done : Nat → Prop) : Ready (support done) child := by
  intro a chosen
  cases List.mem_singleton.mp chosen
  exact ⟨_,knows_row (authorized done (List.mem_append_right _
    (show (⟨9,.nominal 0 [.variable 3]⟩ : Equation) ∈ inputRows from List.mem_cons_self))) rfl⟩

theorem root_matches (done : Nat → Prop) :
    HeadMatches (restriction (support done)) reg.constructors interp root impl := by
  refine .cons ⟨root_range_now,headCode,[⟨0,.actual,3⟩,⟨0,.actual,4⟩],
    [⟨0,.actual,7⟩,⟨0,.actual,8⟩],rfl,?_,?_⟩ .nil
  · exact .nominal (args := [3,4]) (alias_refl _)
      (authorized done (List.mem_append_left _ (show lower ∈ oldRows from List.mem_cons_self)))
      (.cons .capture (.cons .capture .nil))
  · exact .nominal (args := [7,8]) (alias_refl _)
      (authorized done (List.mem_append_left _ (show upper ∈ oldRows from
        List.mem_cons_of_mem _ List.mem_cons_self))) (.cons .capture (.cons .capture .nil))

theorem child_matches (done : Nat → Prop) :
    HeadMatches (restriction (support done)) reg.constructors interp child leaf :=
  .cons ⟨child_range,.variable 0,[⟨0,.lower,9⟩],[⟨0,.upper,11⟩],rfl,.capture,.capture⟩ .nil

def rank (n : Nat) : Nat := if n ≤ 2 ∨ 9 ≤ n ∨ n = 5 ∨ n = 6 then 1 else 0

theorem table : final.equations = oldRows ++ [pairRow,tie] ++ inputRows ++ [returnRow,childRow] := rfl

theorem alias_rank {a b : Nat} (h : Alias final a b) : rank a = rank b := by
  have written {a b : Nat} (which : (⟨a,.variable b⟩ : Equation) ∈ final.equations) :
      rank a = rank b := by
    rw [table] at which
    simp only [oldRows,inputRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at which
    rcases which with x|x|x|x|x|x|x|x|x|x <;> cases x <;> rfl
  have bounds {a b} (h : GeneralDeclarativeBounds319.Bound final.normal a b) : rank a = rank b := by
    induction h with
    | refl => rfl
    | interval given =>
      change _ ∈ [(0,1),(1,2),(9,10),(10,11)] at given
      simp only [List.mem_cons,List.not_mem_nil,or_false] at given
      rcases given with x|x|x|x <;> cases x <;> rfl
    | constraint given => cases given
    | trans _ _ first last => exact first.trans last
  induction h with
  | bounds forward _ => exact bounds forward
  | forward h => exact written h
  | backward h => exact (written h).symm
  | trans _ _ first last => exact first.trans last

theorem acyclic : ∀ n, ¬AliasCycle final (observed final) n := by
  apply graph_no_cycle rank (fun _ _ h => alias_rank h)
  rintro n shape child ⟨code,submitted,read⟩ part
  rw [table] at submitted
  simp only [oldRows,inputRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at submitted
  rcases submitted with x|x|x|x|x|x|x|x|x|x <;> cases x
  all_goals cases read
  all_goals simp [GeneralDeclarativeK2Graph321.Shape.children] at part
  all_goals first
    | (rcases part with rfl|rfl; all_goals decide +kernel)
    | (subst child; decide +kernel)

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (support done)) reg.constructors interp,
    fun d impl => ¬HeadMatches (restriction (support done)) reg.constructors interp d impl⟩

theorem safe (done : Nat → Prop) (d : Demand) : ¬Recurs final reg interp (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact acyclic arg.lower cycle
  · exact acyclic site cycle

end Yulang.GeneralDeclarativeArityProbe330
