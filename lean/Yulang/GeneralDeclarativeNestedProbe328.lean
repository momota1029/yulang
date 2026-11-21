import Yulang.GeneralDeclarativeNestedState328
import Yulang.GeneralDeclarativeRank321

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralDeclarativeNestedProbe328
open GeneralDeclarativeNestedDecl328
open GeneralDeclarativeNestedState328
open GeneralDeclarationExamples (constructors)
open GeneralDeclarativeExampleSource320 (leaf)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeOrigins321 (restriction)
open GeneralDeclarativeLowerKnown321 (Ready Alias knows_row alias_refl)
open GeneralDeclarativeTrace321 (Trace)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)

theorem lo_trace (done : Nat → Prop) :
    Trace (restriction (support done)) .lower 0 normalCode
      [⟨0,.lower,3⟩,⟨1,.actual,9⟩] :=
  .primitive (args := [11,12]) (alias_refl _) (authorized done List.mem_cons_self)
    (.cons (.variant (alias_refl _) (authorized done
      (show (⟨11,lowVar⟩ : Equation) ∈ sourceRows by simp [sourceRows])) .capture)
      (.cons (.nominal (args := [9]) (alias_refl _) (authorized done
        (show (⟨12,lowNom⟩ : Equation) ∈ sourceRows by simp [sourceRows])) (.cons .capture .nil)) .nil))

theorem hi_trace (done : Nat → Prop) :
    Trace (restriction (support done)) .upper 2 normalCode
      [⟨0,.upper,4⟩,⟨1,.actual,10⟩] :=
  .primitive (args := [13,14]) (alias_refl _) (authorized done
    (show (⟨2,hi⟩ : Equation) ∈ sourceRows by simp [sourceRows]))
    (.cons (.variant (alias_refl _) (authorized done
      (show (⟨13,highVar⟩ : Equation) ∈ sourceRows by simp [sourceRows])) .capture)
      (.cons (.nominal (args := [10]) (alias_refl _) (authorized done
        (show (⟨14,highNom⟩ : Equation) ∈ sourceRows by simp [sourceRows])) (.cons .capture .nil)) .nil))

theorem parent_ready (done : Nat → Prop) : Ready (support done) root := by
  intro a here
  cases List.mem_singleton.mp here
  exact ⟨_,knows_row (authorized done (show (⟨0,lo⟩ : Equation) ∈ sourceRows from List.mem_cons_self)) rfl⟩

theorem child_ready (done : Nat → Prop) : Ready (support done) child := by
  intro a here
  cases List.mem_singleton.mp here
  exact ⟨_,knows_row (authorized done (show (⟨3,scalar⟩ : Equation) ∈ sourceRows by simp [sourceRows])) rfl⟩

theorem root_probe (done : Nat → Prop) :
    HeadMatches (restriction (support done)) constructors interpret root impl :=
  .cons ⟨range_root,normalCode,_,_,normalized,lo_trace done,hi_trace done⟩ .nil

theorem child_probe (done : Nat → Prop) :
    HeadMatches (restriction (support done)) constructors interpret child leaf :=
  .cons ⟨range_left,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,4⟩],rfl,.capture,.capture⟩ .nil

def rank (n : Nat) : Nat :=
  if n ≤ 2 then 2 else if 11 ≤ n ∧ n ≤ 16 then 1 else 0

theorem exact_rows : final.equations =
    sourceRows ++ [⟨1,GeneralDeclarativePairCenters326.pair (.variable 15) (.variable 16)⟩,
    ⟨15,.variant 4 (.variable 17)⟩,⟨16,.nominal 0 [.variable 9]⟩,
    ⟨6,.variable 5⟩,⟨5,.variable 17⟩] := rfl

theorem alias_rank {a b : Nat} (equal : Alias final a b) : rank a = rank b := by
  have rowRank {a b : Nat} (h : (⟨a,.variable b⟩ : Equation) ∈ final.equations) : rank a = rank b := by
    rw [exact_rows] at h
    simp only [sourceRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with x|x|x|x|x|x|x|x|x|x|x|x <;> cases x <;> rfl
  have bound {a b} (h : GeneralDeclarativeBounds319.Bound final.normal a b) : rank a = rank b := by
    induction h with
    | refl => rfl
    | constraint h =>
      change _ ∈ [PresenceNormalForm.Atom.tyLe (.var 11) (.var 15),.tyLe (.var 15) (.var 13),
        .tyLe (.var 12) (.var 16),.tyLe (.var 16) (.var 14),.tyLe (.var 3) (.var 17),
        .tyLe (.var 17) (.var 4)] at h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with x|x|x|x|x|x <;> cases x <;> rfl
    | interval h =>
      change _ ∈ [(0,1),(1,2)] at h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with x|x <;> cases x <;> rfl
    | trans _ _ x y => exact x.trans y
  induction equal with
  | bounds h _ => exact bound h
  | forward h => exact rowRank h
  | backward h => exact (rowRank h).symm
  | trans _ _ x y => exact x.trans y

theorem no_cycles : ∀ n, ¬ AliasCycle final (observed final) n := by
  apply graph_no_cycle rank (fun _ _ same => alias_rank same)
  rintro n shape child ⟨body,there,read⟩ member
  rw [exact_rows] at there
  simp only [sourceRows,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at there
  rcases there with x|x|x|x|x|x|x|x|x|x|x|x <;> cases x
  all_goals cases read
  all_goals simp [GeneralDeclarativeK2Graph321.Shape.children] at member
  all_goals first
    | (rcases member with rfl|rfl; all_goals decide +kernel)
    | (subst child; decide +kernel)

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (support done)) constructors interpret,
    fun d c => ¬HeadMatches (restriction (support done)) constructors interpret d c⟩

theorem safe (done : Nat → Prop) (d : Demand) : ¬Recurs final reg interpret (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles site cycle

end Yulang.GeneralDeclarativeNestedProbe328
