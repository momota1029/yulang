import Yulang.GeneralDeclarativeOpaqueFixture328
import Yulang.GeneralDeclarativeRank321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOpaqueFixtureProbe328
open GeneralDeclarativePairDecl326 (root impl reg interpret normalCode normalized)
open GeneralDeclarativeOpaqueFixture328
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
open GeneralDeclarativeEntailment320 (appendFacts)

theorem lower_trace (done : Nat → Prop) :
    Trace (restriction (support done)) .lower 0 normalCode [⟨0,.lower,3⟩,⟨1,.lower,3⟩] :=
  .primitive (args := [3,3]) (alias_refl _) (authorized done List.mem_cons_self) (.cons .capture (.cons .capture .nil))

theorem upper_trace (done : Nat → Prop) :
    Trace (restriction (support done)) .upper 2 normalCode [⟨0,.upper,4⟩,⟨1,.upper,4⟩] :=
  .primitive (args := [4,4]) (alias_refl _) (authorized done (show (⟨2,GeneralDeclarativeOpaqueIntervals328.high endpoints⟩ : Equation) ∈ oldRows by simp [oldRows])) (.cons .capture (.cons .capture .nil))

theorem root_ready (done : Nat → Prop) : Ready (support done) root := by
  intro a included
  cases List.mem_singleton.mp included
  exact ⟨_,knows_row (authorized done (show (⟨0,GeneralDeclarativeOpaqueIntervals328.low endpoints⟩ : Equation) ∈ oldRows from List.mem_cons_self)) rfl⟩

theorem child_ready (done : Nat → Prop) : Ready (support done) child := by
  intro a included
  cases List.mem_singleton.mp included
  exact ⟨_,knows_row (authorized done (show (⟨3,.primitive (.scalar .int) []⟩ : Equation) ∈ oldRows
    by simp [oldRows])) rfl⟩

theorem root_probe (done : Nat → Prop) :
    HeadMatches (restriction (support done)) constructors interpret root impl :=
  .cons ⟨range_root,normalCode,_,_,normalized,lower_trace done,upper_trace done⟩ .nil

theorem child_probe (done : Nat → Prop) :
    HeadMatches (restriction (support done)) constructors interpret child leaf :=
  .cons ⟨range_left,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,4⟩],rfl,.capture,.capture⟩ .nil

def rank (n : Nat) : Nat := if n ≤ 2 then 1 else 0

theorem exact_rows : final.equations =
    [⟨0,GeneralDeclarativeOpaqueIntervals328.low endpoints⟩,
     ⟨2,GeneralDeclarativeOpaqueIntervals328.high endpoints⟩,scalar,
     ⟨1,GeneralDeclarativePairCenters326.pair (.variable 7) (.variable 8)⟩,
     ⟨6,.variable 5⟩,⟨5,.variable 7⟩] := rfl

theorem alias_rank {a b : Nat} (e : Alias final a b) : rank a = rank b := by
  have rowRank {a b : Nat} (h : (⟨a,.variable b⟩ : Equation) ∈ final.equations) : rank a = rank b := by
    rw [exact_rows] at h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with each|each|each|each|each|each <;> cases each <;> rfl
  have range {a b} (h : GeneralDeclarativeBounds319.Bound final.normal a b) : rank a = rank b := by
    induction h with
    | refl => rfl
    | constraint h =>
      change _ ∈ [PresenceNormalForm.Atom.tyLe (.var 3) (.var 7),.tyLe (.var 7) (.var 4),
        .tyLe (.var 3) (.var 8),.tyLe (.var 8) (.var 4)] at h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with x|x|x|x <;> cases x <;> rfl
    | interval h =>
      change _ ∈ [(0,1),(1,2)] at h
      simp only [List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with x|x <;> cases x <;> rfl
    | trans _ _ x y => exact x.trans y
  induction e with
  | bounds h _ => exact range h
  | forward h => exact rowRank h
  | backward h => exact (rowRank h).symm
  | trans _ _ x y => exact x.trans y

theorem no_cycles : ∀ n, ¬ AliasCycle final (observed final) n := by
  apply graph_no_cycle rank (fun _ _ same => alias_rank same)
  rintro n target child ⟨body,there,shape⟩ member
  rw [exact_rows] at there
  simp only [List.mem_cons,List.not_mem_nil,or_false] at there
  rcases there with h|h|h|h|h|h <;> cases h
  all_goals cases shape
  all_goals simp [GeneralDeclarativeK2Graph321.Shape.children] at member
  all_goals first
    | (rcases member with rfl|rfl; all_goals decide +kernel)
    | (subst child; decide +kernel)

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (support done)) constructors interpret,
   fun d decl => ¬ HeadMatches (restriction (support done)) constructors interpret d decl⟩

theorem safe (done : Nat → Prop) (d : Demand) :
    ¬ Recurs final reg interpret (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles site cycle

end Yulang.GeneralDeclarativeOpaqueFixtureProbe328
