import Yulang.GeneralDeclarativeCovariantState326
import Yulang.GeneralDeclarativeRank321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCovariantProbe326
open GeneralDeclarativePairDecl326
open GeneralDeclarativeCovariantState326
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
    Trace (restriction (support2 done)) .lower 0 normalCode [⟨0,.lower,3⟩,⟨1,.lower,3⟩] :=
  .primitive (args := [3,3]) (alias_refl _) (authorized done List.mem_cons_self) (.cons .capture (.cons .capture .nil))

theorem upper_trace (done : Nat → Prop) :
    Trace (restriction (support2 done)) .upper 2 normalCode [⟨0,.upper,4⟩,⟨1,.upper,4⟩] :=
  .primitive (args := [4,4]) (alias_refl _) (authorized done (show (⟨2,hi⟩ : Equation) ∈ sourceRows by simp [sourceRows])) (.cons .capture (.cons .capture .nil))

theorem root_ready (done : Nat → Prop) : Ready (support2 done) root := by
  intro a included
  cases List.mem_singleton.mp included
  exact ⟨_,knows_row (authorized done (show (⟨0,lo⟩ : Equation) ∈ sourceRows from List.mem_cons_self)) rfl⟩

theorem child_ready (done : Nat → Prop) : Ready (support2 done) child := by
  intro a included
  cases List.mem_singleton.mp included
  exact ⟨_,knows_row (authorized done (show (⟨3,.primitive (.scalar .int) []⟩ : Equation) ∈ sourceRows
    by simp [sourceRows])) rfl⟩

theorem root_probe (done : Nat → Prop) :
    HeadMatches (restriction (support2 done)) constructors interpret root impl :=
  .cons ⟨root_range,normalCode,_,_,normalized,lower_trace done,upper_trace done⟩ .nil

theorem child_probe (done : Nat → Prop) :
    HeadMatches (restriction (support2 done)) constructors interpret child leaf :=
  .cons ⟨left_range,.variable 0,[⟨0,.lower,3⟩],[⟨0,.upper,4⟩],rfl,.capture,.capture⟩ .nil

def rank (n : Nat) : Nat := if n = 11 then 2 else if n ≤ 2 then 1 else 0

theorem alias_rank {a b : Nat} (e : Alias final a b) : rank a = rank b := by
  have rowRank {a b : Nat} (h : (⟨a,.variable b⟩ : Equation) ∈ final.equations) : rank a = rank b := by
    simp only [final,middle,appendFacts,sourceRows,List.cons_append,List.nil_append,List.mem_cons,
      List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h|h|h|h <;> cases h <;> rfl
  have range {a b} (h : GeneralDeclarativeBounds319.Bound final.normal a b) : rank a = rank b := by
    induction h with
    | refl => rfl
    | constraint nil => cases nil
    | interval h =>
      change _ ∈ intervals at h
      simp only [intervals,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with h|h|h|h|h|h <;> cases h <;> rfl
    | trans _ _ x y => exact x.trans y
  induction e with
  | bounds h _ => exact range h
  | forward h => exact rowRank h
  | backward h => exact (rowRank h).symm
  | trans _ _ x y => exact x.trans y

theorem no_cycles : ∀ n, ¬ AliasCycle final (observed final) n := by
  apply graph_no_cycle rank (fun _ _ same => alias_rank same)
  rintro n target child ⟨body,there,shape⟩ member
  simp only [final,middle,appendFacts,sourceRows,List.cons_append,List.nil_append,List.mem_cons,
    List.not_mem_nil,or_false] at there
  rcases there with h|h|h|h|h|h|h <;> cases h
  all_goals cases shape
  all_goals simp [GeneralDeclarativeK2Graph321.Shape.children] at member
  all_goals first
    | (rcases member with rfl|rfl; all_goals decide +kernel)
    | (subst child; decide +kernel)

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (support2 done)) constructors interpret,
   fun d decl => ¬ HeadMatches (restriction (support2 done)) constructors interpret d decl⟩

theorem safe (done : Nat → Prop) (d : Demand) :
    ¬ Recurs final reg interpret (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycles arg.lower cycle
  · exact no_cycles site cycle

end Yulang.GeneralDeclarativeCovariantProbe326
