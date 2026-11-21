import Yulang.GeneralDeclarativeCompoundState325

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompoundProbe325
open GeneralDeclarativeCompoundDecl325
open GeneralDeclarativeCompoundState325
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
open GeneralNominalMaterialization (Mode)

theorem inner_trace (done : Nat → Prop) :
    Trace (restriction (support2 done)) .actual 7 innerCode [⟨0,.actual,3⟩] :=
  .nominal (args := [3]) (alias_refl _) (authorized done (by simp [ordinaryRows])) (.cons .capture .nil)

theorem lower_trace (done : Nat → Prop) :
    Trace (restriction (support2 done)) .lower 0 outerCode [⟨0,.actual,3⟩] :=
  .nominal (args := [7]) (alias_refl _) (authorized done (by simp [ordinaryRows]))
    (.cons (inner_trace done) .nil)

theorem upper_trace (done : Nat → Prop) :
    Trace (restriction (support2 done)) .upper 2 outerCode [⟨0,.actual,3⟩] :=
  .nominal (args := [7]) (alias_refl _) (authorized done (by simp [ordinaryRows]))
    (.cons (inner_trace done) .nil)

theorem root_ready (done : Nat → Prop) : Ready (support2 done) demand := by
  intro arg member
  cases List.mem_singleton.mp member
  exact ⟨_,knows_row (authorized done (show (⟨0,openRoot⟩ : Equation) ∈ ordinaryRows by simp [ordinaryRows])) rfl⟩

theorem child_ready (done : Nat → Prop) : Ready (support2 done) call := by
  intro arg member
  cases List.mem_singleton.mp member
  have link : Alias (restriction (support2 done)) 8 7 :=
    .forward (authorized done (show (⟨8,.variable 7⟩ : Equation) ∈ ordinaryRows by simp [ordinaryRows]))
  exact ⟨.nominal 0 1,⟨⟨7,openChild⟩,authorized done (by simp [ordinaryRows]),link,rfl⟩⟩

theorem root_probe (done : Nat → Prop) :
    HeadMatches (restriction (support2 done)) constructors interpret demand impl :=
  .cons ⟨root_bounds,outerCode,_,_,outer_trans,lower_trace done,upper_trace done⟩ .nil

theorem child_probe (done : Nat → Prop) :
    HeadMatches (restriction (support2 done)) constructors interpret call leaf :=
  .cons ⟨child_bounds,.variable 0,[⟨0,.lower,8⟩],[⟨0,.upper,10⟩],rfl,.capture,.capture⟩ .nil

def rank (n : Nat) : Nat := if n ≤ 2 then 2 else if n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 ∨ n = 10 then 1 else 0

theorem alias_rank {a b : Nat} (same : Alias final a b) : rank a = rank b := by
  have rowRank {a b : Nat} (h : (⟨a,.variable b⟩ : Equation) ∈ final.equations) : rank a = rank b := by
    simp only [final,middle,GeneralDeclarativeEntailment320.appendFacts,ordinaryRows,List.cons_append,
      List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with h|h|h|h|h|h|h|h|h <;> cases h <;> rfl
  have bound {a b : Nat} (h : GeneralDeclarativeBounds319.Bound final.normal a b) : rank a = rank b := by
    induction h with
    | refl => rfl
    | constraint empty => cases empty
    | interval has =>
      change _ ∈ [(0,1),(1,2),(8,9),(9,10)] at has
      simp only [List.mem_cons,List.not_mem_nil,or_false] at has
      rcases has with h|h|h|h <;> cases h <;> rfl
    | trans _ _ x y => exact x.trans y
  induction same with
  | bounds first _ => exact bound first
  | forward h => exact rowRank h
  | backward h => exact (rowRank h).symm
  | trans _ _ x y => exact x.trans y

theorem no_cycle : ∀ n, ¬AliasCycle final (observed final) n := by
  apply graph_no_cycle rank (fun _ _ same => alias_rank same)
  rintro n target child ⟨body,there,shape⟩ member
  simp only [final,middle,GeneralDeclarativeEntailment320.appendFacts,ordinaryRows,List.cons_append,
    List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at there
  rcases there with h|h|h|h|h|h|h|h|h <;> cases h
  all_goals cases shape
  all_goals first
    | (have same : child = 7 := List.mem_singleton.mp member; subst child; decide +kernel)
    | (have same : child = 3 := List.mem_singleton.mp member; subst child; decide +kernel)
    | cases member

def tests (done : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (support2 done)) constructors interpret,
   fun d impl => ¬HeadMatches (restriction (support2 done)) constructors interpret d impl⟩

theorem safe (done : Nat → Prop) (d : Demand) :
    ¬Recurs final reg interpret (tests done) d := by
  rintro (⟨arg,_,cycle⟩|⟨_,_,_,_,_,_,_,_,_,site,_,cycle⟩)
  · exact no_cycle arg.lower cycle
  · exact no_cycle site cycle

end Yulang.GeneralDeclarativeCompoundProbe325
