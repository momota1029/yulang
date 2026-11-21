import Yulang.GeneralDeclarativeAggregateReads324

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeAggregateProbe324
open GeneralDeclarativeAggregateFixture324
open GeneralDeclarativeAggregateReads324 (a_bounds b_bounds)
open GeneralDeclarativeRepeatedSource323 (a b eqs nominalCode scalar pat goal parent child registry)
open GeneralDeclarativeExampleSource320 (interp point)
open GeneralDeclarativeRepeatedResolve323 (level)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeBounds319 (Bound)
open GeneralDeclarativeLowerKnown321 (Alias Ready alias_refl knows_row)
open GeneralDeclarativeGraphRows321 (observed)
open GeneralDeclarativeK2Alias321 (AliasCycle)
open GeneralDeclarativeRank321 (graph_no_cycle)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativePriority321 (Candidates Recurs)
open GeneralDeclarativeEndpointProbe321 (HeadMatches)
open GeneralDeclarativeOrigins321 (restriction)
open Core.PresenceGeneration (TyTerm)
open PresenceNormalForm (Atom)
open CommonRoleOutermostResolver (All₂)

abbrev extraAtoms : List (Atom Nat) :=
  [.tyLe (.var 3) (.var 3),.tyLe (.var 3) (.var 3),
   .tyLe (.var 7) (.var 3),.tyLe (.var 3) (.var 7),
   .tyLe (.var 33) (.union (.var 3) (.var 7)),
   .tyLe (.union (.var 3) (.var 7)) (.var 33),
   .tyLe (.var 34) (.inter (.var 3) (.var 7)),
   .tyLe (.inter (.var 3) (.var 7)) (.var 34),
   .tyLe (.var 33) (.var 3),.tyLe (.var 3) (.var 34)]

theorem ordinary_exact : newState.normal.ordinary = extraAtoms := rfl

theorem bound_level {x y} (h : Bound newState.normal x y) : level x = level y := by
  induction h with
  | refl => rfl
  | interval registered =>
    change _ ∈ [(0,1),(1,2),(10,11),(11,12)] at registered
    simp only [List.mem_cons,List.not_mem_nil,or_false] at registered
    rcases registered with h|h|h|h <;> cases h <;> rfl
  | constraint registered =>
    rw [ordinary_exact] at registered
    simp only [extraAtoms,List.mem_cons,List.not_mem_nil,or_false] at registered
    rcases registered with h|h|h|h|h|h|h|h|h|h <;> cases h <;> rfl
  | trans _ _ x y => exact x.trans y

abbrev extraEqs : List Equation := eqs ++ [⟨33,.variable 3⟩,⟨34,.variable 3⟩]

theorem row_level {x y} (found : (⟨x,.variable y⟩ : Equation) ∈ newState.equations) : level x = level y := by
  change _ ∈ extraEqs at found
  simp only [extraEqs,eqs,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at found
  rcases found with h|h|h|h|h|h|h|h|h|h <;> cases h <;> rfl

theorem no_cycle : ∀ n, ¬AliasCycle newState (observed newState) n := by
  apply graph_no_cycle level
  · intro x y same
    induction same with
    | bounds h _ => exact bound_level h
    | forward h => exact row_level h
    | backward h => exact (row_level h).symm
    | trans _ _ x y => exact x.trans y
  · rintro n head deeper ⟨form,row,compiled⟩ next
    change _ ∈ extraEqs at row
    simp only [extraEqs,eqs,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at row
    rcases row with h|h|h|h|h|h|h|h|h|h <;> cases h
    all_goals cases compiled
    all_goals first
      | (cases List.mem_singleton.mp next; decide +kernel)
      | cases next

theorem parent_ready (completed : Nat → Prop) : Ready (support completed) goal := by
  intro arg known
  rcases List.mem_cons.mp known with rfl|later
  · exact ⟨_,knows_row (supported_row completed (old_rows (show (⟨0,nominalCode 3⟩ : Equation) ∈ eqs by simp [eqs]))) rfl⟩
  · cases List.mem_singleton.mp later
    exact ⟨_,knows_row (supported_row completed (old_rows (show (⟨10,nominalCode 7⟩ : Equation) ∈ eqs by simp [eqs]))) rfl⟩

theorem parent_matches (completed : Nat → Prop) :
    HeadMatches (restriction (support completed)) registry.constructors interp goal parent := by
  let code : GeneralNominalCenteredHeadMatExpressions.Expr := .nominal 0 [.variable 0]
  refine .cons ⟨a_bounds,code,[⟨0,.actual,3⟩],[⟨0,.actual,4⟩],rfl,?_,?_⟩
    (.cons ⟨b_bounds,code,[⟨0,.actual,7⟩],[⟨0,.actual,8⟩],rfl,?_,?_⟩ .nil)
  · exact .nominal (args := [3]) (alias_refl _) (supported_row completed (old_rows (by simp [eqs]))) (.cons .capture .nil)
  · exact .nominal (args := [4]) (alias_refl _) (supported_row completed (old_rows (by simp [eqs]))) (.cons .capture .nil)
  · exact .nominal (args := [7]) (alias_refl _) (supported_row completed (old_rows (by simp [eqs]))) (.cons .capture .nil)
  · exact .nominal (args := [8]) (alias_refl _) (supported_row completed (old_rows (by simp [eqs]))) (.cons .capture .nil)

theorem child_matches (completed : Nat → Prop) :
    HeadMatches (restriction (support completed)) registry.constructors interp emitted child :=
  .cons ⟨bounds,.variable 0,[⟨0,.lower,33⟩],[⟨0,.upper,34⟩],rfl,.capture,.capture⟩ .nil

def tests (completed : Nat → Prop) : Candidates :=
  ⟨HeadMatches (restriction (support completed)) registry.constructors interp,
   fun d decl => ¬HeadMatches (restriction (support completed)) registry.constructors interp d decl⟩

theorem no_recurs (completed : Nat → Prop) (d) : ¬Recurs newState registry interp (tests completed) d := by
  rintro (⟨arg,_,cycle⟩|⟨impl,_,i,arg,pat,code,_,_,_,place,_,cycle⟩)
  · exact no_cycle arg.lower cycle
  · exact no_cycle place cycle

end Yulang.GeneralDeclarativeAggregateProbe324
