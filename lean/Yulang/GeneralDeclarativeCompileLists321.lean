import Yulang.GeneralDeclarativeEntailment320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCompileLists321
open GeneralDeclarativeEntailment320 (Entails)
open GeneralDeclarativeHead320 (State Equation)
open GeneralDeclarativeBatch320 (zipFacts collect)
open CommonRoleOutermostResolver (All₂)

def Result (s : State) (compiled : Option (List Equation)) : Prop :=
  ∃ facts, compiled = some facts ∧ ∀ row ∈ facts, Entails s row

theorem none_not_result : ¬Result s none := by rintro ⟨_,bad,_⟩; cases bad

theorem zip_result {s : State} {f : α → β → Option (List Equation)} {as : List α} {bs : List β}
    (generated : All₂ (fun a b => Result s (f a b)) as bs) : Result s (zipFacts f as bs) := by
  induction generated with
  | nil =>
    exact ⟨[],rfl,fun _ h => by cases h⟩
  | cons first _ ih =>
    obtain ⟨before,compOne,trueOne⟩ := first
    obtain ⟨after,compMany,trueMany⟩ := ih
    refine ⟨before ++ after,by simp [zipFacts,compOne,compMany],?_⟩
    intro row h
    exact (List.mem_append.mp h).elim (trueOne row) (trueMany row)

theorem collect_result {s : State} {f : α → Option (List Equation)} {xs : List α}
    (generated : ∀ x ∈ xs, Result s (f x)) : Result s (collect f xs) := by
  induction xs with
  | nil =>
    exact ⟨[],rfl,fun _ h => by cases h⟩
  | cons one more ih =>
    obtain ⟨before,compOne,trueOne⟩ := generated one List.mem_cons_self
    obtain ⟨after,compMany,trueMany⟩ := ih (fun x h => generated x (List.mem_cons_of_mem _ h))
    refine ⟨before ++ after,by simp [collect,compOne,compMany],?_⟩
    intro row h
    exact (List.mem_append.mp h).elim (trueOne row) (trueMany row)

end Yulang.GeneralDeclarativeCompileLists321
