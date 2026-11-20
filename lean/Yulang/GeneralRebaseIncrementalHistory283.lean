import Yulang.GeneralRebaseDirtyHistory283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseIncrementalHistory283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (solve SafeOrder solve_outside solve_rows)
open GeneralNominalAcyclicEquations237 (Descending Coherent)
open CommonNominalFullCarrier (model)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseDirtyHistory283 (select subset safe skipped chosen_eq_of_target)
open GeneralRebaseExactHistory283 (unique equation eval_equal)

def changes (old full : List (Entry Nat)) : List (Entry Nat) :=
  select (old.map Prod.fst) full []

def update (old full : List (Entry Nat)) (cache : Assignment) : Assignment :=
  solve model (changes old full) cache

theorem rows (old full : List (Entry Nat)) (cache : Assignment) (n : Nat) :
    (update old full cache n).2 = (cache n).2 :=
  solve_rows model _ cache n

theorem exact_update {old full : List (Entry Nat)} (includes : old ⊆ full)
    (coherent : Coherent full) (descends : Descending full)
    (oldOrder : SafeOrder old) (newOrder : SafeOrder full) (base : Assignment) :
    update old full (solve model old base) = solve model full base := by
  let cache := solve model old base
  let dirty := changes old full
  let result := update old full cache
  have dirtySafe : SafeOrder dirty := safe _ _ _ newOrder
  have noWrite (n : Nat) (absent : ∀ row ∈ dirty, row.1 ≠ n) :
      result n = cache n := solve_outside model dirty cache n absent
  have rowCache (n : Nat) : (result n).2 = (cache n).2 := rows old full cache n
  change result = solve model full base
  apply unique full descends
  · intro n
    exact (rowCache n).trans
      ((solve_rows model old base n).trans (solve_rows model full base n).symm)
  · intro n absent
    rw [noWrite n (fun row member => absent row (GeneralRebaseDirtyHistory283.subset _ _ _ member))]
    exact (solve_outside model old base n (fun row member => absent row (includes member))).trans
      (solve_outside model full base n absent).symm
  · intro row present
    by_cases hit : row ∈ dirty
    · exact equation dirty dirtySafe cache row hit
    · obtain ⟨oldTarget,_,untouched⟩ := skipped _ _ _ newOrder row present hit
      obtain ⟨oldRow,oldMem,sameTarget⟩ := List.mem_map.mp oldTarget
      have sameRow : oldRow = row :=
        Prod.ext sameTarget (coherent oldRow (includes oldMem) row present sameTarget)
      have oldMem' : row ∈ old := sameRow ▸ oldMem
      rw [noWrite row.1 (fun written mem eq =>
        hit ((chosen_eq_of_target _ _ _ coherent present mem eq) ▸ mem))]
      change (solve model old base row.1).1 = row.2.eval model result
      rw [equation old oldOrder base row oldMem']
      apply eval_equal row.2 (fun n => (rowCache n).symm)
      intro n read
      symm
      apply congrArg Prod.fst
      exact noWrite n (fun write member eq => untouched write member (eq ▸ read))
  · exact fun row => equation full newOrder base row

theorem no_change {old full : List (Entry Nat)} (same : ∀ row, row ∈ full → row.1 ∈ old.map Prod.fst) :
    changes old full = [] := by
  unfold changes
  induction full with
  | nil => rfl
  | cons head tail ih =>
    have known := same head (List.mem_cons_self ..)
    have noHit : GeneralRebaseDirtyHistory283.needs (old.map Prod.fst) [] head = false := by
      simp [GeneralRebaseDirtyHistory283.needs, known]
    simp only [GeneralRebaseDirtyHistory283.select,noHit,Bool.false_eq_true,ite_false]
    exact ih (fun row mem => same row (List.mem_cons_of_mem _ mem))

end Yulang.GeneralRebaseIncrementalHistory283
