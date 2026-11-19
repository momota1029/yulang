import Yulang.GeneralRebaseOptionalDelta283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCrossProbe283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (solve SafeOrder solve_outside solve_rows)
open GeneralNominalAcyclicEquations237 (Descending Coherent)
open CommonNominalFullCarrier (model)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseDirtyHistory283 (select subset safe skipped chosen_eq_of_target)
open GeneralRebaseExactHistory283 (unique equation eval_equal)

def Sparse (first last : Assignment) (dirty : List Nat) : Prop :=
  (∀ n, (first n).2 = (last n).2) ∧
  ∀ n, n ∉ dirty → (first n).1 = (last n).1

def blend (old : List (Entry Nat)) (cached replace : Assignment) (n : Nat) :=
  if n ∈ old.map Prod.fst then cached n else replace n

def refresh (old full : List (Entry Nat)) (dirty : List Nat) (cached replace : Assignment) :=
  solve model (select (old.map Prod.fst) full dirty) (blend old cached replace)

theorem unchanged_on_blend (old : List (Entry Nat)) {before after : Assignment} {boundary : List Nat}
    (sparse : Sparse before after boundary) (n : Nat) (stable : n ∉ boundary) :
    blend old (solve model old before) after n = solve model old before n := by
  unfold blend
  by_cases used : n ∈ old.map Prod.fst
  · simp only [used,ite_true]
  · rw [ite_eq_right used,solve_outside model old before n]
    · exact Prod.ext (sparse.2 n stable).symm (sparse.1 n).symm
    · intro row member same
      exact used (List.mem_map.mpr ⟨row,member,same⟩)

theorem rows (old full : List (Entry Nat)) (dirty : List Nat) {before after : Assignment}
    (sparse : Sparse before after dirty) (n : Nat) :
    (refresh old full dirty (solve model old before) after n).2 = (after n).2 := by
  unfold refresh
  rw [solve_rows]
  unfold blend
  by_cases used : n ∈ old.map Prod.fst
  · rw [ite_eq_left used,solve_rows]
    exact sparse.1 n
  · rw [ite_eq_right used]

theorem exact_refresh {old full : List (Entry Nat)} (includes : old ⊆ full)
    (coherent : Coherent full) (descend : Descending full)
    (oldOrder : SafeOrder old) (newOrder : SafeOrder full) {before after : Assignment}
    {boundary : List Nat} (sparse : Sparse before after boundary) :
    refresh old full boundary (solve model old before) after = solve model full after := by
  let cache := solve model old before
  let dirty := select (old.map Prod.fst) full boundary
  let start := blend old cache after
  let result := refresh old full boundary cache after
  have dirtySafe : SafeOrder dirty := safe _ _ _ newOrder
  have noWrite (n : Nat) (absent : ∀ row ∈ dirty, row.1 ≠ n) :
      result n = start n := solve_outside model dirty start n absent
  have rowResult (n : Nat) : (result n).2 = (after n).2 := rows old full boundary sparse n
  change result = solve model full after
  apply unique full descend
  · intro n; exact (rowResult n).trans (solve_rows model full after n).symm
  · intro n absent
    rw [noWrite n (fun row member => absent row (GeneralRebaseDirtyHistory283.subset _ _ _ member))]
    have none : ¬ n ∈ old.map Prod.fst := by
      intro seen
      obtain ⟨row,listed,hit⟩ := List.mem_map.mp seen
      exact absent row (includes listed) hit
    change (if n ∈ old.map Prod.fst then cache n else after n) = solve model full after n
    rw [ite_eq_right none,solve_outside model full after n absent]
  · intro row present
    by_cases evaluated : row ∈ dirty
    · exact equation dirty dirtySafe start row evaluated
    · obtain ⟨oldTarget,cleanBoundary,cleanWrites⟩ := skipped _ _ _ newOrder row present evaluated
      obtain ⟨oldRow,oldMem,sameTarget⟩ := List.mem_map.mp oldTarget
      have prior : row ∈ old :=
        (Prod.ext sameTarget (coherent oldRow (includes oldMem) row present sameTarget) : oldRow = row) ▸ oldMem
      have noTarget : ∀ other ∈ dirty, other.1 ≠ row.1 :=
        fun other member hit => evaluated ((chosen_eq_of_target _ _ _ coherent present member hit) ▸ member)
      rw [noWrite row.1 noTarget]
      change (if row.1 ∈ old.map Prod.fst then cache row.1 else after row.1).1 = _
      rw [ite_eq_left oldTarget]
      change (solve model old before row.1).1 = row.2.eval model result
      rw [equation old oldOrder before row prior]
      apply eval_equal row.2
      · intro n; exact (solve_rows model old before n).trans ((sparse.1 n).trans (rowResult n).symm)
      · intro n read
        have unchanged := noWrite n (fun other used same => cleanWrites other used (same ▸ read))
        exact congrArg Prod.fst ((unchanged.trans (unchanged_on_blend old sparse n (cleanBoundary n read))).symm)
  · exact fun row => equation full newOrder after row

end Yulang.GeneralRebaseCrossProbe283
