import Yulang.GeneralFiniteColoredScore306

namespace Yulang.GeneralFiniteColoredExact306
open GeneralFiniteColoredRounds306
open GeneralFiniteColoredScore306 (pairs score strictly_drops fixedCheck fixed_exact)
variable {α β : Type} [DecidableEq β]

def limit (nodes : List α) : Nat := (pairs nodes).length

theorem bounded_stationary (edges : α → List α) (observe : α → β) (nodes : List α) :
    ∃ n ≤ limit nodes, Stationary edges observe nodes n := by
  apply Classical.byContradiction
  intro none
  have falling (i : Nat) (bound : i ≤ limit nodes) : score edges observe nodes (i+1) < score edges observe nodes i :=
    strictly_drops (fun stable => none ⟨i,bound,stable⟩)
  have budget (k : Nat) (below : k ≤ limit nodes + 1) :
      score edges observe nodes k + k ≤ score edges observe nodes 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      have prior := ih (by omega)
      have less := falling k (by omega)
      omega
  have finished := budget (limit nodes + 1) (Nat.le_refl _)
  have finite : score edges observe nodes 0 ≤ limit nodes := List.countP_le_length
  omega

theorem stationary_monotone {edges : α → List α} {observe : α → β} {nodes : List α} {n k : Nat}
    (closed : Closed edges nodes) (early : Stationary edges observe nodes n) (late : n ≤ k) :
    Stationary edges observe nodes k := by
  induction late with
  | refl => exact early
  | step _ ih => exact stable_propagates closed ih

def analyze (edges : α → List α) (observe : α → β) (nodes : List α) (x y : α) : Bool :=
  rounds edges observe (limit nodes) x y

theorem limit_stationary (edges : α → List α) (observe : α → β) (nodes : List α)
    (closed : Closed edges nodes) : Stationary edges observe nodes (limit nodes) := by
  obtain ⟨n,bound,stable⟩ := bounded_stationary edges observe nodes
  exact stationary_monotone closed stable bound

theorem sound (edges : α → List α) (observe : α → β) (nodes : List α) (closed : Closed edges nodes) :
    On edges observe nodes (fun x y => analyze edges observe nodes x y = true) :=
  stable_sound (limit_stationary edges observe nodes closed)

theorem exact_checked {edges : α → List α} {observe : α → β} {nodes : List α}
    (closed : Closed edges nodes) {x y : α} (xm : x ∈ nodes) (ym : y ∈ nodes) :
    analyze edges observe nodes x y = true ↔
      ∃ rel, On edges observe nodes rel ∧ rel x y :=
  ⟨fun h => ⟨_,sound edges observe nodes closed,h⟩,
    fun ⟨_,valid,h⟩ => upper closed valid (limit nodes) xm ym h⟩

end Yulang.GeneralFiniteColoredExact306
