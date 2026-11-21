import Yulang.GeneralFiniteColoredTable306

namespace Yulang.GeneralFiniteColoredEarlyStop306
open GeneralFiniteColoredTable306 (advance table compile)
open GeneralFiniteColoredExact306 (limit)
variable {α β : Type} [DecidableEq α] [DecidableEq β]

def run (edges : α → List α) (observe : α → β) (nodes : List α) :
    Nat → List (α × α) → List (α × α)
  | 0,memo => memo
  | fuel+1,memo =>
    let next := advance edges observe nodes memo
    if next = memo then memo else run edges observe nodes fuel next

theorem stays {edges : α → List α} {observe : α → β} {nodes : List α} {start : Nat}
    (same : table edges observe nodes (start+1) = table edges observe nodes start) (later : Nat) :
    table edges observe nodes (start+later) = table edges observe nodes start := by
  induction later with
  | zero => rfl
  | succ i ih =>
    change advance edges observe nodes (table edges observe nodes (start+i)) = _
    rw [ih]
    exact same

theorem exact_run (edges : α → List α) (observe : α → β) (nodes : List α) (budget start : Nat) :
    run edges observe nodes budget (table edges observe nodes start) =
      table edges observe nodes (start+budget) := by
  induction budget generalizing start with
  | zero => rfl
  | succ b ih =>
    change (if table edges observe nodes (start+1) = table edges observe nodes start
      then table edges observe nodes start
      else run edges observe nodes b (table edges observe nodes (start+1))) = _
    split
    · rename_i yes
      exact (stays yes (b+1)).symm
    · have walked := ih (start+1)
      rw [Nat.add_right_comm start 1 b] at walked
      exact walked

def fastCompile (edges : α → List α) (observe : α → β) (nodes : List α) : List (α × α) :=
  run edges observe nodes (limit nodes) (table edges observe nodes 0)

theorem exact_fast (edges : α → List α) (observe : α → β) (nodes : List α) :
    fastCompile edges observe nodes = compile edges observe nodes := by
  unfold fastCompile compile
  rw [exact_run,Nat.zero_add]

end Yulang.GeneralFiniteColoredEarlyStop306
