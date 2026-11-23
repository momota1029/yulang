import Yulang.GeneralDeclarativeWitnessOrderedReport358
import Yulang.GeneralDeclarativeWitnessAddressLinear356

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessActualAddress358
open GeneralDeclarativeWitnessOrderedReplay358 (Tree Forest)
open GeneralDeclarativeWitnessOrderedMeaning358 (diag diags ledger ledgerList Entry)
open GeneralDeclarativeWitnessPathOrder352 (preorder branchOrder)
open GeneralDeclarativeWitnessOrderedReport358 (Checked)
open GeneralDeclarativeWitnessTree349 (exact_report)

theorem positions {a s p d} (node : Tree a s p d) :
    (ledger node).map Entry.path = preorder p (diag node) := by
  refine @Tree.rec a s
    (fun path _ tree => (ledger tree).map Entry.path = preorder path (diag tree))
    (fun path i _ trees => (ledgerList trees).map Entry.path = branchOrder path i (diags trees))
    ?_ ?_ ?_ p d node
  · intro _ path _ later same
    rw [ledger.eq_def,diag.eq_def,preorder.eq_def]
    change path :: (ledgerList later).map Entry.path = path :: branchOrder path 0 (diags later)
    rw [same]
  · intro path i
    rw [ledgerList.eq_def,diags.eq_def,branchOrder.eq_def]
    rfl
  · intro path i d ds first rest ready prior
    rw [ledgerList.eq_def,diags.eq_def,branchOrder.eq_def,List.map_append]
    change (ledger first).map Entry.path ++ (ledgerList rest).map Entry.path =
      preorder (path ++ [i]) (diag first) ++ branchOrder path (i+1) (diags rest)
    rw [ready,prior]

theorem checked_paths {a s p d report} (run : Checked a s p d report) :
    report.writes.map Entry.path = preorder p report.report.tree := by
  rw [run.exactWrites,(exact_report run.decoded).1]
  exact positions run.proof

theorem no_duplicate_path {a s p d report} (run : Checked a s p d report) :
    (report.writes.map Entry.path).Nodup := by
  rw [checked_paths run]
  exact (GeneralDeclarativeWitnessAddressLinear356.tree_addresses _ _).1

theorem unique_entry (rows : List Entry) (addresses : (rows.map Entry.path).Nodup)
    {first last : Entry} (x : first ∈ rows) (y : last ∈ rows)
    (both : first.path = last.path) : first = last := by
  induction rows with
  | nil => cases x
  | cons head tail ih =>
    change (head.path :: tail.map Entry.path).Nodup at addresses
    have stopped := (List.nodup_cons.mp addresses).1
    have safe := (List.nodup_cons.mp addresses).2
    rcases List.mem_cons.mp x with rfl|left <;> rcases List.mem_cons.mp y with rfl|right
    · rfl
    · exact False.elim (stopped (both.symm ▸ List.mem_map_of_mem (f := Entry.path) right))
    · exact False.elim (stopped (both ▸ List.mem_map_of_mem (f := Entry.path) left))
    · exact ih safe left right

theorem unambiguous_address {a s p d report} (run : Checked a s p d report)
    {first last : Entry} (x : first ∈ report.writes) (y : last ∈ report.writes)
    (both : first.path = last.path) : first = last :=
  unique_entry _ (no_duplicate_path run) x y both

end Yulang.GeneralDeclarativeWitnessActualAddress358
