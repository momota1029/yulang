import Yulang.GeneralDeclarativeWitnessRecursiveSource356
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessMixedPathLedger356
open GeneralDeclarativeWitnessRecursiveMixed356 (Tree Branches)
open GeneralDeclarativeWitnessRecursiveTree356 (view views)
open GeneralDeclarativeWitnessMixedLedger356 (Entry entries entriesBranches rootEntry ordinaryEntry)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessPathOrder352 (preorder branchOrder)
open GeneralDeclarativeHead320 (State)

theorem path_map (rows : List Fixed) :
    (rows.map ordinaryEntry).map Entry.path = rows.map Fixed.path := by
  induction rows with
  | nil => rfl
  | cons h t ih =>
    change h.path :: (t.map ordinaryEntry).map Entry.path = h.path :: t.map Fixed.path
    rw [ih]

theorem exact_paths {s : State} {e p} (t : @Tree s e p) :
    (entries t).map Entry.path = preorder p.origin.path (view t) := by
  refine @Tree.rec s e
    (fun p t => (entries t).map Entry.path = preorder p.origin.path (view t))
    (fun p i _ b => (entriesBranches b).map Entry.path = branchOrder p.origin.path i (views b))
    ?_ ?_ ?_ ?_ p t
  · intro p allowed c branches
    rw [entries.eq_def,view.eq_def,preorder.eq_def]
    change p.origin.path :: (entriesBranches c).map Entry.path =
       p.origin.path :: branchOrder p.origin.path 0 (views c)
    rw [branches]
  · intro i p
    rw [entriesBranches.eq_def,views.eq_def,branchOrder.eq_def]
    rfl
  · intro i d ds p a w h child rest first later
    rw [entriesBranches.eq_def,views.eq_def,branchOrder.eq_def,List.map_append]
    have loc : h.node.origin.path = p.origin.path ++ [i] := h.path
    change _ ++ _ = preorder (p.origin.path ++ [i]) (view child) ++ branchOrder p.origin.path (i+1) (views rest)
    rw [first,later,loc]
  · intro i d ds p r route old tail later
    rw [entriesBranches.eq_def,views.eq_def,branchOrder.eq_def,List.map_append,path_map,later,old.paths]

theorem report_paths {p s w} (checked : GeneralDeclarativeWitnessRecursiveSource356.Found p s w) :
    w.report.outputs.map Entry.path =
      preorder p.location.path w.report.answer.tree := by
  have signed := GeneralDeclarativeWitnessTree349.exact_report checked.replay.returned
  rw [checked.replay.exactOutputs,signed.1,← checked.path]
  exact exact_paths checked.replay.proof

end Yulang.GeneralDeclarativeWitnessMixedPathLedger356
