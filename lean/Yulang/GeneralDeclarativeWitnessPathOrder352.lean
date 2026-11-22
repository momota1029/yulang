import Yulang.GeneralDeclarativeWitnessMixedCompletion352

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessPathOrder352
open CommonRoleOutermostResolver (Tree)
open GeneralDeclarativeDemand320 (Demand)
open GeneralDeclarativeWitnessForest350 (Fixed)
open GeneralDeclarativeWitnessMixedForest352 (Problem Global Code Codes Replayed ReplayedList read replayTree replayList)

mutual
def preorder (prefixPath : List Nat) : Tree → List (List Nat)
  | .selected _ children => prefixPath :: branchOrder prefixPath 0 children
  | _ => [prefixPath]
termination_by t => sizeOf t

def branchOrder (prefixPath : List Nat) (index : Nat) : List Tree → List (List Nat)
  | [] => []
  | child::rest => preorder (prefixPath ++ [index]) child ++ branchOrder prefixPath (index+1) rest
termination_by ts => sizeOf ts
end

variable {p : Problem} {g : Global p}

mutual
theorem exact_tree {pre : List Nat} {d : Demand} (code : Code) {res : Replayed g d}
    (run : replayTree g pre d code = some res) :
    res.fixed.map Fixed.path = preorder pre res.tree := by
  cases code with
  | node branch kids =>
    rw [replayTree.eq_def] at run
    cases current : read g pre d branch with
    | none => simp [current] at run
    | some head =>
      simp only [Option.bind_eq_bind,Option.pure_def,current,Option.bind_some] at run
      cases below : replayList g pre 0 head.kids kids with
      | none => simp [below] at run
      | some tail =>
        simp only [below,Option.bind_some] at run
        cases Option.some.inj run
        change pre :: tail.fixed.map Fixed.path = preorder pre (.selected head.decl.id tail.trees)
        rw [preorder.eq_def,exact_list kids below]
termination_by sizeOf code

theorem exact_list {pre : List Nat} {idx : Nat} {ds : List Demand} (code : Codes) {res : ReplayedList g ds}
    (run : replayList g pre idx ds code = some res) :
    res.fixed.map Fixed.path = branchOrder pre idx res.trees := by
  cases code with
  | nil =>
    cases ds with
    | nil =>
      rw [replayList.eq_def] at run
      cases Option.some.inj run
      simp only [branchOrder.eq_def,List.map_nil]
    | cons first last => simp [replayList.eq_def] at run
  | cons branch kids =>
    cases ds with
    | nil => simp [replayList.eq_def] at run
    | cons d more =>
      rw [replayList.eq_def] at run
      cases current : replayTree g (pre ++ [idx]) d branch with
      | none => simp [current] at run
      | some head =>
        simp only [Option.bind_eq_bind,Option.pure_def,current,Option.bind_some] at run
        cases below : replayList g pre (idx+1) more kids with
        | none => simp [below] at run
        | some tail =>
          simp only [below,Option.bind_some] at run
          cases Option.some.inj run
          change (head.fixed ++ tail.fixed).map Fixed.path = branchOrder pre idx (head.tree :: tail.trees)
          rw [branchOrder.eq_def,List.map_append,exact_tree branch current,exact_list kids below]
termination_by sizeOf code
end

end Yulang.GeneralDeclarativeWitnessPathOrder352
