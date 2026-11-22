import Yulang.GeneralDeclarativeWitnessRecordNodes350

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessForestEngine350
open GeneralDeclarativeWitnessForest350 (ProblemTree Global Node Code Codes Replayed ReplayedList extendSidecar)
open GeneralDeclarativeWitnessRecordReplay350 (Wire)
open GeneralDeclarativeDemand320 (Demand)

def assign (p : ProblemTree) (env : Global p) := List Nat → (d : Demand) → Wire → Option (Node env d)

mutual
/-- The authoritative child inputs are exactly those emitted by the
compiler in sequence. The witness tree carries no replacement demands. -/
def replayTree {p : ProblemTree} (env : Global p) (reader : assign p env) (path : List Nat) (d : Demand) :
    Code → Option (Replayed env d)
  | .node layoutHere child => do
    let head ← reader path d layoutHere
    let tail ← replayList env reader path 0 head.kids child
    pure ⟨.selected head.decl.id tail.trees,head.sidecar ++ tail.sidecar,
      (fun b covers => .selected (.whole (extendSidecar head.selection
        (fun _ h => covers (List.mem_append_left _ h))))
        (tail.proof b (fun _ h => covers (List.mem_append_right _ h)))),
      ⟨path,d,head.fixed⟩ :: tail.fixed,
      (fun f h => (List.mem_cons.mp h).elim (fun same => same.symm ▸ head.fixedMeaning path) (tail.fixedMeaning f)),
      (fun m fit e included => (List.mem_append.mp included).elim
        (fun h => (head.fit m fit).2 e h) (fun h => tail.exactIn m fit e h))⟩
termination_by w => sizeOf w

def replayList {p : ProblemTree} (env : Global p) (reader : assign p env) (path : List Nat) (ordinal : Nat) (ds : List Demand) :
    Codes → Option (ReplayedList env ds)
  | .nil =>
    match ds with
    | [] => some ⟨[],[],fun _ _ => .nil,[],fun _ h => False.elim (List.not_mem_nil h),fun _ _ _ impossible => False.elim (List.not_mem_nil impossible)⟩
    | _ :: _ => none
  | .cons first more =>
    match ds with
    | [] => none
    | d :: ds => do
      let head ← replayTree env reader (path ++ [ordinal]) d first
      let tail ← replayList env reader path (ordinal+1) ds more
      pure ⟨head.tree :: tail.trees,head.sidecar ++ tail.sidecar,
        (fun b covers => .cons (head.proof b (fun _ h => covers (List.mem_append_left _ h)))
          (tail.proof b (fun _ h => covers (List.mem_append_right _ h)))),
        head.fixed ++ tail.fixed,
        (fun f h => (List.mem_append.mp h).elim (head.fixedMeaning f) (tail.fixedMeaning f)),
        (fun m fit e included => (List.mem_append.mp included).elim
          (head.exactIn m fit e) (tail.exactIn m fit e))⟩
termination_by w => sizeOf w
end

end Yulang.GeneralDeclarativeWitnessForestEngine350
