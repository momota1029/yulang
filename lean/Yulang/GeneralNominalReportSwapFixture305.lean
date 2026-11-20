import Yulang.GeneralNominalReportRecompute305
import Yulang.GeneralNominalSlotSwapFixture304

namespace Yulang.GeneralNominalReportSwapFixture305
open GeneralNominalSlotSwapFixture304 (snapshot move viewHead knownSlot move_iff_known move_source)
open GeneralNominalReportCoordinates305 (Coordinates observed HeadData nominalRead nominalMove)
open GeneralNominalRecursiveInspection (Origin Capture Report inspectMany)
open GeneralNominalReportSourceTransport (moveBounds moveReport)
open GeneralNominalInspection (Query Bounds)

def coordinates (a b : Bool) : Coordinates (snapshot a) (snapshot b) := by
  refine ⟨move a b,fun i => congrArg Fin.val (move_source a b i),?_,fun _ => rfl⟩
  intro i
  have seen (swap : Bool) (j : Fin 2) :
      observed (snapshot swap) j =
        if j = knownSlot swap then .scalar .int else .pending := by
    unfold observed
    rw [show (snapshot swap).view.heads j = viewHead swap j from rfl]
    by_cases eq : j = knownSlot swap <;> simp [viewHead,eq]
  rw [seen b (move a b i),seen a i]
  by_cases same : i = knownSlot a
  · rw [ite_eq_left same,ite_eq_left ((move_iff_known a b i).mpr same)]
    rfl
  · rw [ite_eq_right same,ite_eq_right (fun h => same ((move_iff_known a b i).mp h))]
    rfl

def queries : List Query := [.variables [7,7],.scalar .int,.scalar .bool,.scalar .int,.variables [42]]

def spans (swap : Bool) : List (Bounds (snapshot swap)) :=
  [(knownSlot swap,knownSlot swap),(knownSlot swap,knownSlot swap),
   (knownSlot swap,knownSlot swap),(GeneralNominalSlotSwapFixture304.pos swap 1,
      GeneralNominalSlotSwapFixture304.pos swap 1)]

def origins (i : Nat) : Option Origin := some (.source i)

theorem full_report :
    inspectMany (snapshot true) queries (spans true) origins 0 =
      moveReport (move false true) (inspectMany (snapshot false) queries (spans false) origins 0) :=
  GeneralNominalReportRecompute305.many_exact (coordinates false true) queries (spans false) origins 0

def harvest {s : GeneralNominalState.State} (r : Report s) :
    List (Nat × Nat × Nat × Option Origin) × List Nat × List Nat × List (Nat × Nat) :=
  (r.captures.map fun c => (c.name,c.bounds.1.val,c.bounds.2.val,c.origin),
    r.blocked.map fun p => p.1.val,r.conflicts.map fun p => p.1.val,r.arity)

theorem actual_output :
    harvest (inspectMany (snapshot false) queries (spans false) origins 0) =
      ([(7,0,0,some (.source 0)),(7,0,0,some (.source 0))],[1],[0],[(1,0)]) ∧
    harvest (inspectMany (snapshot true) queries (spans true) origins 0) =
      ([(7,1,1,some (.source 0)),(7,1,1,some (.source 0))],[0],[1],[(1,0)]) := by
  constructor <;> decide +kernel

end Yulang.GeneralNominalReportSwapFixture305
