import Yulang.GeneralDepthTwoFirstInstall300

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDepthTwoCenters300
open GeneralGeneratedNestedSource299 (model)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCenters (Site SameInputs)
open GeneralDeclarationExamples (roles)
open CommonNominalFullCarrier
open GeneralNominalOutputGrowth (tower tower_equivalent)

def symbolicDepth (i : Nat) := if i = 0 then 2 else if i = 1 then 1 else 0

theorem symbolic_exact (i : Nat) :
    (model i).1 = tower (symbolicDepth i) := by
  by_cases z : i = 0
  · simp [GeneralGeneratedNestedSource299.model,symbolicDepth,tower,z]
  · by_cases o : i = 1
    · simp [GeneralGeneratedNestedSource299.model,symbolicDepth,tower,o]
    · simp [GeneralGeneratedNestedSource299.model,symbolicDepth,tower,z,o]

theorem bounded_same {i j : Nat} (a : i ≤ 2) (b : j ≤ 2)
    (equal : Equivalent (model i).1 (model j).1) : i = j := by
  rw [symbolic_exact,symbolic_exact] at equal
  have eq := (tower_equivalent _ _).mp equal
  unfold symbolicDepth at eq
  split at eq <;> split at eq <;> repeat' first | split at eq | omega

theorem same_center {s : State roles} (held : Models s model) {a b : Site roles}
    (same : SameInputs (Models s) a b) {i j : Nat}
    (left : a.observed.inputs = [some (.source i)])
    (right : b.observed.inputs = [some (.source j)]) :
    Equivalent (model i).1 (model j).1 := by
  have aSeen : GeneralNominalDemandMerging.Denotes model a.observed [(model i).1] := by
    unfold GeneralNominalDemandMerging.Denotes
    rw [left]
    exact .cons ⟨_,rfl,.source i⟩ .nil
  have bSeen : GeneralNominalDemandMerging.Denotes model b.observed [(model j).1] := by
    unfold GeneralNominalDemandMerging.Denotes
    rw [right]
    exact .cons ⟨_,rfl,.source j⟩ .nil
  have paired := GeneralNominalDemandMerging.same_inputs_denote _ _ _ same model held _ _ aSeen bSeen
  cases paired with
  | cons equal _ => exact equal

theorem distinct_center {s : State roles} (held : Models s model) {a b : Site roles} {i j : Nat}
    (left : a.observed.inputs = [some (.source i)]) (right : b.observed.inputs = [some (.source j)])
    (ai : i ≤ 2) (bj : j ≤ 2) (different : i ≠ j) :
    ¬ SameInputs (Models s) a b :=
  fun same => different (bounded_same ai bj (same_center held same left right))

end Yulang.GeneralDepthTwoCenters300
