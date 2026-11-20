import Yulang.GeneralDeferredLadderTowerHead303
import Yulang.GeneralNominalCycleK2
import Yulang.GeneralNominalFiniteHeadInversion
import Yulang.GeneralNominalPeelingOrigins

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderShape303
open CommonNominalFullCarrier
open GeneralNominalOutputGrowth (tower finiteModel)
open GeneralDeferredLadderTowerHead303 (no_structural_head)

def depth (n : Nat) (s : GeneralNominalState.State) (slot : Fin s.base.slots) : Nat :=
  n+1-s.base.source slot

theorem nominal_projection (d : Nat) {arguments : List Argument} {actual : Ty} {index : Nat}
    (equal : Equivalent (tower d) (nominal name arguments))
    (found : arguments[index]? = some ((Sum.inl actual) : Argument)) :
    ∃ k : Nat, k < d ∧ Equivalent actual (tower k) := by
  cases d with
  | zero => exact False.elim (GeneralNominalPeelingOrigins.base_not_nominal .int name arguments equal.1)
  | succ k =>
    have info := (nominal_regular_invariant_exact _ _ _ _).mp equal.1
    have bound := (List.getElem?_eq_some_iff.mp found).1
    have length := info.2.1
    change 1 = arguments.length at length
    have first : index = 0 := by omega
    subst index
    have meaning := info.2.2 0 (.inl (tower k)) (.inl actual) rfl found
    exact ⟨k,by omega,meaning.2,meaning.1⟩

theorem path_rank {s : GeneralNominalState.State} (rank : Fin s.base.slots → Nat)
    (decrease : ∀ a b, GeneralNominalMixedRecurrence.Edge s a b → rank b < rank a)
    (a b : Fin s.base.slots) (path : GeneralNominalMixedRecurrence.Path s a b) :
    rank b ≤ rank a := by
  induction path with
  | nil => exact Nat.le_refl _
  | cons edge _ ih => exact Nat.le_trans ih (Nat.le_of_lt (decrease _ _ edge))

theorem raw_acyclic (n : Nat) (s : GeneralNominalState.State)
    (valid : GeneralNominalState.Models s (finiteModel n)) (i : Fin s.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt s i := by
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle s i cycle
  have strict {a b : Fin s.base.slots} (edge : GeneralNominalMixedRecurrence.Edge s a b) :
      depth n s b < depth n s a := by
    rcases edge with ⟨kind,children,recorded,_⟩ | edge
    · exact False.elim (no_structural_head n s valid a kind children recorded)
    · obtain ⟨desc,_,_,value,seen,same⟩ :=
        GeneralNominalMixedRecurrence.actual_edge_sound s a b edge (finiteModel n) valid
      have obs := GeneralNominalRecursiveInspection.embed_observation (finiteModel n) _ value seen
      cases obs with
      | nominal parent equal found =>
        cases parent
        change Equivalent (tower (depth n s a)) _ at equal
        obtain ⟨k,less,meaning⟩ := nominal_projection _ equal found
        change Equivalent _ (tower (depth n s b)) at same
        have eq := (GeneralNominalOutputGrowth.tower_equivalent _ _).mp
          ⟨subtype_trans same.2 meaning.1,subtype_trans meaning.2 same.1⟩
        omega
  have forward := strict edge
  have reverse := path_rank (depth n s)
    (fun _ _ edge => strict edge) _ _ path
  omega

end Yulang.GeneralDeferredLadderShape303
