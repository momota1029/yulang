import Yulang.GeneralObservedLadderSelection301
import Yulang.GeneralRebaseDisplaySafety276
import Yulang.GeneralRebaseAllWidthSafety275

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralObservedLadderSafety301
open GeneralObservedLadderSource301 (snapshot model_exists)
open GeneralObservedLadderInitial301 (initial)
open GeneralNominalOutputGrowth (tower finiteModel tower_equivalent)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralDeclarationExamples (roles)
open CommonNominalFullCarrier GeneralNominalRecursiveInspection

theorem towers (n id : Nat) : (finiteModel n id).1 = tower (n+1-id) := rfl

theorem semantic (n : Nat) {s : State roles} (valid : Models s (finiteModel n)) (origin) :
    ¬ GeneralNominalVersionedCycles232.Cyclic s origin :=
  GeneralRebaseTowerAcyclic276.acyclic valid (fun id => ⟨n+1-id,towers n id⟩) origin

def depth (n : Nat) (s : GeneralNominalState.State) (slot : Fin s.base.slots) : Nat :=
  n+1-s.base.source slot

theorem raw_edge (n : Nat) (s : GeneralNominalState.State) (noShapes : s.view.kinds = 0)
    (valid : GeneralNominalState.Models s (finiteModel n))
    {a b : Fin s.base.slots} (edge : GeneralNominalMixedRecurrence.Edge s a b) :
    depth n s b < depth n s a := by
  rcases edge with ⟨kind,_,_,_⟩ | nominal
  · have small := kind.isLt
    omega
  · obtain ⟨desc,_,i,value,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound s a b nominal (finiteModel n) valid
    have obs := embed_observation (finiteModel n) _ value seen
    cases obs with
    | nominal parent equal found =>
      cases parent
      change Equivalent (tower (depth n s a)) _ at equal
      obtain ⟨k,less,meaning⟩ := GeneralRebaseTowerSemantics276.nominal_projection _ equal found
      change Equivalent _ (tower (depth n s b)) at same
      have eq := (tower_equivalent _ _).mp
        ⟨subtype_trans same.2 meaning.1,subtype_trans meaning.2 same.1⟩
      omega

theorem raw_acyclic (n : Nat) (s : GeneralNominalState.State) (noShapes : s.view.kinds = 0)
    (valid : GeneralNominalState.Models s (finiteModel n)) (i : Fin s.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt s i := by
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle s i cycle
  have strict := raw_edge n s noShapes valid edge
  have reverse := GeneralRebaseAllWidthSafety275.path_rank (depth n s)
    (fun _ _ edge => raw_edge n s noShapes valid edge) _ _ path
  omega

end Yulang.GeneralObservedLadderSafety301
