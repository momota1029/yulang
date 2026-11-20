import Yulang.GeneralGeneratedNestedInitial299
import Yulang.GeneralRebaseDisplaySafety276

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDepthTwoSafety300
open GeneralGeneratedNestedSource299
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalOutputGrowth (tower tower_equivalent)
open CommonNominalFullCarrier GeneralNominalRecursiveInspection

theorem towers (id : Nat) : ∃ n, (model id).1 = tower n := by
  by_cases x : id = 0
  · exact ⟨2,by simp [GeneralGeneratedNestedSource299.model,x,tower]⟩
  · by_cases y : id = 1
    · exact ⟨1,by simp [GeneralGeneratedNestedSource299.model,y,tower]⟩
    · exact ⟨0,by simp [GeneralGeneratedNestedSource299.model,x,y,tower]⟩

theorem semantic {s : State roles} (valid : Models s model) (origin) :
    ¬ GeneralNominalVersionedCycles232.Cyclic s origin :=
  GeneralRebaseTowerAcyclic276.acyclic valid towers origin

noncomputable def depth (s : GeneralNominalState.State) (slot : Fin s.base.slots) : Nat :=
  Classical.choose (towers (s.base.source slot))

theorem depth_exact (s : GeneralNominalState.State) (slot : Fin s.base.slots) :
    (model (s.base.source slot)).1 = tower (depth s slot) :=
  Classical.choose_spec (towers (s.base.source slot))

theorem raw_edge (s : GeneralNominalState.State) (noShapes : s.view.kinds = 0)
    (valid : GeneralNominalState.Models s model)
    {a b : Fin s.base.slots} (edge : GeneralNominalMixedRecurrence.Edge s a b) :
    depth s b < depth s a := by
  rcases edge with ⟨kind,_,_,_⟩ | nominal
  · have small := kind.isLt
    omega
  · obtain ⟨desc,_,i,value,seen,same⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound s a b nominal model valid
    have obs := embed_observation model _ value seen
    cases obs with
    | nominal parent equal found =>
      cases parent
      rw [depth_exact s a] at equal
      obtain ⟨k,less,meaning⟩ := GeneralRebaseTowerSemantics276.nominal_projection _ equal found
      rw [depth_exact s b] at same
      have eq := (tower_equivalent _ _).mp
        ⟨subtype_trans same.2 meaning.1,subtype_trans meaning.2 same.1⟩
      omega

theorem raw_acyclic (s : GeneralNominalState.State) (noShapes : s.view.kinds = 0)
    (valid : GeneralNominalState.Models s model) (i : Fin s.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt s i := by
  intro cycle
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle s i cycle
  have strict := raw_edge s noShapes valid edge
  have reverse := GeneralRebaseAllWidthSafety275.path_rank (depth s)
    (fun _ _ edge => raw_edge s noShapes valid edge) _ _ path
  omega

end Yulang.GeneralDepthTwoSafety300
