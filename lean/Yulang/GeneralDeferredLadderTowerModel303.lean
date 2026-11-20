import Yulang.GeneralDeferredLadderShape303

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderTowerModel303
open CommonNominalFullCarrier
open GeneralNominalOutputGrowth (tower)
open GeneralNominalCommonBridge (Assignment)
open GeneralDeferredLadderShape303 (nominal_projection path_rank)
open GeneralDeferredLadderTowerHead303 (structural_not_tower)

/-- The depth ranking depends on the witness interpretation, not on a
particular numbering of source slots or a common bound on all source ids. -/
theorem edge_decreases (s : GeneralNominalState.State) (m : Assignment)
    (depth : Nat → Nat) (tower_at : ∀ source, (m source).1 = tower (depth source))
    (valid : GeneralNominalState.Models s m)
    {a b : Fin s.base.slots} (edge : GeneralNominalMixedRecurrence.Edge s a b) :
    depth (s.base.source b) < depth (s.base.source a) := by
  rcases edge with ⟨kind,kids,recorded,_⟩ | edge
  · have holds := GeneralNominalState.normalized_models s m valid a ((s.view.shapes kind).term kids)
      (by rw [recorded]; rfl)
    rw [tower_at] at holds
    exact False.elim (structural_not_tower (s.view.shapes kind) kids
      (GeneralNominalCommonBridge.assignment s.base m) _ holds.1)
  · obtain ⟨desc,_,_,value,seen,same⟩ := GeneralNominalMixedRecurrence.actual_edge_sound s a b edge m valid
    have obs := GeneralNominalRecursiveInspection.embed_observation m _ value seen
    cases obs with
    | nominal parent equal found =>
      cases parent
      rw [tower_at] at equal
      obtain ⟨d,less,meaning⟩ := nominal_projection _ equal found
      rw [tower_at] at same
      have rank := (GeneralNominalOutputGrowth.tower_equivalent _ _).mp
        ⟨subtype_trans same.2 meaning.1,subtype_trans meaning.2 same.1⟩
      rwa [rank]

theorem raw_acyclic (s : GeneralNominalState.State) (m : Assignment)
    (depth : Nat → Nat) (tower_at : ∀ source, (m source).1 = tower (depth source))
    (valid : GeneralNominalState.Models s m) (i : Fin s.base.slots) :
    ¬ GeneralNominalCycleK2.RecursAt s i := by
  intro recurs
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle s i recurs
  have measure := edge_decreases s m depth tower_at valid edge
  have back := path_rank (depth ∘ s.base.source)
    (fun _ _ e => edge_decreases s m depth tower_at valid e) _ _ path
  change depth (s.base.source i) ≤ depth (s.base.source next) at back
  omega

end Yulang.GeneralDeferredLadderTowerModel303
