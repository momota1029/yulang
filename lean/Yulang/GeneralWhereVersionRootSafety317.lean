import Yulang.GeneralWhereVersionRootHead317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 34000
set_option maxHeartbeats 49000000
namespace Yulang.GeneralWhereVersionRootSafety317
open GeneralDictionaryJournalRefinement228Source (roles root_fixed alias_zero)
open GeneralWhereVersionSnapshot317 (snap viewHeads zero one nextDesc)
open GeneralWhereVersionWitness317 (ParentHolds)
open GeneralWhereVersionCommit317 (framedState new_snapshot compiled_models)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier
open GeneralDictionaryDefaultExpression209 (equivalent_trans)

theorem no_semantic (m : Assignment) (valid : ParentHolds m) :
    ¬ GeneralNominalVersionedCycles232.Cyclic framedState (.source 0) :=
  GeneralRebaseTreeAcyclic272.acyclic _ _ (compiled_models m valid) _ _
    GeneralVersionedEndpointObstructionSelect315.canonical
    (GeneralRebaseInstalledReadback271.source_at _ _ _ (root_fixed m valid.1.1.2.1))

theorem no_raw_incoming (m : Assignment) (valid : ParentHolds m) (slot : Fin 10) :
    ¬ GeneralNominalMixedRecurrence.Edge snap slot zero := by
  rintro (structural | nominal)
  · obtain ⟨kind,children,recorded,index,atChild⟩ := structural
    change viewHeads slot = _ at recorded
    unfold viewHeads at recorded
    split at recorded
    · cases recorded; exact Fin.elim0 index
    · split at recorded
      · cases recorded; cases atChild
      · split at recorded
        · cases recorded; cases atChild
        · cases recorded
  · obtain ⟨d,saved,i,actual,seen,equal⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound snap _ _ nominal m (new_snapshot m valid)
    have first : slot = zero ∨ slot = one := by
      change (if slot = zero ∨ slot = one then some nextDesc else none) = some d at saved
      split at saved
      · assumption
      · cases saved
    have canonicalValue := root_fixed m valid.1.1.2.1
    have parent : Equivalent (m (snap.base.source slot)).1 GeneralDictionaryJournalRefinement228Source.foo := by
      rcases first with rfl|rfl
      · change Equivalent (m (GeneralWhereVersionBase317.source zero)).1 _
        rw [GeneralWhereVersionBase317.source_old]; exact canonicalValue
      · have aliased := alias_zero m valid.1.1.2.1
        change Equivalent (m (GeneralWhereVersionBase317.source one)).1 _
        rw [GeneralWhereVersionBase317.source_old]
        exact equivalent_trans ⟨aliased.2,aliased.1⟩ canonicalValue
    have v := GeneralNominalRecursiveInspection.embed_observation m _ actual seen
    cases v with
    | nominal src eq included =>
      cases src
      have nom := equivalent_trans ⟨parent.2,parent.1⟩ eq
      obtain ⟨form,smaller,asWidth⟩ := GeneralDictionaryJournalRefinement228Cycles.nominal_child .foo nom included
      change Equivalent actual (m (GeneralWhereVersionBase317.source zero)).1 at equal
      rw [GeneralWhereVersionBase317.source_old] at equal
      have bad : Equivalent form.value GeneralDictionaryJournalRefinement228Source.foo :=
        equivalent_trans ⟨asWidth.2,asWidth.1⟩ (equivalent_trans equal canonicalValue)
      have rankEq := GeneralDictionaryJournalRefinement228Cycles.equivalent_rank form .foo bad
      omega

private theorem path_end {s : GeneralNominalState.State} (target : Fin s.base.slots)
    (no : ∀ a, ¬ GeneralNominalMixedRecurrence.Edge s a target)
    {a b : Fin s.base.slots} (path : GeneralNominalMixedRecurrence.Path s a b) : b = target → a = target := by
  induction path with
  | nil => exact id
  | cons edge _ ih =>
    intro here
    have same := ih here
    cases same
    exact False.elim (no _ edge)

theorem no_raw (m : Assignment) (valid : ParentHolds m) :
    ¬ GeneralNominalCycleK2.RecursAt snap zero := by
  intro found
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ found
  have same := path_end zero (no_raw_incoming m valid) path rfl
  subst next
  exact no_raw_incoming m valid _ edge

end Yulang.GeneralWhereVersionRootSafety317
