import Yulang.GeneralWhereVersionLeaf317

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 31000
set_option maxHeartbeats 41000000
namespace Yulang.GeneralWhereVersionLeafSafety317
open GeneralDictionaryJournalRefinement228Source (roles width_two root_fixed alias_zero)
open GeneralWhereVersionBase317 (loSlot hiSlot two five seven six)
open GeneralWhereVersionSnapshot317 (snap context viewHeads zero one nextDesc)
open GeneralWhereVersionCase317 (lower upper)
open GeneralWhereVersionWitness317 (ParentHolds inhabited)
open GeneralWhereVersionCommit317 (framedState ports compiled_models new_snapshot)
open GeneralWhereVersionLeafProof317 (mid mid_value)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedCycles232 (Cyclic)
open CommonNominalFullCarrier
open GeneralDictionaryDefaultExpression209 (equivalent_trans)

theorem width (m : Assignment) (valid : ParentHolds m) :
    Equivalent (m 2).1 .emptyRecord :=
  width_two m valid.1.1.2.1

theorem lower_value (m : Assignment) (valid : ParentHolds m) :
    Equivalent (m lower).1 (variant 0 .emptyRecord) :=
  equivalent_trans (ports m valid).1
    ⟨(common_variant_iff ..).mpr (width m valid).1,(common_variant_iff ..).mpr (width m valid).2⟩

theorem center_value (m : Assignment) (valid : ParentHolds m) :
    Equivalent (m mid).1 (variant 0 .emptyRecord) :=
  equivalent_trans (mid_value m valid)
    ⟨(common_variant_iff ..).mpr (width m valid).1,(common_variant_iff ..).mpr (width m valid).2⟩

theorem no_lower (m : Assignment) (valid : ParentHolds m) : ¬ Cyclic framedState (.source lower) :=
  GeneralRebaseTreeAcyclic272.acyclic _ _ (compiled_models m valid) _ _
    GeneralLiveCompoundLeafCycles316.canonical
    (GeneralRebaseInstalledReadback271.source_at _ _ _ (lower_value m valid))

theorem no_center (m : Assignment) (valid : ParentHolds m) : ¬ Cyclic framedState (.source mid) :=
  GeneralRebaseTreeAcyclic272.acyclic _ _ (compiled_models m valid) _ _
    GeneralLiveCompoundLeafCycles316.canonical
    (GeneralRebaseInstalledReadback271.source_at _ _ _ (center_value m valid))

theorem no_raw_incoming (m : Assignment) (valid : ParentHolds m) (slot : Fin 10) :
    ¬ GeneralNominalMixedRecurrence.Edge snap slot loSlot := by
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
      change Equivalent actual (m (GeneralWhereVersionBase317.source loSlot)).1 at equal
      rw [GeneralWhereVersionBase317.source_lo] at equal
      have bad : Equivalent form.value (variant 0 .emptyRecord) :=
        equivalent_trans ⟨asWidth.2,asWidth.1⟩ (equivalent_trans equal (lower_value m valid))
      cases form with
      | top =>
        exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.structural (.variant 0)) ⟨[_],rfl,bad⟩
      | width =>
        open GeneralDictionaryInspectionHeads215 GeneralNominalFiniteHeadInversion in
        have tags := tag_subtype (tagged_shape (.record []) [] rfl)
          (tagged_shape (.variant 0) [.emptyRecord] rfl) bad.1
        cases tags
      | foo => exact (by decide : ¬ (1 : Nat) < 1) smaller

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
    ¬ GeneralNominalCycleK2.RecursAt snap loSlot := by
  intro found
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ found
  have same := path_end loSlot (no_raw_incoming m valid) path rfl
  subst next
  exact no_raw_incoming m valid _ edge

end Yulang.GeneralWhereVersionLeafSafety317
