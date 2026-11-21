import Yulang.GeneralLiveCompoundDepth316

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 24000
set_option maxHeartbeats 25000000
namespace Yulang.GeneralLiveCompoundLeafCycles316
open GeneralDictionaryJournalRefinement228Source (roles root snapshot width_two root_fixed alias_zero)
open GeneralLiveCompoundUpperRefresh316 (upperState old_models)
open GeneralLiveCompoundUpperSnapshot316 (snap context)
open GeneralLiveCompoundChildSite316
open GeneralLiveCompoundLeafProof316 (w valid center_value)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralMixedCompoundUpperSupport307 (child_history)
open GeneralDictionaryCompoundBase239 (lo hi)
open GeneralNominalVersionedCycles232 (Cyclic)
open CommonNominalFullCarrier
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open GeneralNominalRecursiveInspection (Origin)
open GeneralRebaseFiniteTree272 (Tree Canonical value)

theorem lower_actual : Equivalent (w lo).1 (variant 0 GeneralDictionaryOptionalOutput229.value) := by
  have old := (old_models _).mp valid
  have l := GeneralDictionaryCompoundTrust239.lower w
    (GeneralNominalVersionedSupport233.trusted_models GeneralDictionaryCompoundTrust239.trusted
      ((GeneralDictionaryCompoundRefresh239.models_iff _).mp ((GeneralMixedCompoundUpperRefresh307.models_iff _).mp old)))
  have a := GeneralDictionaryCompoundObstruction238.associated_value w (child_history w old)
  exact equivalent_trans l ⟨(common_variant_iff ..).mpr a.1,(common_variant_iff ..).mpr a.2⟩

theorem no_lo : ¬ Cyclic upperState (.source lo) :=
  GeneralLiveCompoundDepth316.headless_variant_no_cycle valid lower_actual GeneralDictionaryOptionalOutput229.no_test

abbrev variantTree : Tree := .node (.structural (.variant 0)) (fun _ =>
  GeneralVersionedEndpointObstructionSelect315.leaf)

theorem canonical : Canonical variantTree :=
  ⟨trivial,fun _ => ⟨by exact List.Pairwise.nil,fun i => Fin.elim0 i⟩⟩

theorem no_mid : ¬ Cyclic upperState (.source mid) :=
  GeneralRebaseTreeAcyclic272.acyclic _ _ valid _ _ canonical
    (GeneralRebaseInstalledReadback271.source_at _ _ _ center_value)

theorem no_nominal : ¬ Cyclic upperState (.source 0) := by
  have h : GeneralNominalVersionedJournal232.Models upperState =
    GeneralNominalVersionedJournal232.Models GeneralMixedCompoundUpperRefresh307.upperState :=
    funext fun m => propext (old_models m)
  exact fun c => GeneralVersionedEndpointObstructionSelect315.no_semantic
    ((GeneralNominalVersionedCycles232.full_models_only h).mp c)

theorem no_raw_incoming (slot : Fin 8) :
    ¬ GeneralNominalMixedRecurrence.Edge snap slot (5 : Fin 8) := by
  rintro (structural | nominal)
  · obtain ⟨kind,children,recorded,index,atChild⟩ := structural
    change GeneralMixedCompoundUpperBase307.viewHeads slot = _ at recorded
    unfold GeneralMixedCompoundUpperBase307.viewHeads at recorded
    split at recorded
    · cases recorded; exact Fin.elim0 index
    · split at recorded
      · cases recorded; cases atChild
      · split at recorded
        · cases recorded; cases atChild
        · cases recorded
  · obtain ⟨d,saved,i,actual,seen,equal⟩ :=
      GeneralNominalMixedRecurrence.actual_edge_sound snap _ _ nominal w valid.1.1
    have first : slot = 0 ∨ slot = 1 := by
      change (if slot = 0 ∨ slot = 1 then some GeneralLiveCompoundUpperSnapshot316.desc else none) = some d at saved
      split at saved
      · assumption
      · cases saved
    have canonicalValue := root_fixed w valid.1.2.1
    have parent : Equivalent (w (snap.base.source slot)).1 GeneralDictionaryJournalRefinement228Source.foo := by
      rcases first with rfl|rfl
      · exact canonicalValue
      · have aliased := alias_zero w valid.1.2.1
        exact equivalent_trans ⟨aliased.2,aliased.1⟩ canonicalValue
    have v := GeneralNominalRecursiveInspection.embed_observation w _ actual seen
    cases v with
    | nominal upperState eq valid =>
      cases upperState
      have nom := equivalent_trans ⟨parent.2,parent.1⟩ eq
      obtain ⟨form,smaller,asWidth⟩ := GeneralDictionaryJournalRefinement228Cycles.nominal_child .foo nom valid
      have bad : Equivalent form.value (variant 0 GeneralDictionaryOptionalOutput229.value) :=
        equivalent_trans ⟨asWidth.2,asWidth.1⟩ (equivalent_trans equal lower_actual)
      cases form with
      | top =>
        exact GeneralDictionaryGroundCopy218Refresh.top_no_head (.structural (.variant 0)) ⟨[_],rfl,bad⟩
      | width =>
        open GeneralDictionaryInspectionHeads215 GeneralNominalFiniteHeadInversion in
        have tags := tag_subtype (tagged_shape (.record []) [] rfl)
          (tagged_shape (.variant 0) [GeneralDictionaryOptionalOutput229.value] rfl) bad.1
        cases tags
      | foo => exact (by decide : ¬ (1 : Nat) < 1) smaller

private theorem path_to_no_incoming {s : GeneralNominalState.State} (target : Fin s.base.slots)
    (no : ∀ a, ¬ GeneralNominalMixedRecurrence.Edge s a target)
    {a b : Fin s.base.slots} (path : GeneralNominalMixedRecurrence.Path s a b) : b = target → a = target := by
  induction path with
  | nil => exact id
  | cons edge rest ih =>
    intro isLast
    have same := ih isLast
    cases same
    exact False.elim (no _ edge)

theorem no_raw_five : ¬ GeneralNominalCycleK2.RecursAt snap (5 : Fin 8) := by
  intro found
  obtain ⟨next,edge,path⟩ := GeneralNominalCycleK2.recurs_cycle _ _ found
  have zero := path_to_no_incoming (5 : Fin 8) no_raw_incoming path rfl
  subst next
  exact no_raw_incoming _ edge

end Yulang.GeneralLiveCompoundLeafCycles316
