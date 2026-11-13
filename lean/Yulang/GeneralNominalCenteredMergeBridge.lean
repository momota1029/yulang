import Yulang.GeneralNominalCenteredPointSource

/-! What a merge erasure must preserve. Raw transition membership constrains
recorded sites; the ordinary merged state depends only on occurrences. -/
namespace Yulang.GeneralNominalCenteredMergeBridge
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalDemandMerging
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls}

theorem output_atoms_same_occurrences (first last otherFirst otherLast : Site roles)
    (one : first.occurrence = otherFirst.occurrence) (two : last.occurrence = otherLast.occurrence) :
    outputAtoms first last = outputAtoms otherFirst otherLast := by
  unfold outputAtoms
  rw [one,two]

theorem merge_current_same_occurrences (state : Tracked roles)
    (first last otherFirst otherLast : Site roles) (support otherSupport : List (Occurrence roles))
    (one : first.occurrence = otherFirst.occurrence) (two : last.occurrence = otherLast.occurrence) :
    (GeneralNominalSharedSteps.merge state first last support).current =
      (GeneralNominalSharedSteps.merge state otherFirst otherLast otherSupport).current := by
  change GeneralNominalSaturationState.merge _ first last = GeneralNominalSaturationState.merge _ otherFirst otherLast
  unfold GeneralNominalSaturationState.merge
  rw [output_atoms_same_occurrences first last otherFirst otherLast one two,one,two]

theorem merge_fact_semantics (first last otherFirst otherLast : Site roles)
    (support : List (Occurrence roles))
    (one : first.occurrence = otherFirst.occurrence) (two : last.occurrence = otherLast.occurrence) :
    (Fact.merge first last support).dependencies = (Fact.merge otherFirst otherLast support).dependencies ∧
      ∀ model, (Fact.merge first last support).Holds model ↔ (Fact.merge otherFirst otherLast support).Holds model := by
  constructor
  · simp only [Fact.dependencies,one,two]
  · intro model
    change PresenceNormalForm.All _ _ (outputAtoms first last) ↔ PresenceNormalForm.All _ _ (outputAtoms otherFirst otherLast)
    rw [output_atoms_same_occurrences first last otherFirst otherLast one two]

theorem no_merge_in_install (state : Tracked roles) (packet : Packet roles)
    (first last : Site roles) (support : List (Occurrence roles)) :
    Fact.merge first last support ∉ GeneralNominalSupportChoices.installedFacts state packet := by
  intro member
  obtain ⟨chosen,_,member⟩ := List.mem_flatMap.mp member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with impossible | impossible <;> cases impossible

theorem actual_new_merge_registered
    (step : GeneralNominalActualInspectionSteps.Step registry root before after)
    (present : Fact.merge first last support ∈ after.facts)
    (new : Fact.merge first last support ∉ before.facts) :
    first ∈ before.current.sites ∧ last ∈ before.current.sites := by
  obtain ⟨focus,_,action⟩ := step
  cases action with
  | administrative focus after action => exact False.elim (new present)
  | install packet dependencies enabled novel guard =>
      rcases List.mem_append.mp present with added | old
      · exact False.elim (no_merge_in_install before packet first last support added)
      · exact False.elim (new old)
  | merge a b dependencies one two same novel guard =>
      rcases List.mem_append.mp present with added | old
      · obtain ⟨chosen,_,equal⟩ := List.mem_map.mp added
        cases equal
        exact ⟨one,two⟩
      · exact False.elim (new old)

theorem centered_merge_has_new_fact
    (state : GeneralNominalCenteredSteps.State roles) (first last : GeneralNominalCenters.Site roles)
    (support : List (Occurrence roles))
    (guard : GeneralNominalSupportChoices.MergeGuard state.erased first.observed last.observed support) :
    ∃ chosen, Fact.merge first.observed last.observed chosen ∈
      (GeneralNominalCenteredSteps.merge state first last support).erased.facts := by
  obtain ⟨chosen,member⟩ := GeneralNominalSupportChoices.merge_alternatives_exists state.erased first.observed last.observed support guard
  exact ⟨chosen,List.mem_append_left _ (List.mem_map.mpr ⟨chosen,member,rfl⟩)⟩

theorem centered_merge_not_exact
    (state : GeneralNominalCenteredSteps.State roles) (first last : GeneralNominalCenters.Site roles)
    (support : List (Occurrence roles))
    (guard : GeneralNominalSupportChoices.MergeGuard state.erased first.observed last.observed support)
    (unregistered : first.observed ∉ state.erased.current.sites)
    (novel : ∀ chosen, Fact.merge first.observed last.observed chosen ∉ state.erased.facts) :
    ¬ GeneralNominalActualInspectionSteps.Step registry root state.erased
      (GeneralNominalCenteredSteps.merge state first last support).erased := by
  intro step
  obtain ⟨chosen,present⟩ := centered_merge_has_new_fact state first last support guard
  exact unregistered (actual_new_merge_registered step present (novel chosen)).1

theorem merge_empty_outputs_slices (state : Tracked roles) (first last : Site roles)
    (support observed : List (Occurrence roles)) (empty : first.occurrence.demand.outputs = []) (model : Assignment) :
    Slice (GeneralNominalSharedSteps.merge state first last support) observed model ↔ Slice state observed model := by
  constructor
  · intro valid
    exact ⟨valid.1,fun fact member included => valid.2 fact (List.mem_append_right _ member) included⟩
  · intro valid
    refine ⟨valid.1,?_⟩
    intro fact member included
    rcases List.mem_append.mp member with added | old
    · obtain ⟨chosen,_,rfl⟩ := List.mem_map.mp added
      simp only [Fact.Holds,outputAtoms,empty,List.flatMap_nil]
      exact PresenceNormalForm.all_nil _ _
    · exact valid.2 fact old included

end Yulang.GeneralNominalCenteredMergeBridge
