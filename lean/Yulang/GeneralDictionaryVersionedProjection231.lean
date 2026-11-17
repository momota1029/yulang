import Yulang.GeneralDictionaryVersionedMerge231
import Yulang.GeneralNominalVersionedPlans231
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDictionaryVersionedProjection231
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryUpper230Current
open GeneralDictionaryVersionedNames231
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
abbrev origin0 : Origin := .nominal (.source 0) 0 0
abbrev origin1 : Origin := .nominal (.source 0) 0 1
theorem seen0 : Observes extended origin0 .emptyRecord := by
  refine Observes.nominal (arguments := [.inl .emptyRecord,.inl .emptyRecord]) (.source 0) ?_ rfl
  change Equivalent (extended 0).1 foo
  rw [old_value 0 (by simp [GeneralDictionaryVersionedSupport231.pool])]
  exact ⟨subtype_refl _,subtype_refl _⟩
theorem seen1 : Observes extended origin1 .emptyRecord := by
  refine Observes.nominal (arguments := [.inl .emptyRecord,.inl .emptyRecord]) (.source 0) ?_ rfl
  change Equivalent (extended 0).1 foo
  rw [old_value 0 (by simp [GeneralDictionaryVersionedSupport231.pool])]
  exact ⟨subtype_refl _,subtype_refl _⟩

theorem observed_value (index : Nat) (small : index < 2) (seen : Observes extended (.nominal (.source 0) 0 index) value) :
    Equivalent value .emptyRecord := by
  have observed : Observes extended (.nominal (.source 0) 0 index) .emptyRecord := by
    rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
    · exact seen0
    · exact seen1
  exact nominal_observation_unique extended (.argument (.source 0) 0 index) value .emptyRecord seen observed

theorem fit_observed (index : Nat) (small : index < 2) (seen : Observes extended (.nominal (.source 0) 0 index) value) :
    Fits (currentContext).state extended (2,2) value := by
  have equal := observed_value index small seen
  change Subtype (extended 2).1 value ∧ Subtype value (extended 2).1
  rw [two_retained]
  exact ⟨equal.2,equal.1⟩

theorem raw_projection : ProjectionModels (currentContext).state (report (currentContext) declaration [(0,0)]) extended := by
  rw [report_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨_,seen0⟩,fun _ seen => fit_observed 0 (by decide) seen⟩
    · cases List.mem_singleton.mp member
      exact ⟨⟨_,seen1⟩,fun _ seen => fit_observed 1 (by decide) seen⟩
  · intro test member; cases member
  · intro first one last two _ origin located value seen
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj located
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals first | exact fit_observed 0 (by decide) seen | exact fit_observed 1 (by decide) seen
  · intro first one last two _ a b firstOrigin lastOrigin x y seenX seenY
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj firstOrigin
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals cases Option.some.inj lastOrigin
    all_goals
      have ex : Equivalent x .emptyRecord := by first | exact observed_value 0 (by decide) seenX | exact observed_value 1 (by decide) seenX
      have ey : Equivalent y .emptyRecord := by first | exact observed_value 0 (by decide) seenY | exact observed_value 1 (by decide) seenY
      exact ⟨subtype_trans ex.1 ey.2,subtype_trans ey.1 ex.2⟩




theorem self_checks : PresenceNormalForm.All CommonNominalFullCarrier.model extended
    (selfChecks currentContext.state (report currentContext declaration [(0,0)])) := by
  rw [report_exact]
  intro atom member
  simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals exact subtype_refl _

theorem ordinary : GeneralNominalVersionedPlans231.Ordinary packet extended := by
  unfold GeneralNominalVersionedPlans231.Ordinary
  rw [bindings_exact]
  exact ⟨GeneralDictionaryVersionedMerge231.compatible,GeneralDictionaryVersionedMerge231.merge_model,self_checks⟩

theorem head_models : GeneralNominalVersionedPlans231.HeadModels packet extended :=
  ⟨(GeneralNominalVersionedPlans231.private_models_iff ..).mpr
    ⟨retains_journal.1,ordinary⟩,raw_projection⟩

end Yulang.GeneralDictionaryVersionedProjection231
