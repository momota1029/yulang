import Yulang.GeneralDictionaryOptionalCurrent229

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2048
namespace Yulang.GeneralDictionaryOptionalRaw229
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryOptionalCurrent229
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalRecursiveCandidates GeneralNominalRecursiveInspection
open CommonNominalFullCarrier
variable (allocated : List GeneralNominalIdentities.Origin) (reserved : List Nat)
  (ordinary : List (PresenceNormalForm.Atom Nat))
abbrev origin0 : Origin := .nominal (.source 0) 0 0
abbrev origin1 : Origin := .nominal (.source 0) 0 1
theorem seen0 : Observes modelHigh origin0 .emptyRecord :=
  .nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl
theorem seen1 : Observes modelHigh origin1 .emptyRecord :=
  .nominal (.source 0) ⟨subtype_refl _,subtype_refl _⟩ rfl

theorem observed_value (index : Nat) (small : index < 2) (seen : Observes modelHigh (.nominal (.source 0) 0 index) value) :
    Equivalent value .emptyRecord := by
  have observed : Observes modelHigh (.nominal (.source 0) 0 index) .emptyRecord := by
    rcases (show index = 0 ∨ index = 1 by omega) with rfl | rfl
    · exact seen0
    · exact seen1
  exact nominal_observation_unique modelHigh (.argument (.source 0) 0 index) value .emptyRecord seen observed

theorem fit_observed (index : Nat) (small : index < 2) (seen : Observes modelHigh (.nominal (.source 0) 0 index) value) :
    Fits (currentContext allocated reserved ordinary).state modelHigh (2,2) value := by
  have equal := observed_value index small seen
  exact ⟨equal.2,equal.1⟩

theorem raw_projection : ProjectionModels (currentContext allocated reserved ordinary).state (report (currentContext allocated reserved ordinary) declaration [(0,0)]) modelHigh := by
  rw [report_exact]
  refine ⟨?_,?_,?_,?_⟩
  · intro anchor member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨⟨_,seen0⟩,fun _ seen => fit_observed allocated reserved ordinary 0 (by decide) seen⟩
    · cases List.mem_singleton.mp member
      exact ⟨⟨_,seen1⟩,fun _ seen => fit_observed allocated reserved ordinary 1 (by decide) seen⟩
  · intro test member; cases member
  · intro first one last two _ origin located value seen
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals cases Option.some.inj located
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals first | exact fit_observed allocated reserved ordinary 0 (by decide) seen | exact fit_observed allocated reserved ordinary 1 (by decide) seen
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



theorem high_fresh (purpose : Nat) :
    (modelHigh (fresh snapshot.seed root.identity declaration.id purpose 0 0)).1 = .emptyRecord := by
  have large : 4 < fresh snapshot.seed root.identity declaration.id purpose 0 0 :=
    GeneralNominalIdentities.source_above_seed snapshot.seed _
  have zero : fresh snapshot.seed root.identity declaration.id purpose 0 0 ≠ 0 := by omega
  have one : fresh snapshot.seed root.identity declaration.id purpose 0 0 ≠ 1 := by omega
  have three : fresh snapshot.seed root.identity declaration.id purpose 0 0 ≠ 3 := by omega
  change fresh 4 228 229 purpose 0 0 ≠ 0 at zero
  change fresh 4 228 229 purpose 0 0 ≠ 1 at one
  change fresh 4 228 229 purpose 0 0 ≠ 3 at three
  simp [modelHigh,GeneralDictionaryJournalRefinement228Source.model,zero,one,three]

theorem merge_model : PresenceNormalForm.All CommonNominalFullCarrier.model modelHigh
    (GeneralNominalAllocation.merges (currentContext allocated reserved ordinary).state registry root.identity declaration
      (packet allocated reserved ordinary).bindings) := by
  rw [bindings_exact]
  let lo := fresh snapshot.seed root.identity declaration.id 0 0 0
  let hi := fresh snapshot.seed root.identity declaration.id 1 0 0
  have pair : PresenceNormalForm.All CommonNominalFullCarrier.model modelHigh
      (GeneralNominalAllocation.equations lo (.union (.var 2) (.var 2)) ++
        GeneralNominalAllocation.equations hi (.inter (.var 2) (.var 2))) := by
    rw [PresenceNormalForm.all_append,GeneralNominalCaptureMerges.equations_exact,
      GeneralNominalCaptureMerges.equations_exact]
    change Equivalent (modelHigh lo).1 (.union .emptyRecord .emptyRecord) ∧
      Equivalent (modelHigh hi).1 (.inter .emptyRecord .emptyRecord)
    rw [high_fresh 0,high_fresh 1]
    exact ⟨⟨(common_union_is_join _ _ _).mp (subtype_refl _) |>.1,
      (common_union_is_join _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩⟩,
      ⟨(common_inter_is_meet _ _ _).mpr ⟨subtype_refl _,subtype_refl _⟩,
      (common_inter_is_meet _ _ _).mp (subtype_refl _) |>.1⟩⟩
  change PresenceNormalForm.All CommonNominalFullCarrier.model modelHigh (_ ++ _)
  exact (PresenceNormalForm.all_append ..).mpr ⟨pair,pair⟩

theorem head_model
    (raw : GeneralNominalState.Models (currentContext allocated reserved ordinary).state modelHigh) :
    GeneralNominalCenteredHeadCandidates.HeadModels registry (currentContext allocated reserved ordinary)
      root declaration [(0,0)] modelHigh := by
  refine ⟨?_,raw_projection allocated reserved ordinary⟩
  unfold privateState
  apply (GeneralNominalState.extend_models ..).mpr
  refine ⟨(GeneralNominalAllocation.propagate_models ..).mpr ⟨raw,?_,merge_model allocated reserved ordinary⟩,?_⟩
  · change GeneralNominalAllocation.Compatible (packet allocated reserved ordinary).bindings modelHigh
    rw [bindings_exact]
    intro first one last two _
    rcases List.mem_cons.mp one with rfl | one
    all_goals first | cases List.mem_singleton.mp one | skip
    all_goals rcases List.mem_cons.mp two with rfl | two
    all_goals first | cases List.mem_singleton.mp two | skip
    all_goals exact subtype_refl _
  · rw [report_exact]
    intro atom member
    simp only [selfChecks,List.map_cons,List.map_nil,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals exact subtype_refl _

end Yulang.GeneralDictionaryOptionalRaw229
