import Yulang.GeneralMixedCompoundPointEvidence308
import Yulang.GeneralMixedCompoundUpperTypes307

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 22000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralMixedCompoundPointAdmin308
open GeneralDictionaryJournalRefinement228Source (roles root snapshot root_fixed)
open GeneralDictionaryCompoundSource238 (registry declaration)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralMixedCompoundPointFirstPlan308 (candidateModel)
open GeneralMixedCompoundPointViewTrust308 (observed)
open GeneralMixedCompoundPointSites308 (centers)
open GeneralMixedCompoundPointRoot308 (models_observed)
open GeneralNominalVersionedDiagnostic232 (AdministrativeReady)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCenters (Site rootSite SameInputs)
open GeneralNominalDemandMerging (Denotes same_inputs_denote)
open GeneralNominalRecursiveInspection (Origin Observes)
open GeneralMixedCompoundChildEquality307 (mid)
open GeneralDictionaryDefaultExpression209 (equivalent_trans)
open CommonNominalFullCarrier

abbrev rSite := rootSite snapshot.seed root
noncomputable abbrev w := candidateModel

theorem root_denotes : Denotes w rSite.observed [(w 0).1] := by
  change GeneralNominalDemandMerging.All₂
    (fun ref value => ∃ origin : Origin, ref = some origin ∧ Observes w origin value)
    [some (.source 0)] [(w 0).1]
  exact .cons ⟨_,rfl,.source 0⟩ .nil

theorem child_denotes : Denotes w childSite.observed [(w mid).1] := by
  change GeneralNominalDemandMerging.All₂
    (fun ref value => ∃ origin : Origin, ref = some origin ∧ Observes w origin value)
    [some (.source mid)] [(w mid).1]
  exact .cons ⟨_,rfl,.source mid⟩ .nil

theorem different : ¬ Equivalent (w 0).1 (w mid).1 := by
  intro collapse
  have a := root_fixed w models_observed.1.2.1
  have b : (w mid).1 = variant 0 .emptyRecord := GeneralRebaseCompoundReplacement273.center_value
  rw [b] at collapse
  have no : Equivalent (GeneralMixedCompoundUpperTypes307.meaning .nominal)
      (GeneralMixedCompoundUpperTypes307.meaning .variantWidth) :=
    equivalent_trans ⟨a.2,a.1⟩ collapse
  cases GeneralMixedCompoundUpperTypes307.equiv_kind no

theorem no_merge_forward : ¬ SameInputs (Models observed) rSite childSite := by
  intro yes
  have all := same_inputs_denote _ _ _ yes w models_observed _ _ root_denotes child_denotes
  cases all with | cons h _ => exact different h

theorem no_merge_backward : ¬ SameInputs (Models observed) childSite rSite := by
  intro yes
  have all := same_inputs_denote _ _ _ yes w models_observed _ _ child_denotes root_denotes
  cases all with | cons h _ => exact different ⟨h.2,h.1⟩

theorem merge_already {a b : Site roles} (one : a ∈ observed.core.sites) (two : b ∈ observed.core.sites)
    (yes : SameInputs (Models observed) a b) :
    GeneralNominalSaturationState.Alias observed.core.erased.current a.occurrence.identity b.occurrence.identity := by
  rw [centers] at one two
  rcases List.mem_cons.mp one with rfl|one <;> rcases List.mem_cons.mp two with rfl|two
  · exact .refl _
  · cases List.mem_singleton.mp two; exact False.elim (no_merge_forward yes)
  · cases List.mem_singleton.mp one; exact False.elim (no_merge_backward yes)
  · cases List.mem_singleton.mp one; cases List.mem_singleton.mp two; exact .refl _

theorem root_ready : AdministrativeReady observed root :=
  ⟨⟨rSite,centers ▸ List.mem_cons_self,rfl⟩,fun _ a _ _ b same => merge_already a b same⟩

theorem child_ready : AdministrativeReady observed childSite.occurrence :=
  ⟨⟨childSite,centers ▸ List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl⟩,
    fun _ a _ _ b same => merge_already a b same⟩

end Yulang.GeneralMixedCompoundPointAdmin308
