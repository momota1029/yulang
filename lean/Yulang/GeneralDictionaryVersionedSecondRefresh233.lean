import Yulang.GeneralDictionaryVersionedSecondInstall233
import Yulang.GeneralDictionaryGroundCopy218Refresh
set_option backward.isDefEq.respectTransparency false
/-! This barrier concerns the inherited source-only trusted cache, not a complete
versioned learning system. The cut intentionally need not satisfy new effects. -/
namespace Yulang.GeneralDictionaryVersionedSecondRefresh233
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229
open GeneralDictionaryVersionedSecondInstall233
open GeneralNominalCenteredHeadMatStepObservations
open CommonNominalFullCarrier

 theorem sites : installed.core.sites = [GeneralNominalCenters.rootSite snapshot.seed root] := by
  change (GeneralNominalVersionedInstall232.installCore GeneralDictionaryVersionedPointStage233.point.core plan).sites = _
  rw [GeneralNominalVersionedTerminal232.sites_eq terminal]
  exact GeneralDictionaryVersionedPointStage233.centered_sites

 theorem cut : Cut installed.legacy GeneralDictionaryOptionalSource229.modelLow := by
  apply cut_of_recorded
  · exact GeneralDictionaryOptionalSource229.source_models
  · intro site member
    change site ∈ [GeneralNominalCenters.rootSite snapshot.seed root] at member
    cases List.mem_singleton.mp member
    exact GeneralNominalCenters.point_root_holds _ _ root_point _
  · intro plan member
    change plan ∈ [] at member
    cases member
  · intro effect member
    change effect ∈ [] at member
    cases member
  · intro first one last two alias recorded
    rw [sites] at one two
    cases List.mem_singleton.mp one
    cases List.mem_singleton.mp two
    apply (GeneralNominalDemandMerging.output_atoms_exact ..).mpr
    intro a ha b hb same
    change a ∈ [⟨0,4⟩] at ha
    change b ∈ [⟨0,4⟩] at hb
    cases List.mem_singleton.mp ha
    cases List.mem_singleton.mp hb
    exact ⟨subtype_refl _,subtype_refl _⟩

 theorem no_refresh (context : GeneralNominalCandidates.Context)
    (certificate : GeneralNominalCenteredHeadMatStepRefresh.Refresh installed.legacy context)
    (unknown : ¬ GeneralNominalState.Known installed.core.erased.current.context.state identity)
    (known : GeneralNominalState.Known context.state identity) : False := by
  have zero : identity ≠ 0 := by
    intro same; subst identity
    apply unknown
    exact ⟨(0 : Fin 5),rfl,Or.inr ⟨_,rfl⟩⟩
  have one : identity ≠ 1 := by
    intro same; subst identity
    apply unknown
    exact ⟨(1 : Fin 5),rfl,Or.inr ⟨_,rfl⟩⟩
  have two : identity ≠ 2 := by
    intro same; subst identity
    apply unknown
    exact ⟨(2 : Fin 5),rfl,Or.inl (by intro h; cases h)⟩
  obtain ⟨test,observation,head⟩ := GeneralNominalCenteredHeadMatStepCache.known_has_head known
  have held := GeneralNominalCenteredHeadAllocMergeStable.head_holds head
    (by
      obtain ⟨facts,trusted,sound⟩ := certificate.cache observation (GeneralNominalSupport.head_recorded head)
      exact sound _ (cut facts trusted))
  change test.Holds (GeneralDictionaryOptionalSource229.modelLow identity).1 at held
  by_cases three : identity = 3
  · subst identity
    exact GeneralDictionaryGroundCopy218Refresh.top_no_head test held
  · have value : (GeneralDictionaryOptionalSource229.modelLow identity).1 =
        GeneralDictionaryOptionalOutput229.value := by
      simp [GeneralDictionaryOptionalSource229.modelLow,zero,one,two,three]
    rw [value] at held
    exact GeneralDictionaryOptionalOutput229.no_test test held
end Yulang.GeneralDictionaryVersionedSecondRefresh233
