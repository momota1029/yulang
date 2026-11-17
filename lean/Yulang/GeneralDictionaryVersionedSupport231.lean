import Yulang.GeneralDictionaryUpper230Regression
import Yulang.GeneralDictionaryDefaultJournalSupport213
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Yulang.GeneralDictionaryVersionedSupport231
open GeneralDictionaryJournalRefinement228Source
open GeneralDictionaryOptionalInitial229 GeneralDictionaryOptionalInstall229
open GeneralDictionaryUpper230Step
abbrev pool : List Nat := [0,1,2,3,4,lo,hi,actual]
theorem packet_support : GeneralDictionaryDefaultPacketSupport213.packetSources plan ⊆ pool := by
  decide +kernel
theorem head_support : GeneralNominalHeadLedgerFrame182.headSources plan ⊆ pool := by
  decide +kernel

theorem class_support (state : GeneralNominalCenteredSteps.State roles)
    (requests : ∀ output ∈ GeneralNominalCenteredHeadOutputs.requests state root,
      output = ⟨0,4⟩) :
    GeneralDictionaryDefaultModeEffects213.classSources state root plan ⊆ pool := by
  intro name member
  obtain ⟨output,present,member⟩ := List.mem_flatMap.mp member
  cases requests output present
  change name ∈ 4 :: _ at member
  rcases List.mem_cons.mp member with rfl | member
  · simp [pool]
  · change name ∈ [4] at member
    cases List.mem_singleton.mp member
    simp [pool]

theorem effect_support : GeneralDictionaryDefaultJournalSupport213.effectSources after effect ⊆ pool := by
  intro name member
  change name ∈ GeneralNominalHeadLedgerFrame182.headSources plan ++
    GeneralDictionaryDefaultModeEffects213.classSources start.core root plan ++
    GeneralDictionaryDefaultModeEffects213.classSources after.core root plan at member
  rcases List.mem_append.mp member with member | member
  · rcases List.mem_append.mp member with member | member
    · exact head_support member
    · exact class_support start.core (fun _ => GeneralDictionaryOptionalInstall229.request_exact) member
  · exact class_support after.core (fun _ => GeneralDictionaryUpper230Selected.request_exact) member

theorem journal_support : GeneralDictionaryDefaultJournalSupport213.journalSources after ⊆ pool := by
  intro name member
  simp only [GeneralDictionaryDefaultJournalSupport213.journalSources,List.mem_append] at member
  rcases member with ((((current | original) | rawSites) | sites) | packets) | effects
  · exact (show GeneralDictionaryDefaultRawSupport213.sources
      after.core.erased.current.context.state ⊆ pool by decide +kernel) current
  · exact (show GeneralDictionaryDefaultRawSupport213.sources
      after.core.erased.source.state ⊆ pool by decide +kernel) original
  · exact (show after.core.erased.current.sites.flatMap GeneralNominalCenteredEmptyFrame179.rawSiteSources ⊆ pool
      by decide +kernel) rawSites
  · exact (show after.core.sites.flatMap GeneralNominalCenteredFrame179.siteSources ⊆ pool
      by decide +kernel) sites
  · change name ∈ GeneralDictionaryDefaultPacketSupport213.packetSources plan ++ [] at packets
    exact packet_support (List.mem_append.mp packets |>.elim id (by intro impossible; cases impossible))
  · change name ∈ GeneralDictionaryDefaultJournalSupport213.effectSources after effect ++ [] at effects
    exact effect_support (List.mem_append.mp effects |>.elim id (by intro impossible; cases impossible))

end Yulang.GeneralDictionaryVersionedSupport231
