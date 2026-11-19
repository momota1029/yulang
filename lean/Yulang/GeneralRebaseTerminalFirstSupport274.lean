import Yulang.GeneralRebaseSemanticSupport274

set_option maxRecDepth 20000
set_option maxHeartbeats 6600000
namespace Yulang.GeneralRebaseTerminalFirstSupport274
open GeneralDictionaryVersionedSecondRaw233 (oldLo oldHi)
open GeneralDictionaryOptionalInstall229 (actual)
open GeneralDictionaryJournalRefinement228Source (root snapshot roles)
open GeneralRebaseTerminalRowFrame274 (oldPlan)
open GeneralRebaseTerminalPublic274 (first)
open GeneralRebaseTerminalFreshSupport274 (first_raw_sites first_sites)
open GeneralNominalVersionedJournalFrame236 (sources effectSources)
open GeneralDictionaryDefaultJournalSupport213 (journalSources)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)
open GeneralNominalCenteredSteps (State)

def pool : List Nat := [0,1,2,3,4,actual,oldLo,oldHi]

theorem join {xs ys : List Nat} (a : xs ⊆ pool) (b : ys ⊆ pool) : xs ++ ys ⊆ pool :=
 fun _ member => (List.mem_append.mp member).elim (fun h => a h) (fun h => b h)

theorem raw : GeneralDictionaryDefaultRawSupport213.sources first.core.erased.current.context.state ⊆ pool := by decide +kernel

theorem source : GeneralDictionaryDefaultRawSupport213.sources snapshot ⊆ pool := by decide +kernel

theorem legacy : journalSources first.legacy ⊆ pool := by
 unfold journalSources
 rw [show first.legacy.core.erased.source.state = snapshot from rfl,
     first_raw_sites,first_sites,show first.core.plans = [] from rfl,show first.legacy.effects = [] from rfl]
 have sites :
   [GeneralNominalDemandMerging.pointSite root].flatMap GeneralNominalCenteredEmptyFrame179.rawSiteSources ++
   [GeneralNominalCenters.rootSite snapshot.seed root].flatMap GeneralNominalCenteredFrame179.siteSources ⊆ pool := by
    decide +kernel
 simpa only [List.flatMap_nil,List.append_nil,List.append_assoc] using join raw (join source sites)

theorem plan_reads : GeneralNominalVersionedPacketFrame236.sources oldPlan ⊆ pool := by decide +kernel

theorem classes (s : State roles) (sites : s.erased.current.sites = [GeneralNominalDemandMerging.pointSite root]) :
 classSources s root oldPlan ⊆ pool := by
 intro id read
 obtain ⟨out,requested,contains⟩ := List.mem_flatMap.mp read
 obtain ⟨site,present,_,member⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp requested
 rw [sites] at present
 cases List.mem_singleton.mp present
 have found : out = ⟨0,4⟩ := List.mem_singleton.mp member
 cases found
 change id ∈ [4,4] at contains
 have same : id = 4 := by simpa using contains
 simp [same,pool]

theorem effect : effectSources first GeneralDictionaryVersionedInitialFrame233.effect ⊆ pool := by
 apply join
 · apply join
   · change GeneralNominalVersionedPacketFrame236.headSources oldPlan.packet ⊆ pool
     decide +kernel
   · exact classes _ rfl
 · exact classes _ first_raw_sites

theorem complete : sources first ⊆ pool := by
 unfold sources
 change (journalSources first.legacy ++
   [GeneralNominalVersionedPacketFrame236.sources oldPlan].flatten) ++
   [effectSources first GeneralDictionaryVersionedInitialFrame233.effect].flatten ⊆ pool
 simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using join (join legacy plan_reads) effect

end Yulang.GeneralRebaseTerminalFirstSupport274
