import Yulang.GeneralRebaseTerminalStableCells274
import Yulang.GeneralRebaseCompoundOwnerCapture273

set_option maxRecDepth 23000
set_option maxHeartbeats 7500000
namespace Yulang.GeneralRebaseTerminalTypePool274
open CommonNominalFullCarrier
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralDictionaryDefaultJournalSupport213 (journalSources)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)
open GeneralNominalVersionedPacketFrame236 (headSources)
open GeneralNominalCenteredSteps (State)
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralDictionaryOptionalInitial229 (declaration)
open GeneralDictionaryVersionedSecondInstall233 (installed)
open GeneralRebaseTerminalRowFrame274 (oldPlan newPlan)
open GeneralDictionaryOptionalInstall229 (actual)
open GeneralDictionaryVersionedSecondRaw233 (oldLo oldHi newLo newHi raw_old raw_new)
open GeneralRebaseTerminalStableSupport274 (terminal_raw_sites)

def pool : List Nat := [0,1,2,3,4,actual,oldLo,oldHi,newLo,newHi]

theorem pair_subset {a b : List Nat} (one : a ⊆ pool) (two : b ⊆ pool) : a ++ b ⊆ pool :=
 fun _ h => (List.mem_append.mp h).elim (fun ha => one ha) (fun hb => two hb)

theorem terminal_map : GeneralDictionaryDefaultRawSupport213.sources installed.core.erased.current.context.state ⊆ pool := by decide +kernel

theorem source_map : GeneralDictionaryDefaultRawSupport213.sources snapshot ⊆ pool := by decide +kernel

theorem terminal_legacy : journalSources installed.legacy ⊆ pool := by
 unfold journalSources
 rw [show installed.legacy.core.erased.source.state = snapshot from rfl,
     terminal_raw_sites,GeneralDictionaryVersionedSecondRefresh233.sites,
     GeneralRebaseTerminalPublic274.final_legacy_empty.1,GeneralRebaseTerminalPublic274.final_legacy_empty.2]
 have support :
   [GeneralNominalDemandMerging.pointSite root].flatMap GeneralNominalCenteredEmptyFrame179.rawSiteSources ++
   [GeneralNominalCenters.rootSite snapshot.seed root].flatMap GeneralNominalCenteredFrame179.siteSources ⊆ pool := by
    decide +kernel
 simpa only [List.flatMap_nil,List.append_nil,List.append_assoc] using
   pair_subset terminal_map (pair_subset source_map support)

theorem plans : installed.plans.flatMap GeneralNominalVersionedPacketFrame236.sources ⊆ pool := by
 change [newPlan,oldPlan].flatMap GeneralNominalVersionedPacketFrame236.sources ⊆ pool
 decide +kernel

theorem classes (s : State roles) (p : GeneralNominalCenters.Plan roles)
 (sites : s.erased.current.sites = [GeneralNominalDemandMerging.pointSite root])
 (decl : p.packet.declaration = declaration) : classSources s root p ⊆ pool := by
 intro id member
 obtain ⟨out,request,within⟩ := List.mem_flatMap.mp member
 obtain ⟨site,mem,_,found⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp request
 rw [sites] at mem
 cases List.mem_singleton.mp mem
 have only : out = ⟨0,4⟩ := List.mem_singleton.mp found
 cases only
 change id ∈ 4 :: ((GeneralDictionaryAssociatedProvenance.lookup roles p.packet.declaration 0).toList.flatMap _) at within
 rw [decl] at within
 change id ∈ [4,4] at within
 exact (show id = 4 by simpa using within) ▸ (by simp [pool])

theorem effects : installed.effects.flatMap (GeneralNominalVersionedJournalFrame236.effectSources installed) ⊆ pool := by
 change [GeneralDictionaryVersionedSecondInstall233.effect,GeneralDictionaryVersionedInitialFrame233.effect].flatMap _ ⊆ pool
 apply pair_subset
 · apply pair_subset
   · apply pair_subset
     · change headSources newPlan.packet ⊆ pool
       decide +kernel
     · exact classes _ _ GeneralDictionaryVersionedPointStage233.raw_sites rfl
   · exact classes _ _ terminal_raw_sites rfl
 · change (GeneralNominalVersionedJournalFrame236.effectSources installed GeneralDictionaryVersionedInitialFrame233.effect ++ []) ⊆ pool
   rw [List.append_nil]
   apply pair_subset
   · apply pair_subset
     · change headSources oldPlan.packet ⊆ pool
       decide +kernel
     · exact classes _ _ rfl rfl
   · exact classes _ _ terminal_raw_sites rfl

theorem covered : sources installed ⊆ pool := pair_subset (pair_subset terminal_legacy plans) effects

theorem actual_width (m : Assignment) (valid : Models installed m) :
 Equivalent (m actual).1 (m 2).1 := by
 have first := GeneralRebaseTerminalPublic274.final_to_first m valid
 have held := first.2.1 oldPlan (List.mem_cons_self ..)
 have schema : oldPlan.headSchema = GeneralDictionaryCompoundPacket238.plan.headSchema := by
   rw [GeneralDictionaryOptionalInstall229.head_schema,GeneralDictionaryCompoundPacket238.head_schema]
 have exact := GeneralRebaseCompoundOwnerCapture273.actual_is_width m oldPlan held.1 schema held.2.1.2.2.2.2.1
 rwa [GeneralNominalVersionedFrame231.binder_eq,GeneralDictionaryOptionalInstall229.binder_exact] at exact

end Yulang.GeneralRebaseTerminalTypePool274
