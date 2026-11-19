import Yulang.GeneralRebaseTerminalBridge274
import Yulang.GeneralNominalVersionedJournalFrame236

set_option maxRecDepth 22000
set_option maxHeartbeats 8000000
namespace Yulang.GeneralRebaseTerminalStableSupport274
open GeneralDictionaryOptionalInstall229 (lo hi)
open GeneralDictionaryJournalRefinement228Source (snapshot root roles)
open GeneralDictionaryVersionedSecondInstall233 (installed terminal)
open GeneralRebaseTerminalRowFrame274 (oldPlan newPlan)
open GeneralNominalVersionedJournalFrame236 (sources)
open GeneralDictionaryDefaultJournalSupport213 (journalSources)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)
open GeneralNominalVersionedPacketFrame236 (headSources)
open GeneralNominalCenteredSteps (State)

def unused (pool : List Nat) : Prop := lo ∉ pool ∧ hi ∉ pool

theorem combine {a b : List Nat} (left : unused a) (right : unused b) : unused (a ++ b) := by
 constructor <;> intro h
 · exact (List.mem_append.mp h).elim left.1 right.1
 · exact (List.mem_append.mp h).elim left.2 right.2

theorem terminal_raw_sites : installed.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] := by
 change (GeneralNominalVersionedInstall232.installCore GeneralDictionaryVersionedPointStage233.point.core newPlan).erased.current.sites = _
 rw [GeneralNominalVersionedTerminal232.raw_eq terminal]
 exact GeneralDictionaryVersionedPointStage233.raw_sites

theorem source_map : unused (GeneralDictionaryDefaultRawSupport213.sources snapshot) := by unfold unused; decide +kernel

theorem terminal_map : unused (GeneralDictionaryDefaultRawSupport213.sources installed.core.erased.current.context.state) := by unfold unused; decide +kernel

theorem terminal_legacy : unused (journalSources installed.legacy) := by
 unfold journalSources
 rw [show installed.legacy.core.erased.source.state = snapshot from rfl,
     terminal_raw_sites,GeneralDictionaryVersionedSecondRefresh233.sites,
     GeneralRebaseTerminalPublic274.final_legacy_empty.1,GeneralRebaseTerminalPublic274.final_legacy_empty.2]
 have neither : unused
   ([GeneralNominalDemandMerging.pointSite root].flatMap GeneralNominalCenteredEmptyFrame179.rawSiteSources ++
     [GeneralNominalCenters.rootSite snapshot.seed root].flatMap GeneralNominalCenteredFrame179.siteSources) := by unfold unused; decide +kernel
 simpa only [List.flatMap_nil,List.append_nil,List.append_assoc] using combine terminal_map (combine source_map neither)

theorem plans_unused : unused (installed.plans.flatMap GeneralNominalVersionedPacketFrame236.sources) := by
 change unused ([newPlan,oldPlan].flatMap GeneralNominalVersionedPacketFrame236.sources)
 unfold unused
 decide +kernel

theorem unused_classes (s : State roles) (p : GeneralNominalCenters.Plan roles)
 (pointOnly : s.erased.current.sites = [GeneralNominalDemandMerging.pointSite root])
 (declaration : p.packet.declaration = GeneralDictionaryOptionalInitial229.declaration) :
 unused (classSources s root p) := by
 have req (out : GeneralSourceState.Output) (h : out ∈ GeneralNominalCenteredHeadOutputs.requests s root) :
   out = ⟨0,4⟩ := by
   obtain ⟨site,mem,_,found⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp h
   rw [pointOnly] at mem
   cases List.mem_singleton.mp mem
   exact List.mem_singleton.mp found
 have only (id : Nat) (member : id ∈ classSources s root p) : id = 4 := by
   obtain ⟨out,mem,supported⟩ := List.mem_flatMap.mp member
   cases req out mem
   change id ∈ 4 :: ((GeneralDictionaryAssociatedProvenance.lookup roles p.packet.declaration 0).toList.flatMap _) at supported
   rw [declaration] at supported
   change id ∈ [4,4] at supported
   simpa using supported
 constructor
 · intro used
   have value := only lo used
   have greater : 4 < lo := GeneralDictionaryOptionalInstall229.fresh_large 0
   omega
 · intro used
   have value := only hi used
   have greater : 4 < hi := GeneralDictionaryOptionalInstall229.fresh_large 1
   omega

theorem effects_unused : unused (installed.effects.flatMap (GeneralNominalVersionedJournalFrame236.effectSources installed)) := by
 change unused ([GeneralDictionaryVersionedSecondInstall233.effect,GeneralDictionaryVersionedInitialFrame233.effect].flatMap _)
 apply combine
 · apply combine
   · apply combine
     · change unused (headSources newPlan.packet)
       unfold unused
       decide +kernel
     · exact unused_classes _ _ GeneralDictionaryVersionedPointStage233.raw_sites rfl
   · exact unused_classes _ _ terminal_raw_sites rfl
 · change unused (GeneralNominalVersionedJournalFrame236.effectSources installed GeneralDictionaryVersionedInitialFrame233.effect ++ [])
   rw [List.append_nil]
   apply combine
   · apply combine
     · change unused (headSources oldPlan.packet)
       unfold unused
       decide +kernel
     · exact unused_classes _ _ rfl rfl
   · exact unused_classes _ _ terminal_raw_sites rfl

theorem terminal_hidden : unused (sources installed) :=
 combine (combine terminal_legacy plans_unused) effects_unused

end Yulang.GeneralRebaseTerminalStableSupport274
