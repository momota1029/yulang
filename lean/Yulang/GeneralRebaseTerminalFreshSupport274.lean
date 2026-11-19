import Yulang.GeneralRebaseTerminalPointExact274

set_option maxRecDepth 22000
set_option maxHeartbeats 7400000
namespace Yulang.GeneralRebaseTerminalFreshSupport274
open GeneralDictionaryVersionedSecondRaw233 (newLo newHi)
open GeneralDictionaryJournalRefinement228Source (snapshot root roles)
open GeneralDictionaryVersionedPointStage233 (point)
open GeneralRebaseTerminalPublic274 (first)
open GeneralRebaseTerminalRowFrame274 (oldPlan)
open GeneralNominalVersionedJournalFrame236 (sources effectSources)
open GeneralDictionaryDefaultJournalSupport213 (journalSources)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)
open GeneralNominalCenteredSteps (State)

def Fresh (xs : List Nat) : Prop := newLo ∉ xs ∧ newHi ∉ xs

theorem fresh_append {xs ys : List Nat} (left : Fresh xs) (right : Fresh ys) : Fresh (xs ++ ys) := by
 constructor <;> intro h
 · exact (List.mem_append.mp h).elim left.1 right.1
 · exact (List.mem_append.mp h).elim left.2 right.2

theorem first_raw_sites : first.core.erased.current.sites = [GeneralNominalDemandMerging.pointSite root] := by
 change (GeneralNominalVersionedInstall232.installCore GeneralDictionaryVersionedInitialFrame233.before.core oldPlan).erased.current.sites = _
 rw [GeneralNominalVersionedTerminal232.raw_eq GeneralDictionaryVersionedInitialFrame233.children_empty]
 rfl

theorem first_sites : first.core.sites = [GeneralNominalCenters.rootSite snapshot.seed root] := by
 change (GeneralNominalVersionedInstall232.installCore GeneralDictionaryVersionedInitialFrame233.before.core oldPlan).sites = _
 rw [GeneralNominalVersionedTerminal232.sites_eq GeneralDictionaryVersionedInitialFrame233.children_empty]
 rfl

theorem first_raw : Fresh (GeneralDictionaryDefaultRawSupport213.sources first.core.erased.current.context.state) := by
 unfold Fresh
 decide +kernel

theorem snapshot_raw : Fresh (GeneralDictionaryDefaultRawSupport213.sources snapshot) := by
 unfold Fresh
 decide +kernel

theorem first_legacy : Fresh (journalSources first.legacy) := by
 unfold journalSources
 rw [show first.legacy.core.erased.source.state = snapshot from rfl,
     first_raw_sites,first_sites,show first.core.plans = [] from rfl,show first.legacy.effects = [] from rfl]
 have sites : Fresh ([GeneralNominalDemandMerging.pointSite root].flatMap GeneralNominalCenteredEmptyFrame179.rawSiteSources ++
    [GeneralNominalCenters.rootSite snapshot.seed root].flatMap GeneralNominalCenteredFrame179.siteSources) := by
   unfold Fresh
   decide +kernel
 simpa only [List.flatMap_nil,List.append_nil,List.append_assoc] using fresh_append first_raw (fresh_append snapshot_raw sites)

theorem plan : Fresh (GeneralNominalVersionedPacketFrame236.sources oldPlan) := by
 unfold Fresh
 decide +kernel

theorem head : Fresh (GeneralNominalVersionedPacketFrame236.headSources oldPlan.packet) := by
 unfold Fresh
 decide +kernel

theorem class_singleton (s : State roles)
 (sites : s.erased.current.sites = [GeneralNominalDemandMerging.pointSite root]) :
 Fresh (classSources s root oldPlan) := by
 have only (id : Nat) (read : id ∈ classSources s root oldPlan) : id = 4 := by
   obtain ⟨output,request,contains⟩ := List.mem_flatMap.mp read
   obtain ⟨site,member,_,out⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp request
   rw [sites] at member
   cases List.mem_singleton.mp member
   have outEq : output = ⟨0,4⟩ := List.mem_singleton.mp out
   cases outEq
   change id ∈ [4,4] at contains
   simpa using contains
 constructor
 · intro h
   exact (by decide +kernel : newLo ≠ 4) (only _ h)
 · intro h
   exact (by decide +kernel : newHi ≠ 4) (only _ h)

theorem effect : Fresh (effectSources first GeneralDictionaryVersionedInitialFrame233.effect) :=
 fresh_append (fresh_append head (class_singleton _ rfl)) (class_singleton _ first_raw_sites)

theorem first_support : Fresh (sources first) := by
 unfold sources
 change Fresh ((journalSources first.legacy ++
   [GeneralNominalVersionedPacketFrame236.sources oldPlan].flatten) ++
     [effectSources first GeneralDictionaryVersionedInitialFrame233.effect].flatten)
 simpa only [List.flatten_cons,List.flatten_nil,List.append_nil] using
   fresh_append (fresh_append first_legacy plan) effect

end Yulang.GeneralRebaseTerminalFreshSupport274
