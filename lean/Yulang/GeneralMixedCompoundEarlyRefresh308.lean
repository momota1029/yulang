import Yulang.GeneralMixedCacheStatic308
import Yulang.GeneralMixedCompoundEarlyModels308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 18000
set_option maxHeartbeats 7500000
namespace Yulang.GeneralMixedCompoundEarlyRefresh308
open GeneralDictionaryJournalRefinement228Source (roles root snapshot)
open GeneralDictionaryCompoundSource238 (registry sourceRegistry)
open GeneralDictionaryCompoundFrame238 (installed)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralDictionaryCompoundBase239 (lo)
open GeneralMixedCompoundEarlyBase308 (looseSnap wideLoose looseContext refines known_iff)
open GeneralMixedCompoundUpperSnapshot307 (snap desc)
open GeneralMixedCompoundEarlyModels308 (old_zero old_one)
open GeneralMixedCompoundBatch307 (batch)
open GeneralMixedCacheStatic308 (Static cache)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound refresh_models)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralCanonicalObservations (Recorded)

noncomputable abbrev early := refresh installed looseContext

theorem static_point_installed : Static point installed :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem static_installed_early : Static installed early :=
  GeneralMixedCacheStatic308.from_refresh installed looseContext rfl

theorem cache_point : CacheSound installed snap :=
  cache static_point_installed batch.cache

theorem cache_loose : CacheSound installed looseSnap := by
  intro obs held
  cases held with
  | scalar slot n seen =>
    exact cache_point _ (Recorded.scalar (snapshot := snap) slot n seen)
  | structural slot k children seen =>
    exact cache_point _ (Recorded.structural (snapshot := snap) slot k children seen)
  | nominal slot d seen =>
    change (if slot = 0 then some wideLoose else if slot = 1 then some desc else none) = some d at seen
    by_cases zero : slot = 0
    · subst slot
      have same : wideLoose = d := Option.some.inj seen
      subst d
      exact ⟨[],[],.source,.source,fun m _ facts => old_zero m facts.1⟩
    · by_cases one : slot = 1
      · subst slot
        have same : desc = d := Option.some.inj seen
        subst d
        exact ⟨[],[],.source,.source,fun m _ facts => old_one m facts.1⟩
      · simp [zero,one] at seen

noncomputable def certificate : Refresh installed looseContext :=
  ⟨refines,rfl,batch.support,fun m valid =>
    batch.constraints m ((GeneralDictionaryCompoundPoint238.models_iff m).mpr valid),cache_loose⟩

theorem previously_unknown : ¬ GeneralNominalState.Known installed.core.erased.current.context.state lo := by
  intro h
  exact GeneralDictionaryCompoundRefreshStep239.lower_unknown
    ((GeneralNominalReobservationSteps.revision_known GeneralDictionaryCompoundPoint238.revision lo).mpr h)

theorem early_known : GeneralNominalState.Known looseSnap lo :=
  (known_iff lo).mpr GeneralMixedCompoundUpperSupport307.known_lo

theorem step : Step registry root installed early := by
  refine ⟨root,.root,.refresh root looseContext certificate lo ?_ previously_unknown early_known⟩
  exact GeneralDictionaryCompoundRefresh239.supported (5 : Fin 7) (by decide)

theorem models (m : GeneralNominalCommonBridge.Assignment) : Models early m ↔ Models installed m :=
  refresh_models certificate

theorem reachable : B4TargetV8.Reachable
    (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) sourceRegistry root early := by
  obtain ⟨s,init,prior⟩ := GeneralDictionaryCompoundStep238.reachable
  exact ⟨s,init,.tail prior step⟩

end Yulang.GeneralMixedCompoundEarlyRefresh308
