import Yulang.GeneralNominalVersionedMixedCache233
import Yulang.GeneralNominalVersionedRefresh232

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralMixedCacheStatic308
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalSaturationState (Alias)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedObservations233 (Justified CacheSound)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenters (SameInputs)

structure Static (s t : State roles) : Prop where
  source : s.core.erased.source = t.core.erased.source
  sourceSites : s.core.sourceSites = t.core.sourceSites
  rawSites : s.core.erased.current.sites = t.core.erased.current.sites
  packets : s.core.erased.current.packets = t.core.erased.current.packets
  aliases : s.core.erased.current.aliases = t.core.erased.current.aliases
  centers : s.core.sites = t.core.sites
  legacyPlans : s.core.plans = t.core.plans
  legacyEffects : s.legacy.effects = t.legacy.effects
  plans : s.plans = t.plans
  effects : s.effects = t.effects
  ordinary : s.core.erased.current.context.state.ordinary = t.core.erased.current.context.state.ordinary

variable {roles : Roles.RoleDecls} {s t : State roles}

theorem reverse (h : Static s t) : Static t s :=
  ⟨h.source.symm,h.sourceSites.symm,h.rawSites.symm,h.packets.symm,h.aliases.symm,h.centers.symm,
    h.legacyPlans.symm,h.legacyEffects.symm,h.plans.symm,h.effects.symm,h.ordinary.symm⟩

theorem from_refresh (s : State roles) (ctx : GeneralNominalCandidates.Context)
    (atoms : s.core.erased.current.context.state.ordinary = ctx.state.ordinary) :
    Static s (refresh s ctx) :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,atoms⟩

theorem alias (h : Static s t) (a : Alias s.core.erased.current x y) :
    Alias t.core.erased.current x y := by
  induction a with
  | refl => exact .refl _
  | edge mem => exact .edge (h.aliases ▸ mem)
  | symm _ ih => exact .symm ih
  | trans _ _ one two => exact .trans one two

theorem legacy_done (h : Static s t) (d : GeneralNominalSupport.Discharged s.core.erased.current focus) :
    GeneralNominalSupport.Discharged t.core.erased.current focus := by
  induction d with
  | packet p mem _ ih => exact .packet p (h.packets ▸ mem) ih
  | alias a b one two al _ ih => exact .alias a b (h.rawSites ▸ one) (h.rawSites ▸ two) (alias h al) ih

theorem versioned_done (h : Static s t) (d : GeneralNominalVersionedSupport233.Discharged s focus) :
    GeneralNominalVersionedSupport233.Discharged t focus := by
  induction d with
  | packet p mem _ ih => exact .packet p (h.plans ▸ mem) ih
  | alias a b one two al _ ih => exact .alias a b (h.rawSites ▸ one) (h.rawSites ▸ two) (alias h al) ih

theorem legacy_models (h : Static s t) (facts : List (GeneralNominalCenteredHeadMatStepSupport.Fact roles)) :
    GeneralNominalCenteredHeadMatStepSupport.Models s.legacy facts =
      GeneralNominalCenteredHeadMatStepSupport.Models t.legacy facts := by
  funext m
  unfold GeneralNominalCenteredHeadMatStepSupport.Models
  rw [h.source,h.sourceSites]

theorem versioned_models (h : Static s t) (facts : List (GeneralNominalVersionedSupport233.Fact roles)) :
    GeneralNominalVersionedSupport233.SliceModels s facts = GeneralNominalVersionedSupport233.SliceModels t facts := by
  funext m
  unfold GeneralNominalVersionedSupport233.SliceModels
  rw [h.source,h.sourceSites]

theorem legacy (h : Static s t) (used : GeneralNominalCenteredHeadMatStepSupport.Trusted s.legacy facts) :
    GeneralNominalCenteredHeadMatStepSupport.Trusted t.legacy facts := by
  induction used with
  | source => exact .source
  | input p _ mem read ih =>
    refine GeneralNominalCenteredHeadMatStepSupport.Trusted.input p ih (h.legacyPlans ▸ mem) ?_
    unfold GeneralNominalCenteredHeadMatStepSupport.Readback at read ⊢
    rwa [legacy_models h] at read
  | output e _ mem listed input read settled ih =>
    refine GeneralNominalCenteredHeadMatStepSupport.Trusted.output e ih (h.legacyEffects ▸ mem) (h.legacyPlans ▸ listed) input ?_
      ⟨h.packets ▸ settled.1,fun _ present => legacy_done h (settled.2 _ present)⟩
    unfold GeneralNominalCenteredHeadMatStepSupport.ClassReadback at read ⊢
    rwa [legacy_models h] at read
  | merge a b _ one two al atoms witnessed same ih =>
    refine GeneralNominalCenteredHeadMatStepSupport.Trusted.merge a b ih (h.centers ▸ one) (h.centers ▸ two) (alias h al) ?_ ?_ ?_
    · intro atom mem; exact h.ordinary ▸ atoms atom mem
    · rwa [legacy_models h] at witnessed
    · rwa [legacy_models h] at same

theorem versioned (h : Static s t) (used : GeneralNominalVersionedSupport233.Trusted s facts) :
    GeneralNominalVersionedSupport233.Trusted t facts := by
  induction used with
  | source => exact .source
  | input p _ mem read ih =>
    refine GeneralNominalVersionedSupport233.Trusted.input p ih (h.plans ▸ mem) ?_
    unfold GeneralNominalVersionedSupport233.Readback at read ⊢
    rwa [versioned_models h] at read
  | output e _ mem listed input read settled ih =>
    refine GeneralNominalVersionedSupport233.Trusted.output e ih (h.effects ▸ mem) (h.plans ▸ listed) input ?_
      ⟨h.plans ▸ settled.1,fun _ present => versioned_done h (settled.2 _ present)⟩
    unfold GeneralNominalVersionedSupport233.ClassReadback at read ⊢
    rwa [versioned_models h] at read
  | merge a b _ one two al atoms witnessed same ih =>
    refine GeneralNominalVersionedSupport233.Trusted.merge a b ih (h.centers ▸ one) (h.centers ▸ two) (alias h al) ?_ ?_ ?_
    · intro atom mem; exact h.ordinary ▸ atoms atom mem
    · rwa [versioned_models h] at witnessed
    · rwa [versioned_models h] at same

theorem justified (h : Static s t) (used : Justified s obs) : Justified t obs := by
  obtain ⟨older,newer,oldTrust,newTrust,sound⟩ := used
  refine ⟨older,newer,legacy h oldTrust,versioned h newTrust,?_⟩
  rwa [legacy_models h,versioned_models h] at sound

theorem cache (h : Static s t) (used : CacheSound s snap) : CacheSound t snap :=
  fun o found => justified h (used o found)

theorem cache_iff (h : Static s t) : CacheSound s snap ↔ CacheSound t snap :=
  ⟨cache h,cache (reverse h)⟩

end Yulang.GeneralMixedCacheStatic308
