import Yulang.GeneralRebaseCompactTrust279

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebaseCompactInstallGuard279
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Models Effect)
open GeneralRebaseCompactEdgeInstall279 (replaceEdges models_exact aliases_exact requests_exact frame_exact classes_exact)
open GeneralRebaseCompactDiagnostics279 (safe_iff ready_iff)
open GeneralRebaseCompactLocal279 (safe_known)
open GeneralRebaseCompactTrust279 (cache_iff)
open GeneralRebaseInstallNovelty279 (Edge)
open GeneralNominalVersionedInstall232 (InstallationModels install installCore install_models LegacyLive)
open GeneralNominalVersionedChildren232 (edges)
open GeneralNominalVersionedMixedKernel234 (Installable AlternativesSafe)
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {state : State roles} {new : List (Edge roles)}
variable {registry : Registry} {e : Effect roles}

def reframe (e : Effect roles) (snapshot : e.snapshot = state.core) (new : List (Edge roles)) :
    Effect roles :=
  ⟨e.registry,(replaceEdges state new).core,e.plan,
    (frame_exact state new _ _ _ _).mpr (snapshot ▸ e.frame),
    (by
      change GeneralNominalVersionedCandidates231.Unique e.registry state.core.erased.current.context
        e.plan.packet.site.occurrence e.plan.packet.declaration.id
        (GeneralNominalVersionedFrame231.children e.plan.packet)
      exact snapshot ▸ e.unique),
    (ready_iff e.plan).mpr (snapshot ▸ e.ready)⟩

theorem reframe_holds (snapshot : e.snapshot = state.core) (m : Assignment) :
    (reframe e snapshot new).Holds m ↔ e.Holds m := by
  unfold Effect.Holds
  change (GeneralNominalVersionedPlans231.HeadModels e.plan.packet m ∧
    GeneralNominalVersionedEffects231.ClassEffects (replaceEdges state new).core e.plan.packet.site.occurrence e.plan m) ↔ _
  rw [classes_exact,snapshot]

theorem post_core (snapshot : e.snapshot = state.core) :
    (install (replaceEdges state new) (reframe e snapshot new)).core =
      (replaceEdges (install state e) (new ++ edges e.plan)).core := rfl

theorem post_versions (snapshot : e.snapshot = state.core) (old : Effect roles) (m : Assignment) :
    old.Live (installCore (replaceEdges state new).core (reframe e snapshot new).plan) m ↔
      old.Live (installCore state.core e.plan) m :=
  classes_exact (install state e) (new ++ edges e.plan) _ _ m

theorem post_legacy (snapshot : e.snapshot = state.core)
    (old : GeneralNominalCenteredHeadMatStepJournal.Effect roles) (m : Assignment) :
    old.Live (installCore (replaceEdges state new).core (reframe e snapshot new).plan) m ↔
      old.Live (installCore state.core e.plan) m := by
  apply Iff.trans (GeneralNominalVersionedEffects231.class_effects_iff ..).symm
  apply Iff.trans (classes_exact (install state e) (new ++ edges e.plan) _ _ m)
  exact GeneralNominalVersionedEffects231.class_effects_iff ..

theorem witnesses_iff (snapshot : e.snapshot = state.core) (m : Assignment) :
    InstallationModels (replaceEdges state new) (reframe e snapshot new) m ↔
      InstallationModels state e m := by
  have current :
      (reframe e snapshot new).Live (installCore (replaceEdges state new).core (reframe e snapshot new).plan) m ↔
        e.Live (installCore state.core e.plan) m := post_versions snapshot e m
  have legacy : LegacyLive (replaceEdges state new).legacy (reframe e snapshot new).plan m ↔
      LegacyLive state.legacy e.plan m := by
    unfold LegacyLive
    simp only [post_legacy snapshot]
    rfl
  unfold InstallationModels
  simp only [models_exact,reframe_holds,current,legacy,post_versions snapshot]
  rfl

theorem target_models (snapshot : e.snapshot = state.core) (m : Assignment) :
    Models (install (replaceEdges state new) (reframe e snapshot new)) m ↔
      Models (install state e) m :=
  (install_models rfl).trans ((witnesses_iff snapshot m).trans (install_models snapshot).symm)

theorem choice_iff (p : Plan roles) :
    GeneralNominalCycleSteps.ChoiceCompatible (replaceEdges state new).core.erased.current p.packet ↔
      GeneralNominalCycleSteps.ChoiceCompatible state.core.erased.current p.packet := by
  unfold GeneralNominalCycleSteps.ChoiceCompatible
  simp only [aliases_exact]
  rfl

theorem alternatives_iff (input : Site roles) :
    AlternativesSafe registry (replaceEdges state new) input ↔ AlternativesSafe registry state input := by
  unfold AlternativesSafe
  simp only [frame_exact,safe_iff]

theorem enabled_iff (snapshot : e.snapshot = state.core) :
    Installable registry (replaceEdges state new) (reframe e snapshot new) ↔ Installable registry state e := by
  constructor <;> intro h
  · exact ⟨h.registry_eq,snapshot,safe_known.mp h.safe,(cache_iff _).mp h.cache,h.materialized,
      (choice_iff e.plan).mp h.choice,(safe_iff e.plan).mp h.positions,
      (alternatives_iff _).mp h.alternatives,by
        obtain ⟨m,valid⟩ := h.common
        exact ⟨m,(witnesses_iff snapshot m).mp valid⟩⟩
  · exact ⟨h.registry_eq,rfl,safe_known.mpr h.safe,(cache_iff _).mpr h.cache,h.materialized,
      (choice_iff e.plan).mpr h.choice,(safe_iff e.plan).mpr h.positions,
      (alternatives_iff _).mpr h.alternatives,by
        obtain ⟨m,valid⟩ := h.common
        exact ⟨m,(witnesses_iff snapshot m).mpr valid⟩⟩

end Yulang.GeneralRebaseCompactInstallGuard279
