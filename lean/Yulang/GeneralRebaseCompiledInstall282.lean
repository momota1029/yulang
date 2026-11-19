import Yulang.GeneralRebaseProspective282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseCompiledInstall282
open GeneralDeclarations GeneralSourceDictionaries
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedProgressSplit236 (Reachable reachable_step)
open GeneralNominalVersionedMixedKernel234 (Installable At Committed AlternativesSafe)
open GeneralNominalVersionedInstall232 (install InstallationModels)
open GeneralRebaseProspective282 (Compiled decoded acceptance_before empty_install)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalSaturationState (Generated)
open GeneralRebaseLiveStore282 (live live_private copy_live)
open GeneralRebaseTermCopy281 (Copy Respects)
open GeneralRebasePrivateStore282 (copy_outside)
open GeneralNominalCommonBridge (Assignment)

variable {roles : Roles.RoleDecls} {r : Registry} {root : Occurrence roles}
  {before after : State roles} {e : Effect roles}

structure Setup (r : Registry) (before : State roles) (e : Effect roles) : Prop where
  registry_eq : e.registry = registry r
  snapshot_eq : e.snapshot = before.core
  safe : B4TargetV8.SafeKnown (GeneralNominalVersionedDiagnostic232.boundary roles) (registry r) before
    e.plan.packet.site.occurrence
  cache : GeneralNominalVersionedMixedObservations233.CacheSound before before.core.erased.current.context.state
  materialized : (GeneralNominalVersionedPlans231.emittedSchema e.plan).unknown = false
  choice : GeneralNominalCycleSteps.ChoiceCompatible before.core.erased.current e.plan.packet
  positions : GeneralNominalVersionedCycles232.Safe before e.plan
  alternatives : AlternativesSafe (registry r) before e.plan.input

theorem setup (enabled : Installable (registry r) before e) : Setup r before e :=
  ⟨enabled.registry_eq,enabled.snapshot_eq,enabled.safe,enabled.cache,enabled.materialized,
    enabled.choice,enabled.positions,enabled.alternatives⟩

theorem add_common (other : Setup r before e) (common : ∃ a, InstallationModels before e a) :
    Installable (registry r) before e :=
  ⟨other.registry_eq,other.snapshot_eq,other.safe,other.cache,other.materialized,other.choice,
    other.positions,other.alternatives,common⟩

theorem compiled_at (reach : Reachable r root before) (fields : Setup r before e) :
    Installable (registry r) before e ↔ ∃ a, Compiled (install before e) a :=
  ⟨fun ready => (acceptance_before reach fields.snapshot_eq).mpr ready.common,
    fun found => add_common fields ((acceptance_before reach fields.snapshot_eq).mp found)⟩

theorem model_invariant (reach : Reachable r root before) {a b : Assignment}
    (same : GeneralRebasePrivateJournal282.AgreeOutside (GeneralRebaseMixedOwnedTrace277.raw before).seed a b) :
    Compiled before a ↔ Compiled before b := by
  have empty := GeneralNominalVersionedMixedRegistry234.reachable_legacy_empty reach
  exact (decoded empty a).trans ((GeneralRebasePrivateJournal282.models_iff reach
    (GeneralRebaseHistorySupport282.decode_agrees reach same)).trans (decoded empty b).symm)

theorem table_at (reach : Reachable r root before) (fields : Setup r before e)
    (source : Generated before.core.erased.current root e.plan.packet.site.occurrence)
    (novel : ¬ Committed before e.plan) :
    Installable (registry r) before e ↔
      ∃ a, Compiled (install before e) a ∧ Respects (live (install before e)) a := by
  constructor
  · intro enabled
    have reached : Reachable r root (install before e) :=
      reachable_step reach ⟨_,source,.install e enabled novel⟩
    obtain ⟨a,compiled⟩ := (compiled_at reach fields).mp enabled
    exact ⟨Copy (live (install before e)) a,
      (model_invariant reached (copy_outside (live_private reached) a)).mp compiled,
      copy_live reached a⟩
  · rintro ⟨a,good,_⟩
    exact (compiled_at reach fields).mpr ⟨a,good⟩

def OldInstall (r : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ e, Generated before.core.erased.current root e.plan.packet.site.occurrence ∧
    Installable (registry r) before e ∧ ¬ Committed before e.plan ∧ after = install before e

def NewInstall (r : Registry) (root : Occurrence roles) (before after : State roles) : Prop :=
  ∃ e, Generated before.core.erased.current root e.plan.packet.site.occurrence ∧
    Setup r before e ∧ ¬ Committed before e.plan ∧ after = install before e ∧
    ∃ a, Compiled after a ∧ Respects (live after) a

theorem same_install (reaches : Reachable r root before) :
    NewInstall r root before after ↔ OldInstall r root before after := by
  constructor
  · rintro ⟨e,source,checked,novel,rfl,models⟩
    exact ⟨e,source,(table_at reaches checked source novel).mpr models,novel,rfl⟩
  · rintro ⟨e,source,enabled,novel,rfl⟩
    exact ⟨e,source,setup enabled,novel,rfl,(table_at reaches (setup enabled) source novel).mp enabled⟩

end Yulang.GeneralRebaseCompiledInstall282
