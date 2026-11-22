import Yulang.GeneralDeclarativeCurrentTrace345
import Yulang.GeneralDeclarativeStoppedOrder339

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentHistory345
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary checked_compiled)
open GeneralNominalVersionedMixedKernel234 (Step)
open GeneralNominalCenteredHeadMatEffects (Ready ready_of_wf)
open GeneralNominalCenteredHeadDefaultSchemas (RequestsDeclared)
open GeneralStoppedInstallHistory335 (InstalledBetween installed_origin)
open GeneralNominalCenteredHeadAllocEncoding (registry)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalCommonBridge (Assignment)
open B4Target (Steps)

theorem after_historical_install {r : Registry} {root : Occurrence rs}
    {start final : State rs} {e : Effect rs}
    (checked : (boundary rs).Checked r)
    (reachable : B4TargetV8.Reachable (boundary rs) r root final)
    (came : InstalledBetween (registry r) root start final e) :
    RequestsDeclared final.core e.plan.packet.site.occurrence e.plan ∧
    Ready final.core e.plan.packet.site.occurrence e.plan := by
  obtain ⟨before,_,live,enabled,novel,later⟩ := came
  let original : Step (registry r) root before (install before e) := ⟨_,live,.install e enabled novel⟩
  have beforeToFinal := GeneralNominalVersionedMixedGrowth234.trans (GeneralNominalVersionedMixedGrowth234.step original)
    (GeneralNominalVersionedMixedGrowth234.steps later)
  have sameRegistry : e.plan.packet.registry = registry r := e.frame.registry_eq.trans enabled.registry_eq
  have interp : e.plan.packet.context.interpretation = final.core.erased.current.context.interpretation := by
    rw [e.frame.context_eq,enabled.snapshot_eq,beforeToFinal.interpretation]
  have begun : e.plan.packet.site ∈ before.core.erased.current.sites := by
    simpa only [enabled.snapshot_eq] using e.frame.raw_recorded
  have physical : e.plan.packet.site ∈ final.core.erased.current.sites := beforeToFinal.legacy.rawSites begun
  have shape := GeneralNominalVersionedMixedRoles235.reachable checked reachable
  have declared := GeneralDeclarativeCurrentRequest345.declared (p := e.plan) (checked_compiled checked).2
    shape (shape.raw _ physical) e.frame.role_eq
  refine ⟨declared,ready_of_wf ?_ ?_ ?_ declared⟩
  · rw [sameRegistry,interp]
    exact GeneralNominalVersionedMixedReady235.coverage reachable
  · rw [e.frame.registry_eq]
    exact e.frame.visible
  · rw [sameRegistry]
    exact checked.1

theorem initially_empty {r : Registry} {root : Occurrence rs} {start : State rs}
    (h : (boundary rs).Initial r root start) :
    start.effects = [] := by
  obtain ⟨legacy,_,rfl⟩ := h
  rfl

theorem retained_ready {r : Registry} {root : Occurrence rs}
    {final : State rs} {e : Effect rs}
    (checked : (boundary rs).Checked r)
    (reachable : B4TargetV8.Reachable (boundary rs) r root final)
    (retained : e ∈ final.effects) :
    RequestsDeclared final.core e.plan.packet.site.occurrence e.plan ∧
    Ready final.core e.plan.packet.site.occurrence e.plan := by
  obtain ⟨start,h,path⟩ := reachable
  exact after_historical_install checked ⟨start,h,path⟩ (installed_origin path (initially_empty h) retained)

end Yulang.GeneralDeclarativeCurrentHistory345
