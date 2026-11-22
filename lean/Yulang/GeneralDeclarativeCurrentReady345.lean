import Yulang.GeneralDeclarativeCurrentSeed345
import Yulang.GeneralDeclarativeCurrentRequest345
import Yulang.GeneralDeclarativePackageBoundary344

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeCurrentReady345
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepRoles (Origin Invariant)
open GeneralWhereVersionInstall317 (Journal install InstallStep Models)
open GeneralVersionedHistoryEvidence310 (Compiled)
open GeneralNominalVersionedEvidence231 (Frame)
open GeneralNominalCenteredHeadWFSource (Coverage)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary checked_compiled)
open GeneralNominalCenteredHeadMatEffects (Ready ready_of_wf)
open GeneralNominalCenteredHeadDefaultSchemas (RequestsDeclared)
open GeneralNominalCommonBridge (Assignment)

theorem after_ready {r : Registry} {before : Journal rs} {root : Occurrence rs}
    {after : Journal rs} {p : Plan rs}
    (valid : Invariant (Compiled r) seed root before.mixed.core)
    (covered : Coverage (Compiled r) before.mixed.core.erased.current.context.interpretation)
    (step : InstallStep r before after)
    (recorded : after.versionedWhere[before.versionedWhere.length]? = some p) :
    RequestsDeclared after.mixed.core p.packet.site.occurrence p ∧
    Ready after.mixed.core p.packet.site.occurrence p := by
  have installedOrigin := GeneralDeclarativeCurrentSeed345.after_origin valid step
  cases step with
  | whereRow ctx installed checked frame _ _ _ _ _ =>
    change (before.versionedWhere ++ [installed])[before.versionedWhere.length]? = some p at recorded
    rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self] at recorded
    have same : installed = p := Option.some.inj recorded
    subst p
    have declared := GeneralDeclarativeCurrentRequest345.declared (p := installed)
      (checked_compiled checked).2 installedOrigin (valid.raw _ frame.raw_recorded) frame.role_eq
    refine ⟨declared,ready_of_wf ?_ ?_ ?_ declared⟩
    · rw [frame.registry_eq,frame.context_eq]
      exact covered
    · rw [frame.registry_eq]
      exact frame.visible
    · rw [frame.registry_eq]
      exact checked.1

theorem from_reachable {r : Registry} {before : Journal rs} {root : Occurrence rs}
    {ctx : GeneralNominalCandidates.Context} {p : Plan rs}
    (checked : (boundary rs).Checked r)
    (reach : B4TargetV8.Reachable (boundary rs) r root before.mixed)
    (step : InstallStep r before (install before ctx p)) (m : Assignment)
    (fit : Models (install before ctx p) m) (protect : List Nat) :
    ∃ prepared s ports whereRows rootRows n,
      GeneralDeclarativeCommitPackage344.Witness (install before ctx p) p m n protect prepared s ports whereRows rootRows := by
  have valid := GeneralNominalVersionedMixedRoles235.reachable checked reach
  have cover := GeneralNominalVersionedMixedReady235.coverage reach
  exact GeneralDeclarativePackageBoundary344.actual step m fit protect (after_ready valid cover step (by
    change (before.versionedWhere ++ [p])[before.versionedWhere.length]? = some p
    rw [List.getElem?_append_right (Nat.le_refl _),Nat.sub_self]; rfl)).2

end Yulang.GeneralDeclarativeCurrentReady345
