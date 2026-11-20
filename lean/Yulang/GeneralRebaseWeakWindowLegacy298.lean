import Yulang.GeneralRebaseWeakWindow298
import Yulang.GeneralDictionaryVersionLoopNontermination239

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 26000
set_option maxHeartbeats 12000000
namespace Yulang.GeneralRebaseWeakWindowLegacy298
open GeneralDictionaryVersionLoopSource237 (roles sourceRegistry registry root declaration initial)
open GeneralDictionaryVersionLoopIteration239 (state reachable)
open GeneralRebaseVersionMicro278 (installed refreshed install_step refresh_step reobserve_step)
open GeneralRebaseRevisitedTrace298 (Family)
open GeneralRebaseSourceSurvivor267 (Boundary)
open GeneralRebaseLiveProjection264 (project)
open GeneralRebaseWeakProgress268 (Weak)
open GeneralRebaseWeakWindow298 (targetCodes window)
open GeneralNominalVersionedMixedKernel234 (Step)

def owner : Nat := GeneralNominalIdentities.pair root.identity declaration.id

theorem positive_initial :
    (project [owner] [] (state 0)).remaining = [] := by decide +kernel

theorem observed_install :
    (project [owner] [] (installed 0)).remaining = [] := by decide +kernel

theorem installed_reachable :
    B4TargetV8.Reachable (Boundary roles) sourceRegistry root (installed 0) :=
  GeneralNominalVersionedMixedProgressSplit236.reachable_step (reachable 0) (install_step 0)

theorem no_weak_after_first (after : GeneralNominalVersionedJournal232.State roles) :
    ¬ Weak registry root [owner] [] (installed 0) after := by
  intro action
  have counts := GeneralRebaseWeakProgress268.decrease action
  rw [observed_install] at counts
  exact (Nat.not_lt_zero _) counts

theorem no_raw_accessibility :
    ¬ Acc (fun next prev => Step registry root prev next) (installed 0) := by
  intro acc
  have next := acc.inv (refresh_step 0)
  have p := next.inv (reobserve_step 0)
  exact GeneralDictionaryVersionLoopNontermination239.no_acc 1 p

theorem empty_but_divergent (checked : (Boundary roles).Checked sourceRegistry)
    (codes : Family sourceRegistry root checked) :
    targetCodes codes [owner] [] (installed 0) (window codes [owner] [] (installed 0)) = [] ∧
      ¬ Acc (fun next prev => Step registry root prev next) (installed 0) :=
  ⟨(GeneralRebaseWeakWindow298.no_weak_iff codes [owner] [] (installed 0) installed_reachable).mpr
      no_weak_after_first,no_raw_accessibility⟩

end Yulang.GeneralRebaseWeakWindowLegacy298
