import Yulang.GeneralRebaseVersionPrivate278
import Yulang.GeneralRebaseLoosePrivate278

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseInstallTimeline278
open GeneralRebaseRoundMicro278 (Tick Phase next)

def installedCount : Tick → Nat
  | ⟨n,.enter⟩ => n
  | ⟨n,.installed⟩ | ⟨n,.refreshed⟩ => n+1

def observedCount : Tick → Nat
  | ⟨n,.enter⟩ | ⟨n,.installed⟩ => n
  | ⟨n,.refreshed⟩ => n+1

theorem install_event (t : Tick) :
    installedCount (next t) = installedCount t + (if t.phase = .enter then 1 else 0) := by
  rcases t with ⟨n,p⟩
  cases p <;> rfl

theorem observe_event (t : Tick) :
    observedCount (next t) = observedCount t + (if t.phase = .installed then 1 else 0) := by
  rcases t with ⟨n,p⟩
  cases p <;> rfl

namespace Version
open GeneralDictionaryVersionLoopIteration239 (state stages round)
open GeneralDictionaryVersionLoopFamilyNovel239 (bad)
open GeneralRebaseVersionMicro278 (raw installed refreshed)
open GeneralRebaseVersionPrivate278 (refreshed_exact reobserved_exact later_bad)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)

theorem round_restriction (earlier later : Nat) (bound : earlier ≤ later) (m : Assignment)
    (valid : Models (state later) m) : Models (state earlier) m := by
  induction later with
  | zero =>
    have eq : earlier = 0 := by omega
    exact eq ▸ valid
  | succ later ih =>
    by_cases same : earlier = later+1
    · exact same ▸ valid
    · exact ih (by omega) (GeneralNominalVersionedMixedKernel234.steps_models (round later) valid)

theorem enter_patch (n index : Nat) : Models (state n) (bad index) ↔ n ≤ index := by
  constructor
  · intro held
    apply Classical.byContradiction
    intro outside
    exact later_bad index (round_restriction (index+1) n (by omega) (bad index) held)
  · exact (stages n).future index

theorem patch_exact (t : Tick) (index : Nat) :
    Models (raw t) (bad index) ↔ installedCount t ≤ index := by
  rcases t with ⟨n,p⟩
  cases p
  · exact enter_patch n index
  · exact (refreshed_exact n _).symm.trans ((reobserved_exact n _).symm.trans (enter_patch (n+1) index))
  · exact (reobserved_exact n _).symm.trans (enter_patch (n+1) index)

end Version

namespace Loose
open GeneralDictionaryLooseIterationIteration240 (state stages round)
open GeneralDictionaryLooseFamilyNovel240 (bad)
open GeneralRebaseLooseMicro278 (raw installed refreshed)
open GeneralRebaseLoosePrivate278 (refreshed_exact reobserved_exact later_bad)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalCommonBridge (Assignment)

theorem round_restriction (earlier later : Nat) (bound : earlier ≤ later) (m : Assignment)
    (valid : Models (state later) m) : Models (state earlier) m := by
  induction later with
  | zero =>
    have eq : earlier = 0 := by omega
    exact eq ▸ valid
  | succ later ih =>
    by_cases same : earlier = later+1
    · exact same ▸ valid
    · exact ih (by omega) (GeneralNominalVersionedMixedKernel234.steps_models
        (GeneralNominalPointErasure240.steps_old (round later)) valid)

theorem enter_patch (n index : Nat) : Models (state n) (bad index) ↔ n ≤ index := by
  constructor
  · intro held
    apply Classical.byContradiction
    intro outside
    exact later_bad index (round_restriction (index+1) n (by omega) (bad index) held)
  · exact (stages n).future index

theorem patch_exact (t : Tick) (index : Nat) :
    Models (raw t) (bad index) ↔ installedCount t ≤ index := by
  rcases t with ⟨n,p⟩
  cases p
  · exact enter_patch n index
  · exact (refreshed_exact n _).symm.trans ((reobserved_exact n _).symm.trans (enter_patch (n+1) index))
  · exact (reobserved_exact n _).symm.trans (enter_patch (n+1) index)

end Loose
end Yulang.GeneralRebaseInstallTimeline278
