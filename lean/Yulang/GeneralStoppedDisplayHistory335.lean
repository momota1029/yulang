import Yulang.GeneralStoppedInstallHistory335
import Yulang.GeneralStoppedDisplayOriginal335

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralStoppedDisplayHistory335
open GeneralNominalExamples (registry displayRoot displayChild)
open GeneralRebaseDisplayFrame276 (before after effect)
open GeneralStoppedDisplayProjection335 (reached)
open GeneralStoppedInstallHistory335 (InstalledBetween installed_origin)
open GeneralNominalVersionedMixedBoundary234 (Local)

theorem root_recorded : effect ∈ after.effects := List.mem_cons_self

theorem root_installed : InstalledBetween registry displayRoot before after effect :=
  installed_origin reached rfl root_recorded

/-- No emitted leaf versioned effect was stored. This actual successful
raw leaf has a local proof and its literal site, but there is no such
entry to reconstruct the ordinary leaf from. -/
theorem selected_not_installed :
    Local registry after displayChild (.selected 3 []) ∧
    (∀ e ∈ after.effects, e.plan.packet.site.occurrence ≠ displayChild) := by
  refine ⟨GeneralRebaseDisplaySelection276.picked_child,?_⟩
  intro e present
  change e ∈ [effect] at present
  cases List.mem_singleton.mp present
  intro bad
  have id := congrArg GeneralSourceDictionaries.Occurrence.identity bad
  have nope : effect.plan.packet.site.occurrence.identity ≠ displayChild.identity := by decide +kernel
  exact nope id

end Yulang.GeneralStoppedDisplayHistory335
