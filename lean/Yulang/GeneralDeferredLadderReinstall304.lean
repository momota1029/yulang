import Yulang.GeneralDeferredLadderAdministrative304
import Yulang.GeneralDeferredLadderRequestFree303

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderReinstall304
open GeneralDeferredLadderOperationalView304 (View choices after_install requests_iff choice_forward)
open GeneralDeferredLadderResnapshot304 (HeadView resnapshot safe_forward alternatives_forward)
open GeneralDeferredLadderAdministrative304 (known_forward)
open GeneralDeferredLadderRequestFree303 (model_of_request_free_install)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedInstall232 (install install_models installCore)
open GeneralNominalVersionedMixedKernel234 (Installable)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalVersionedPlans231 (Holds)

variable {roles : Roles.RoleDecls} {a b : State roles}

theorem request_forward (ab : View a b) (empty : ∀ o, requests a.core o = []) :
    ∀ o, requests b.core o = [] := by
  intro o
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry seen
  have old := (requests_iff ab o entry).mpr seen
  rw [empty] at old
  cases old

theorem future_requests_iff (ab : View a b) (p : GeneralNominalCenters.Plan roles)
    (o : GeneralSourceDictionaries.Occurrence roles) (output : GeneralSourceState.Output) :
    output ∈ requests (installCore a.core p) o ↔ output ∈ requests (installCore b.core p) o := by
  refine GeneralNominalVersionedRefresh232.requests_iff_of_same_lists
    (before := installCore a.core p) (after := installCore b.core p) ?_ ab.aliases
  change a.core.erased.current.sites ++ _ = b.core.erased.current.sites ++ _
  rw [ab.sites]

theorem future_request_forward (ab : View a b) (p : GeneralNominalCenters.Plan roles)
    (empty : ∀ o, requests (installCore a.core p) o = []) :
    ∀ o, requests (installCore b.core p) o = [] := by
  intro o
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro entry seen
  have old := (future_requests_iff ab p o entry).mpr seen
  rw [empty] at old
  cases old

/-- Rebuild and enable the same current plan at another genuinely reached
history. The supplied cache is for that history, rather than an inference
from equality of model predicates. -/
theorem enabled (ab : HeadView a b) (projected : choices a = choices b)
    (e : Effect roles) (good : Installable registry a e)
    (cache : GeneralNominalVersionedMixedObservations233.CacheSound b b.core.erased.current.context.state)
    (noLegacy : b.legacy.effects = [])
    (empty : ∀ o, requests a.core o = [])
    (after : ∀ o, requests (installCore a.core e.plan) o = [])
    (held : ∀ model, Models a model → Holds e.plan model) :
    Installable registry b (resnapshot ab e good.snapshot_eq) := by
  refine ⟨good.registry_eq,rfl,known_forward ab good.safe,cache,good.materialized,
    choice_forward ab.raw projected good.choice,safe_forward ab good.positions,
    alternatives_forward ab good.alternatives,?_⟩
  obtain ⟨m,sat⟩ := good.common
  have old := (ab.raw.models m).mp sat.1
  refine ⟨m,(install_models (effect := resnapshot ab e good.snapshot_eq) rfl).mp ?_⟩
  exact (model_of_request_free_install (resnapshot ab e good.snapshot_eq) rfl noLegacy
    (request_forward ab.raw empty) (future_request_forward ab.raw _ after)
    (fun m hm => held m ((ab.raw.models m).mpr hm)) m).mpr old

theorem compared_after (ab : HeadView a b) (e : Effect roles) (atA : e.snapshot = a.core)
    (aLegacy : a.legacy.effects = []) (bLegacy : b.legacy.effects = [])
    (empty : ∀ o, requests a.core o = [])
    (after : ∀ o, requests (installCore a.core e.plan) o = [])
    (held : ∀ model, Models a model → Holds e.plan model) :
    HeadView (install a e) (install b (resnapshot ab e atA)) := by
  have left := model_of_request_free_install e atA aLegacy empty after held
  have right := model_of_request_free_install (resnapshot ab e atA) rfl bLegacy
    (request_forward ab.raw empty) (future_request_forward ab.raw e.plan after)
    (fun m hm => held m ((ab.raw.models m).mpr hm))
  refine ⟨after_install ab.raw _ _ rfl rfl (fun m => (left m).trans ((ab.raw.models m).trans (right m).symm)),
    rfl,?_⟩
  change a.core.sites ++ _ = b.core.sites ++ _
  rw [ab.centers]
  rfl

end Yulang.GeneralDeferredLadderReinstall304
