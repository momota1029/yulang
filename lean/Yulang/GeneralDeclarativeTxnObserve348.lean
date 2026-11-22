import Yulang.GeneralDeclarativeTxnComplete348
import Yulang.GeneralDeclarativeWhereStore346

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeTxnObserve348
open GeneralWhereVersionInstall317 (Journal Models)
open GeneralNominalReobservationSteps (Revision)
open GeneralNominalCandidates (Context)
open GeneralNominalVersionedFrameTransport232 (class_effects_iff)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadOutputs (requests)
open GeneralNominalCenters (Plan Site)
open GeneralWhereOriginDelta318 (Cell)
open GeneralDeclarativeWhereEndpoint346 (At)
open GeneralDeclarativeTxnNormalized348 (Observed)
open GeneralDeclarativeObservedSyntax347 (structural)
open GeneralWhereOriginTrace318 (rawOf)
open GeneralDeclarativeHead320 (Equation)

def refresh (j : Journal rs) (ctx : Context) : Journal rs :=
  ⟨GeneralNominalVersionedRefresh232.refresh j.mixed ctx,j.versionedWhere⟩

def revise (j : Journal rs) (revision : Revision j.mixed.core.erased.current) : Journal rs :=
  GeneralDeclarativeWhereStore346.revise j revision

theorem refresh_models {j : Journal rs} {ctx : Context}
    (t : GeneralNominalVersionedMixedObservations233.Refresh j.mixed ctx)
    (m : Assignment) : Models (refresh j ctx) m ↔ Models j m := by
  unfold Models
  apply and_congr (GeneralNominalVersionedMixedObservations233.refresh_models t)
  apply forall_congr'; intro p
  apply forall_congr'; intro present
  apply and_congr_right
  intro _
  exact class_effects_iff (fun _ => GeneralNominalVersionedRefresh232.refresh_requests ..)

theorem revise_models {j : Journal rs} {revision : Revision j.mixed.core.erased.current}
    (t : GeneralNominalVersionedMixedObservations233.Reobserve j.mixed revision)
    (m : Assignment) : Models (revise j revision) m ↔ Models j m := by
  unfold Models
  apply and_congr (GeneralNominalVersionedMixedObservations233.reobserve_models t)
  apply forall_congr'; intro p
  apply forall_congr'; intro present
  apply and_congr_right
  intro _
  exact class_effects_iff (fun _ => GeneralNominalVersionedRefresh232.reobserve_requests ..)

theorem retains_actor {basis x y : Journal rs} {p : Plan rs} {c : Cell p} {ord : Nat}
    {site : Site rs} (birth : At basis x p c ord site)
    (stamps : x.versionedWhere = y.versionedWhere)
    (positions : x.mixed.core.sites = y.mixed.core.sites) :
    At basis y p c ord site :=
  ⟨stamps ▸ birth.stamp,positions ▸ birth.physical,birth.emittedHere,birth.childHere,
    birth.canonical,birth.clauseRole,birth.inputHere,birth.written⟩

/-- Physical writers stay at their positions under this actual nominal
reobservation; the old normalized observation is not copied blindly.
The current snapshot must expose its own row to release the read. -/
theorem revise_observed {basis j : Journal rs} {p : Plan rs} {c : Cell p}
    {revision : Revision j.mixed.core.erased.current} {ord : Nat} {site : Site rs} {row : Equation}
    (birth : At basis j p c ord site)
    (current : structural (rawOf (revise j revision)) c.row.target = some row) :
    Observed basis (revise j revision) p c ord site row :=
  ⟨retains_actor birth rfl rfl,current⟩

end Yulang.GeneralDeclarativeTxnObserve348
