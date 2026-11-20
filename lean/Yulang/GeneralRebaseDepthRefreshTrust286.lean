import Yulang.GeneralRebaseDepthConfluence286

/-! A certified refresh changes the current snapshot, not its retained source
or established packets/effects. Its support witnesses can therefore be reused
when another view-only refinement retains all ordinary atoms. -/
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 29500
set_option maxHeartbeats 14500000
namespace Yulang.GeneralRebaseDepthRefreshTrust286
open GeneralNominalVersionedJournal232 (State)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedMixedObservations233 (Refresh CacheSound)
open GeneralNominalVersionedSupport233 (Discharged)
open GeneralNominalSettledSupport (Settled)

theorem preserves_alias (s : State roles) (ctx) {n m}
    (found : GeneralNominalSaturationState.Alias s.core.erased.current n m) :
    GeneralNominalSaturationState.Alias (refresh s ctx).core.erased.current n m := by
  induction found with
  | refl n => exact .refl n
  | edge edge => exact .edge edge
  | symm _ ih => exact .symm ih
  | trans _ _ ih one => exact .trans ih one

theorem versioned_discharged (s : State roles) (ctx) {o}
    (closed : Discharged s o) : Discharged (refresh s ctx) o := by
  induction closed with
  | packet p recorded _ ih => exact .packet p recorded ih
  | alias x y one two equal _ ih => exact .alias x y one two (preserves_alias s ctx equal) ih

theorem legacy_discharged (s : State roles) (ctx) {o}
    (closed : Settled s.core.erased.current o) :
    Settled (refresh s ctx).core.erased.current o := by
  induction closed with
  | packet p recorded _ ih => exact .packet p recorded ih
  | alias x y one two equal _ ih => exact .alias x y one two (preserves_alias s ctx equal) ih

theorem versioned {s : State roles} {ctx} (cert : Refresh s ctx) {facts}
    (known : GeneralNominalVersionedSupport233.Trusted s facts) :
    GeneralNominalVersionedSupport233.Trusted (refresh s ctx) facts := by
  induction known with
  | source => exact .source
  | input p _ present explains ih =>
    exact .input p ih present explains
  | output e _ present planIn oldInput readback done ih =>
    exact .output e ih present planIn oldInput readback
      ⟨done.1,fun child member => versioned_discharged s ctx (done.2 child member)⟩
  | merge a b _ one two same atoms legal agree ih =>
    exact .merge a b ih one two (preserves_alias s ctx same) (fun atom member => cert.refines.ordinary atom (atoms atom member)) legal agree

theorem legacy {s : State roles} {ctx} (cert : Refresh s ctx) {facts}
    (known : GeneralNominalCenteredHeadMatStepSupport.Trusted s.legacy facts) :
    GeneralNominalCenteredHeadMatStepSupport.Trusted (refresh s ctx).legacy facts := by
  induction known with
  | source => exact .source
  | input p _ present explains ih =>
    exact .input p ih present explains
  | output e _ present planIn oldInput readback done ih =>
    exact .output e ih present planIn oldInput readback
      ⟨done.1,fun child member => legacy_discharged s ctx (done.2 child member)⟩
  | merge a b _ one two same atoms legal agree ih =>
    exact .merge a b ih one two (preserves_alias s ctx same) (fun atom member => cert.refines.ordinary atom (atoms atom member)) legal agree

theorem retained {s : State roles} {ctx} (cert : Refresh s ctx) :
    CacheSound (refresh s ctx) ctx.state := by
  intro o recorded
  obtain ⟨old,new,oldTrust,newTrust,sound⟩ := cert.cache o recorded
  exact ⟨old,new,legacy cert oldTrust,versioned cert newTrust,sound⟩

end Yulang.GeneralRebaseDepthRefreshTrust286
