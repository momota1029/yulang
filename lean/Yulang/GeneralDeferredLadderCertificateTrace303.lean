import Yulang.GeneralDeferredLadderInstalledCert303

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderCertificateTrace303
open GeneralNominalVersionedJournal232 (State Effect)
open GeneralNominalVersionedInstall232 (install)
open GeneralNominalVersionedInstallation231 (replayPlan)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralNominalCenters (Plan)
open GeneralNominalRecursiveCandidates (Context)

/-- A paired sequence records the reference installation and the actual
replay context. The input does not assert target operational enabledness. -/
inductive ReplayTrace {roles} (first : State roles) (context : Context) :
    Nat → State roles → Context → Prop
  | zero : ReplayTrace first context 0 first context
  | next (previous : ReplayTrace first context count s ctx)
      (e : Effect roles) (snapshot : e.snapshot = s.core) (q : Plan roles)
      (located : q.packet.context = ctx) (same : Same e.plan q) :
    ReplayTrace first context (count+1) (install s e) (replayPlan q).packet.context

theorem refresh_of_replay {first last : State roles} {ctx target : Context}
    {count : Nat} (initial : Refresh first ctx) (trace : ReplayTrace first ctx count last target) :
    Nonempty (Refresh last target) := by
  induction trace with
  | zero => exact ⟨initial⟩
  | next _ e snapshot q located same ih =>
    obtain ⟨cert⟩ := ih
    exact ⟨GeneralDeferredLadderInstalledCert303.lift_install e snapshot _ cert q located same⟩

end Yulang.GeneralDeferredLadderCertificateTrace303
