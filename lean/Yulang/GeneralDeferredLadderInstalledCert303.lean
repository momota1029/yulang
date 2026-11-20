import Yulang.GeneralDeferredLadderReplay303
import Yulang.GeneralNominalVersionedMixedCache233

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderInstalledCert303
open GeneralNominalCenters (Plan)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralNominalVersionedInstallation231 (replayPlan atoms)
open GeneralNominalVersionedInstall232 (install install_models)
open GeneralNominalVersionedJournal232 (State Effect Models)
open GeneralNominalVersionedMixedObservations233 (Refresh)
open GeneralDeferredLadderReplay303 (replay_refines replay_support)
open GeneralDeferredLadderInstallData303 (atoms_eq)
open GeneralNominalRecursiveCandidates (Context)
open PresenceNormalForm (All)

/-- A refresh certificate transports over a reference installation and the
same erased packet replayed in the retargeted context. This is a certificate
constructor only; it does not presume either raw installation is enabled. -/
def lift_install {s : State roles} (e : Effect roles) (snapshot : e.snapshot = s.core)
    (ctx : Context) (cert : Refresh s ctx) (q : Plan roles)
    (context : q.packet.context = ctx) (same : Same e.plan q) :
    Refresh (install s e) (replayPlan q).packet.context := by
  have baseContext : e.plan.packet.context = s.core.erased.current.context :=
    e.frame.context_eq.trans (congrArg (fun core => core.erased.current.context) snapshot)
  have oldRefines : GeneralNominalRefinements.Refines e.plan.packet.context.state q.packet.context.state := by
    rw [baseContext,context]
    exact cert.refines
  have oldSupport : ∀ id ∈ GeneralNominalState.sources q.packet.context.state,
      id ∈ GeneralNominalState.sources e.plan.packet.context.state := by
    rw [baseContext,context]
    exact cert.support
  refine ⟨replay_refines same oldRefines,same.interpretation.symm,replay_support same oldSupport,?_,?_⟩
  · intro m valid
    have prior := (install_models snapshot).mp valid
    obtain ⟨source,ordinary⟩ := cert.constraints m prior.1
    have appended := (GeneralNominalVersionedInstallation231.atoms_iff e.plan.packet m).mpr prior.2.1.2.1.1
    have kept : All CommonNominalFullCarrier.model m (atoms q.packet) := atoms_eq same ▸ appended
    refine ⟨?_,?_⟩
    · change GeneralNominalCommonBridge.Models q.packet.context.state.base m
      rw [context]
      exact source
    · change All CommonNominalFullCarrier.model m (q.packet.context.state.ordinary ++ atoms q.packet)
      rw [context]
      exact (PresenceNormalForm.all_append ..).mpr ⟨ordinary,kept⟩
  · apply GeneralNominalVersionedMixedCache233.cache
      (GeneralNominalVersionedSupportCache233.install_growth snapshot)
    intro observation recorded
    have real := GeneralNominalVersionedCache232.recorded_replay q recorded
    rw [context] at real
    exact cert.cache observation real

end Yulang.GeneralDeferredLadderInstalledCert303
