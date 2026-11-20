import Yulang.GeneralDeferredLadderEarlyInstall303
import Yulang.GeneralDeferredLadderInstalledCert303

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeferredLadderEarlyReplay303
open GeneralDeferredLadderLedger302 (Phase)
open GeneralDeferredLadderRetargetData302 (listPlan list_same)
open GeneralDeferredLadderEarlyInstall303 (effect installation)
open GeneralObservedLadderRoute301 (focus invocation)
open GeneralNominalVersionedMixedObservations233 (Refresh refresh_models)
open GeneralNominalVersionedRefresh232 (refresh)
open GeneralNominalVersionedInstall232 (install install_models)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalRecursiveCandidates (Context)
open GeneralNominalCommonBridge (Assignment)

theorem all_models (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx)
    (m : Assignment) :
    Models (install (refresh p.state ctx) (effect p hi ctx cert)) m ↔ Models p.state m := by
  refine ⟨fun valid => (refresh_models cert).mp ((install_models rfl).mp valid).1,?_⟩
  intro valid
  exact (install_models rfl).mpr (installation p hi ctx cert m ((refresh_models cert).mpr valid))

theorem reindexed_to_ref (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx) :
    GeneralNominalCenteredHeadMatPlanData.Same (GeneralDeferredLadderEnabled302.effect p hi).plan
      (effect p hi ctx cert).plan := by
  have seed := (GeneralDeferredLadderRetargetData302.lift p ctx cert).seed
  obtain ⟨constructors,interp⟩ := GeneralDeferredLadderReindexed302.promotion_metadata p ctx cert
  refine ⟨rfl,rfl,rfl,seed.symm,constructors.symm,interp.symm,?_⟩
  change GeneralNominalReportErasure.erase (GeneralDeferredLadderLedger302.env p).state
    (GeneralNominalRecursiveCandidates.report (GeneralDeferredLadderLedger302.env p)
      GeneralDeclarationExamples.display [GeneralObservedLadderReport301.point n k (by omega)]) =
    GeneralNominalReportErasure.erase ctx.state
      (GeneralNominalRecursiveCandidates.report ctx GeneralDeclarationExamples.display (listPlan p ctx cert k hi).packet.bounds)
  rw [GeneralDeferredLadderRetargetData302.list_erasure p ctx cert k hi,
    GeneralDictionaryOrdinaryTransport.candidate_report_extended,GeneralDeferredLadderReport302.display_report n k hi]
  rfl

def after_certificate (p : Phase n k) (hi : k ≤ n) (ctx : Context) (cert : Refresh p.state ctx) :
    Refresh (GeneralDeferredLadderAdvance302.advance p hi).state
      (install (refresh p.state ctx) (effect p hi ctx cert)).core.erased.current.context :=
  GeneralDeferredLadderInstalledCert303.lift_install (GeneralDeferredLadderEnabled302.effect p hi)
    rfl ctx cert (effect p hi ctx cert).plan rfl (reindexed_to_ref p hi ctx cert)

end Yulang.GeneralDeferredLadderEarlyReplay303
