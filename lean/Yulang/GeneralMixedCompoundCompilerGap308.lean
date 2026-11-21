import Yulang.GeneralMixedCompoundPointEvidence308
import Yulang.GeneralMixedCompoundUpperObstruction307
import Yulang.GeneralMixedCompoundEarlySquare308

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 25000
set_option maxHeartbeats 17500000
namespace Yulang.GeneralMixedCompoundCompilerGap308
open GeneralDictionaryJournalRefinement228Source (root roles)
open GeneralDictionaryCompoundSource238 (registry declaration)
open GeneralDictionaryCompoundSites238 (childSite)
open GeneralDictionaryCompoundFrame238 (installed)
open GeneralDictionaryCompoundPoint238 (point)
open GeneralMixedCompoundPointFirstPlan308 (pointFirst candidateModel)
open GeneralMixedCompoundPointViewTrust308 (observed)
open GeneralMixedCompoundUpperRefresh307 (upperState)
open GeneralMixedCompoundPointRoot308 (plan models_observed)
open GeneralMixedCompoundPointEvidence308 (local_certificate)
open GeneralMixedCompoundEarlySquare308 (common_model)
open GeneralMixedCompoundEarlyRefresh308 (models)
open GeneralNominalVersionedEvidence231 (Certificate)
open GeneralNominalVersionedJournal232 (State Models)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredHeadMatPlanData (Same)
open GeneralRebaseCompoundRows273 (Agrees)
open GeneralNominalCenters (Plan)

def LocallyCertified (s : State roles) : Prop :=
  ∃ (m : Assignment) (p : Plan roles), Models s m ∧
    Certificate registry s.core m root declaration.id [childSite.occurrence] p

theorem current_readback :
    Same plan GeneralMixedCompoundUpperRoot307.plan := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  change GeneralNominalReportErasure.erase _
      (GeneralNominalRecursiveCandidates.report GeneralMixedCompoundPointView308.context declaration [(0,0)]) =
    GeneralNominalReportErasure.erase _
      (GeneralNominalRecursiveCandidates.report GeneralMixedCompoundUpperSnapshot307.context declaration [(0,0)])
  rw [GeneralMixedCompoundPointRoot308.report_exact,GeneralMixedCompoundUpperRoot307.report_exact]
  rfl

theorem public_same (boundary : Assignment) :
    (∃ m, Agrees m boundary ∧ Models observed m) ↔
    (∃ m, Agrees m boundary ∧ Models upperState m) := by
  simp only [GeneralMixedCompoundPointViewTrust308.models,common_model,models]
  exact GeneralMixedCompoundPointFirstPublic308.same_projection boundary

theorem point_cert : LocallyCertified observed := ⟨candidateModel,plan,models_observed,local_certificate⟩

theorem historical_not_cert : ¬ LocallyCertified upperState := by
  rintro ⟨m,p,valid,certificate⟩
  have chosen := GeneralMixedCompoundUpperRoot307.frame_plan certificate.frame
  subst p
  exact GeneralMixedCompoundUpperObstruction307.no_current_packet m valid certificate.packet

/-- Current root captures/anchors have exactly the same identity-erased
readback and the public model projections agree. These data do not determine
whether an installed journal admits a full current local certificate. -/
theorem equal_readback_separates_local_cert :
    Same plan GeneralMixedCompoundUpperRoot307.plan ∧
    (∀ boundary, (∃ m, Agrees m boundary ∧ Models observed m) ↔
      (∃ m, Agrees m boundary ∧ Models upperState m)) ∧
    LocallyCertified observed ∧ ¬ LocallyCertified upperState :=
  ⟨current_readback,public_same,point_cert,historical_not_cert⟩

theorem no_factorization {Code : Type} (code : State roles → Code) (accept : Code → Prop)
    (insensitive : Same plan GeneralMixedCompoundUpperRoot307.plan →
      (∀ boundary, (∃ m, Agrees m boundary ∧ Models observed m) ↔
        (∃ m, Agrees m boundary ∧ Models upperState m)) →
      code observed = code upperState)
    (correct : ∀ s, accept (code s) ↔ LocallyCertified s) : False := by
  have eq := insensitive current_readback public_same
  have yes := (correct observed).mpr point_cert
  rw [eq] at yes
  exact historical_not_cert ((correct upperState).mp yes)

end Yulang.GeneralMixedCompoundCompilerGap308
