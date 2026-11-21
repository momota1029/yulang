import Yulang.GeneralLiveCompoundFullResult316
import Yulang.GeneralVersionedEndpointBadRow315

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 28000
set_option maxHeartbeats 45000000
/-! Identify the incompatible row at the actual stable, fully classified
state, without using a different model for its child or changing evidence. -/
namespace Yulang.GeneralLiveCompoundCulprit316
open GeneralDictionaryJournalRefinement228Source (roles root)
open GeneralLiveCompoundRegistry316 (declaration)
open GeneralLiveCompoundPost316 (raw raw_models)
open GeneralLiveCompoundPostFrames316 (rootPlan)
open GeneralLiveCompoundLeafInstall316 (after)
open GeneralLiveCompoundPostRootHead316 (adds oldPlan report_codes capture_eval binder_eval)
open GeneralLiveCompoundCurrentRoot316 (plan packet bindings_exact)
open GeneralLiveCompoundPostFeedback316 (old_valid)
open GeneralNominalVersionedInstallation231 (reserved atoms allocated)
open GeneralNominalVersionedTransport231 (extendedPlan extendedPacket)
open GeneralNominalVersionedPlans231 (HeadModels Ordinary variables)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedJournal232 (Models)
open GeneralVersionedEndpointEquationCut315 (whereRows)
open GeneralVersionedEndpointBadRow315 (lowerRow upperRow)
open GeneralNominalReportErasure (checks_exact projections_exact)
open GeneralNominalRecursiveCandidates (report)
open GeneralLiveCompoundUpperSnapshot316 (snap context)

abbrev slot0 : Fin 8 := 0

theorem old_head (m : Assignment) (given : HeadModels rootPlan.packet m) :
    HeadModels oldPlan.packet m := by
  have base := (GeneralNominalVersionedPlans231.private_models_iff ..).mp given.1
  have sameRaw : GeneralNominalState.Models raw m := base.1
  have rawOld : GeneralNominalState.Models oldPlan.packet.context.state m := (raw_models m).mp sameRaw
  have pure := (GeneralNominalVersionedTransport231.ordinary_iff (reserved adds) (atoms adds)
    (allocated adds) packet m).mp base.2
  have projected := (GeneralNominalVersionedTransport231.projection_iff (reserved adds) (atoms adds)
    (allocated adds) packet m).mp given.2
  refine ⟨(GeneralNominalVersionedPlans231.private_models_iff ..).mpr ⟨rawOld,?_⟩,?_⟩
  · unfold Ordinary at pure ⊢
    rw [bindings_exact] at pure
    change Ordinary oldPlan.packet m
    unfold Ordinary
    rw [GeneralMixedCompoundUpperRoot307.bindings_exact]
    refine ⟨pure.1,pure.2.1,?_⟩
    have checks := pure.2.2
    change PresenceNormalForm.All CommonNominalFullCarrier.model m
      (GeneralNominalRecursiveInspection.selfChecks snap (report context declaration [(slot0,slot0)])) at checks
    rw [← checks_exact,report_codes,checks_exact] at checks
    exact checks
  · change GeneralNominalRecursiveInspection.ProjectionModels snap (report context declaration [(slot0,slot0)]) m at projected
    rw [← projections_exact,report_codes,projections_exact] at projected
    exact projected

theorem variables_pair (m : Assignment) : variables rootPlan m = variables oldPlan m := by
  change variables (extendedPlan (reserved adds) (atoms adds) (allocated adds) plan) m = _
  rw [GeneralNominalVersionedTransport231.variables_eq]
  funext mode name
  unfold variables
  simp only [binder_eval,capture_eval,
    show plan.packet.declaration.outputNames = oldPlan.packet.declaration.outputNames from rfl]

theorem where_rows : whereRows rootPlan = [lowerRow,upperRow] := by
  unfold whereRows GeneralVersionedRootWrites312.whereRequests rootPlan
  simp only [GeneralNominalVersionedTransport231.plan_packet,GeneralNominalVersionedTransport231.frame_eq,
    GeneralNominalVersionedTransport231.capture_eq]
  change (GeneralNominalCenteredHeadMatSchemas.generated packet.registry.constructors packet.context.interpretation
    ((GeneralCanonicalChildOrder.canonicalEmit packet.site.occurrence.identity packet.declaration packet.checked
      (GeneralNominalVersionedFrame231.capture packet)
      ((GeneralNominalVersionedFrame231.frame packet).allocation packet.declaration.id)).flatMap
        GeneralNominalCenteredHeadMatSchemas.emissionRequests)).equations = _
  simp only [GeneralCanonicalChildOrder.canonicalEmit,GeneralCanonicalChildOrder.canonicalDeclaration,
    GeneralCanonicalChildOrder.canonicalRequirements,List.mergeSort_singleton]
  rfl

theorem only_lower (m : Assignment) (valid : Models after m) (head : HeadModels rootPlan.packet m) :
    ∀ row ∈ whereRows rootPlan, ¬ row.Holds (variables rootPlan m) m ↔ row = lowerRow := by
  intro row seen
  rw [variables_pair]
  exact GeneralVersionedEndpointBadRow315.only_lower_fails m (old_valid m valid) (old_head m head) row
    (GeneralVersionedEndpointBadRow315.both_rows.symm ▸ (where_rows ▸ seen))

end Yulang.GeneralLiveCompoundCulprit316
