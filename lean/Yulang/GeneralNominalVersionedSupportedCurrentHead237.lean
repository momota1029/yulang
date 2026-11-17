import Yulang.GeneralNominalVersionedSupportedHead237
import Yulang.GeneralNominalVersionedCurrentHead237
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedSupportedCurrentHead237
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231
variable {roles : Roles.RoleDecls} {state : State roles} {model : Assignment}
theorem selective_head (names : List Nat) (plan : Plan roles)
    (supported : GeneralNominalVersionedModelSupport237.Support state names)
    (sites : GeneralNominalVersionedTraceSiteSupport237.Covered state names)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
    (covered : GeneralNominalVersionedAggregateLedger236.ProtectedCovered
      (GeneralNominalVersionedSupportedCompletion237.pool names state plan) state plan.packet)
    (valid : Models state model)
    (cross : GeneralNominalAllocation.Compatible plan.packet.bindings model)
    (self : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)))
    (projection : GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) model)
    (schema : SchemaHolds plan plan.headSchema model)
    (live : GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan model) :
    let next := GeneralNominalVersionedSupportedCompletion237.extended names state plan model
    Models state next ∧ HeadModels plan.packet next ∧
      SchemaHolds plan plan.headSchema next ∧
      (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
        GeneralNominalCaptureMerges.Fits next ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name)
          (next (GeneralNominalVersionedFrame231.binder plan name)).1) ∧
      GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan next := by
  obtain ⟨models,head,classes⟩ := GeneralNominalVersionedSupportedCompletion237.simultaneous
    names state plan model frame.context_eq supported
    (GeneralNominalVersionedSupportedCompletion237.reused_of_ledger names state plan model covered valid) valid cross self projection live
  have actual := (GeneralNominalVersionedSupportedHead237.head_schema_iff names state plan model sites frame.center_recorded).mpr schema
  exact ⟨models,head,actual,GeneralNominalVersionedCurrentHead237.capture_fits plan frame models head actual,classes⟩
end Yulang.GeneralNominalVersionedSupportedCurrentHead237
