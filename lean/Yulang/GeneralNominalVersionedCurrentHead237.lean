import Yulang.GeneralNominalVersionedCurrentProjection237
import Yulang.GeneralNominalVersionedProjectionBounds237
import Yulang.GeneralNominalVersionedSelectiveChild237
import Yulang.GeneralNominalVersionedMixedLedgerCompletion236
set_option backward.isDefEq.respectTransparency false
/-! Capture Fits is derived, not independently assumed, for a current complete
actual head. Selective completion preserves that head while building new merges. -/
namespace Yulang.GeneralNominalVersionedCurrentHead237
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedPlans231
variable {roles : Roles.RoleDecls} {state : State roles} {model : Assignment}

theorem capture_fits (plan : Plan roles)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
    (valid : Models state model) (head : HeadModels plan.packet model)
    (schema : SchemaHolds plan plan.headSchema model) (name : Nat)
    (needed : name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name) :
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name)
      (model (GeneralNominalVersionedFrame231.binder plan name)).1 :=
  GeneralNominalVersionedProjectionBounds237.capture_fits plan model
    (GeneralNominalVersionedCurrentProjection237.frame_finished plan frame)
    (GeneralNominalVersionedCurrentProjection237.schema_projection plan frame model valid schema)
    ((private_models_iff ..).mp head.1).2.2.1 schema name needed

theorem holds_iff (plan : Plan roles)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
    (valid : Models state model) : Holds plan model ↔
    HeadModels plan.packet model ∧ SchemaHolds plan plan.headSchema model ∧ Outputs plan model ∧
    (∀ clause ∈ plan.packet.declaration.requirements, ∀ signature : clause.Signature roles,
      (GeneralNominalVersionedFrame231.childSite plan clause signature).Holds model ∧
      (childSchema plan clause signature).Holds (variables plan model) model) := by
  rw [GeneralNominalVersionedPacketFrame236.holds_shape]
  constructor
  · rintro ⟨head,_,_,schema,_,children,outputs⟩
    exact ⟨head,schema,outputs,children⟩
  · rintro ⟨head,schema,outputs,children⟩
    exact ⟨head,valid.1.2.2.2.1 plan.input frame.center_recorded,
      capture_fits plan frame valid head schema,schema,fun eq member _ => outputs eq member,children,outputs⟩

theorem selective_head (plan : Plan roles)
    (frame : GeneralNominalVersionedEvidence231.Frame registry state.core focus key plan)
    (covered : GeneralNominalVersionedAggregateLedger236.ProtectedCovered
      (GeneralNominalVersionedMixedFreshCompletion236.pool state plan) state plan.packet)
    (valid : Models state model)
    (cross : GeneralNominalAllocation.Compatible plan.packet.bindings model)
    (self : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)))
    (projection : GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) model)
    (schema : SchemaHolds plan plan.headSchema model)
    (live : GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan model) :
    let next := GeneralNominalVersionedMixedSelectiveCompletion236.extended state plan model
    Models state next ∧ HeadModels plan.packet next ∧
      SchemaHolds plan plan.headSchema next ∧
      (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
        GeneralNominalCaptureMerges.Fits next ((GeneralNominalVersionedFrame231.capture plan.packet).inputs name)
          (next (GeneralNominalVersionedFrame231.binder plan name)).1) ∧
      GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan next := by
  obtain ⟨models,head,classes⟩ := GeneralNominalVersionedMixedLedgerCompletion236.simultaneous
    state plan model frame.context_eq covered valid cross self projection live
  have actual := (GeneralNominalVersionedSelectiveHead237.head_schema_iff state plan model frame.center_recorded).mpr schema
  exact ⟨models,head,actual,capture_fits plan frame models head actual,classes⟩
end Yulang.GeneralNominalVersionedCurrentHead237
