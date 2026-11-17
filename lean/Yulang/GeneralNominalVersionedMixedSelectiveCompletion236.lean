import Yulang.GeneralNominalVersionedSelectiveAggregate236
import Yulang.GeneralNominalVersionedMixedFreshCompletion236
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedMixedSelectiveCompletion236
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedMixedFreshCompletion236 (pool)
open GeneralNominalVersionedAggregateRealization236 (entries)
variable {roles : Roles.RoleDecls}
noncomputable def extended (state : State roles) (plan : Plan roles) (model : Assignment) : Assignment :=
  GeneralNominalVersionedSelectiveAggregate236.patch plan.packet.context.state.seed plan.packet.site.occurrence.identity
    plan.packet.declaration.id plan.packet.bindings plan.packet.declaration.inputNames (pool state plan) model

def Reused (state : State roles) (plan : Plan roles) (model : Assignment) : Prop :=
  ∀ entry ∈ entries plan.packet.context.state.seed plan.packet.site.occurrence.identity plan.packet.declaration.id
    plan.packet.bindings plan.packet.declaration.inputNames, entry.1 ∈ pool state plan →
      PresenceNormalForm.All CommonNominalFullCarrier.model model (GeneralNominalAllocation.equations entry.1 entry.2)

theorem preserves (state : State roles) (plan : Plan roles) (model : Assignment)
    (identity) (member : identity ∈ pool state plan) : extended state plan model identity = model identity :=
  GeneralNominalSelectiveEquationRealization236.preserves _ _ identity member

theorem raw_preserves (state : State roles) (plan : Plan roles) (model : Assignment)
    (identity) (member : identity ∈ GeneralNominalSemanticRawFrame236.sources plan.packet.context.state) :
    extended state plan model identity = model identity :=
  preserves state plan model identity (by simp [pool,member])

theorem models (state : State roles) (plan : Plan roles) (model : Assignment) (valid : Models state model) :
    Models state (extended state plan model) := by
  apply (GeneralNominalVersionedJournalFrame236.models_iff _ _).mp valid
  intro identity member
  exact (preserves state plan model identity (by simp [pool,member])).symm

theorem classes (state : State roles) (plan : Plan roles) (model : Assignment)
    (valid : GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan model) :
    GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan (extended state plan model) := by
  apply (GeneralNominalVersionedJournalFrame236.class_iff _ _ _ _).mp valid
  intro identity member
  exact (preserves state plan model identity (by simp [pool,member])).symm

theorem compatible (state : State roles) (plan : Plan roles) (model : Assignment)
    (valid : GeneralNominalAllocation.Compatible plan.packet.bindings model) :
    GeneralNominalAllocation.Compatible plan.packet.bindings (extended state plan model) := by
  intro first one last two same
  have a := GeneralNominalSemanticRawFrame236.report_endpoints plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) first one
  have b := GeneralNominalSemanticRawFrame236.report_endpoints plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) last two
  change CommonNominalFullCarrier.Subtype (extended state plan model first.2.1).1 (extended state plan model last.2.2).1
  rw [raw_preserves state plan model _ a.1,raw_preserves state plan model _ b.2]
  exact valid first one last two same

theorem checks (state : State roles) (plan : Plan roles) (model : Assignment)
    (valid : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet))) :
    PresenceNormalForm.All CommonNominalFullCarrier.model (extended state plan model)
      (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)) := by
  intro atom member
  apply (GeneralNominalCenteredModelExtension.atom_same atom (fun identity present =>
    (raw_preserves state plan model identity (GeneralNominalSemanticRawFrame236.checks_sources
      plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) atom member present)).symm)).mp
  exact valid atom member

theorem merges (state : State roles) (plan : Plan roles) (model : Assignment) (reused : Reused state plan model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model (extended state plan model)
      (GeneralNominalVersionedAllocation231.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings) := by
  apply GeneralNominalVersionedSelectiveAggregate236.merges _ _ _ _ _ _ reused
  intro binding member
  have supported := GeneralNominalSemanticRawFrame236.report_endpoints plan.packet.context.state
    (GeneralNominalPacketSupport.report plan.packet) binding member
  exact ⟨by simp [pool,supported.1],by simp [pool,supported.2]⟩

theorem projections (state : State roles) (plan : Plan roles) (model : Assignment)
    (valid : GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) model) :
    GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) (extended state plan model) := by
  apply (GeneralNominalSemanticRawFrame236.projection_iff _ _ (fun identity member =>
    (raw_preserves state plan model identity (GeneralNominalSemanticRawFrame236.report_sources_subset
      plan.packet.context plan.packet.declaration plan.packet.bounds member)).symm)).mp valid

theorem simultaneous (state : State roles) (plan : Plan roles) (model : Assignment)
    (current : plan.packet.context = state.core.erased.current.context)
    (reused : Reused state plan model) (valid : Models state model)
    (cross : GeneralNominalAllocation.Compatible plan.packet.bindings model)
    (self : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)))
    (projection : GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) model)
    (live : GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan model) :
    Models state (extended state plan model) ∧
      GeneralNominalVersionedPlans231.HeadModels plan.packet (extended state plan model) ∧
      GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan (extended state plan model) := by
  refine ⟨models state plan model valid,⟨?_,projections state plan model projection⟩,classes state plan model live⟩
  apply (GeneralNominalVersionedPlans231.private_models_iff ..).mpr
  refine ⟨?_,compatible state plan model cross,merges state plan model reused,checks state plan model self⟩
  rw [current]
  exact (models state plan model valid).1.1
end Yulang.GeneralNominalVersionedMixedSelectiveCompletion236
