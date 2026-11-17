import Yulang.GeneralNominalVersionedAggregateRealization236
import Yulang.GeneralNominalVersionedPlans231
import Yulang.GeneralNominalSemanticRawFrame236
import Yulang.GeneralNominalRawFrame179
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedSemanticCompletion236
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedAggregateRealization236
open GeneralNominalCenteredModelExtension
variable (packet : Packet roles) (model : Assignment)
noncomputable abbrev extended := patch packet.context.state.seed packet.site.occurrence.identity
  packet.declaration.id packet.bindings packet.declaration.inputNames model

def Fresh : Prop := GeneralNominalVersionedAggregateRealization236.Fresh packet.context.state.seed
  packet.site.occurrence.identity packet.declaration.id packet.bindings packet.declaration.inputNames
  (GeneralNominalSemanticRawFrame236.sources packet.context.state)

theorem preserves (fresh : Fresh packet) : ∀ identity ∈ GeneralNominalSemanticRawFrame236.sources packet.context.state,
    extended packet model identity = model identity :=
  GeneralNominalVersionedAggregateRealization236.preserves _ _ _ _ _ fresh

theorem raw_models (fresh : Fresh packet) (valid : GeneralNominalState.Models packet.context.state model) :
    GeneralNominalState.Models packet.context.state (extended packet model) :=
  (GeneralNominalSemanticRawFrame236.source_models_same _
    (fun identity member => (preserves packet model fresh identity member).symm)).mp valid

theorem compatible (fresh : Fresh packet) (valid : GeneralNominalAllocation.Compatible packet.bindings model) :
    GeneralNominalAllocation.Compatible packet.bindings (extended packet model) := by
  intro first one last two same
  have a := GeneralNominalSemanticRawFrame236.report_endpoints packet.context.state (GeneralNominalPacketSupport.report packet) first one
  have b := GeneralNominalSemanticRawFrame236.report_endpoints packet.context.state (GeneralNominalPacketSupport.report packet) last two
  change CommonNominalFullCarrier.Subtype (extended packet model first.2.1).1 (extended packet model last.2.2).1
  rw [preserves packet model fresh _ a.1,preserves packet model fresh _ b.2]
  exact valid first one last two same

theorem checks (fresh : Fresh packet)
    (valid : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks packet.context.state (GeneralNominalPacketSupport.report packet))) :
    PresenceNormalForm.All CommonNominalFullCarrier.model (extended packet model)
      (GeneralNominalRecursiveInspection.selfChecks packet.context.state (GeneralNominalPacketSupport.report packet)) := by
  intro atom member
  apply (atom_same atom (fun identity present => (preserves packet model fresh identity
    (GeneralNominalSemanticRawFrame236.checks_sources packet.context.state (GeneralNominalPacketSupport.report packet)
      atom member present)).symm)).mp
  exact valid atom member

theorem ordinary (fresh : Fresh packet) (cross : GeneralNominalAllocation.Compatible packet.bindings model)
    (self : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks packet.context.state (GeneralNominalPacketSupport.report packet))) :
    GeneralNominalVersionedPlans231.Ordinary packet (extended packet model) :=
  ⟨compatible packet model fresh cross,
   merges packet.context.state packet.registry packet.site.occurrence.identity packet.declaration packet.bindings model fresh
     (GeneralNominalSemanticRawFrame236.report_endpoints packet.context.state (GeneralNominalPacketSupport.report packet)),
   checks packet model fresh self⟩

theorem private_models (fresh : Fresh packet) (valid : GeneralNominalState.Models packet.context.state model)
    (cross : GeneralNominalAllocation.Compatible packet.bindings model)
    (self : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks packet.context.state (GeneralNominalPacketSupport.report packet))) :
    GeneralNominalState.Models (GeneralNominalVersionedPlans231.privateState packet) (extended packet model) :=
  (GeneralNominalVersionedPlans231.private_models_iff ..).mpr
    ⟨raw_models packet model fresh valid,ordinary packet model fresh cross self⟩

theorem projections (fresh : Fresh packet)
    (valid : GeneralNominalRecursiveInspection.ProjectionModels packet.context.state (GeneralNominalPacketSupport.report packet) model) :
    GeneralNominalRecursiveInspection.ProjectionModels packet.context.state (GeneralNominalPacketSupport.report packet) (extended packet model) := by
  apply (GeneralNominalSemanticRawFrame236.projection_iff _ _ (fun identity member =>
    (preserves packet model fresh identity (GeneralNominalSemanticRawFrame236.report_sources_subset
      packet.context packet.declaration packet.bounds member)).symm)).mp valid

theorem head_models (fresh : Fresh packet) (valid : GeneralNominalState.Models packet.context.state model)
    (cross : GeneralNominalAllocation.Compatible packet.bindings model)
    (self : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks packet.context.state (GeneralNominalPacketSupport.report packet)))
    (projection : GeneralNominalRecursiveInspection.ProjectionModels packet.context.state (GeneralNominalPacketSupport.report packet) model) :
    GeneralNominalVersionedPlans231.HeadModels packet (extended packet model) :=
  ⟨private_models packet model fresh valid cross self,projections packet model fresh projection⟩
end Yulang.GeneralNominalVersionedSemanticCompletion236
