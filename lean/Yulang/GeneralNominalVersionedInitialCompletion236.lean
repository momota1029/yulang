import Yulang.GeneralNominalVersionedSemanticCompletion236
import Yulang.GeneralNominalVersionedJournal232
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedInitialCompletion236
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalSaturationState (Packet)
open GeneralNominalVersionedSemanticCompletion236 (extended)
open GeneralNominalVersionedJournal232
open GeneralNominalCenters
variable (packet : Packet roles) {root : GeneralSourceDictionaries.Occurrence roles}
variable (source : GeneralNominalSourceFormation.InitialSource packet.registry packet.context root)

include source

theorem fresh : GeneralNominalVersionedSemanticCompletion236.Fresh packet := by
  intro name named many
  constructor <;> intro member
  all_goals
    have below := source.below_seed _ (GeneralNominalSemanticRawFrame236.contained packet.context.state member)
    have above := GeneralNominalAggregateVersion231.above_seed packet.context.state.seed packet.site.occurrence.identity packet.declaration.id 0 name packet.bindings
    have above1 := GeneralNominalAggregateVersion231.above_seed packet.context.state.seed packet.site.occurrence.identity packet.declaration.id 1 name packet.bindings
    omega

theorem center_kept (model : Assignment) (index : Fin (roles root.demand.role).arity) :
    extended packet model ((rootSite packet.context.state.seed root).center index) =
      model ((rootSite packet.context.state.seed root).center index) := by
  apply GeneralNominalFiniteEquationRealization236.outside
  intro entry member
  obtain ⟨name,named,many,rfl | rfl⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp member
  all_goals
    by_cases point : (root.demand.arguments index).1 = (root.demand.arguments index).2
    · rw [point_center _ _ index point]
      intro equal
      have small := source.below_seed _ (source.linked.1 index).1
      have large := GeneralNominalAggregateVersion231.above_seed packet.context.state.seed packet.site.occurrence.identity packet.declaration.id 0 name packet.bindings
      have large1 := GeneralNominalAggregateVersion231.above_seed packet.context.state.seed packet.site.occurrence.identity packet.declaration.id 1 name packet.bindings
      omega
    · simpa only [rootSite,point,ite_false,GeneralNominalCenters.fresh,GeneralNominalAllocation.origin] using
        (GeneralNominalAggregateVersion231.not_legacy_slot packet.context.state.seed packet.site.occurrence.identity packet.declaration.id _ name packet.bindings root.identity 0 7 index.val)

theorem initial_models (model : Assignment)
    (valid : Models (initial packet.context root) model) :
    Models (initial packet.context root) (extended packet model) := by
  obtain ⟨raw,site⟩ := (GeneralNominalVersionedJournal232.initial_models packet.context root model).mp valid
  apply (GeneralNominalVersionedJournal232.initial_models packet.context root (extended packet model)).mpr
  refine ⟨GeneralNominalVersionedSemanticCompletion236.raw_models packet model (fresh packet source) raw,?_⟩
  intro index
  change CommonNominalFullCarrier.Subtype (extended packet model (root.demand.arguments index).1).1
    (extended packet model ((rootSite packet.context.state.seed root).center index)).1 ∧
    CommonNominalFullCarrier.Subtype (extended packet model ((rootSite packet.context.state.seed root).center index)).1
      (extended packet model (root.demand.arguments index).2).1
  have kept (identity) (member : identity ∈ GeneralNominalState.sources packet.context.state) :
      extended packet model identity = model identity := by
    apply GeneralNominalFiniteEquationRealization236.outside
    intro entry entryMem equal
    obtain ⟨name,_,_,rfl | rfl⟩ := (GeneralNominalVersionedAggregateRealization236.member_iff ..).mp entryMem
    all_goals
      have below := source.below_seed identity member
      have above := GeneralNominalAggregateVersion231.above_seed packet.context.state.seed packet.site.occurrence.identity packet.declaration.id 0 name packet.bindings
      have above1 := GeneralNominalAggregateVersion231.above_seed packet.context.state.seed packet.site.occurrence.identity packet.declaration.id 1 name packet.bindings
      omega
  rw [kept _ (source.linked.1 index).1,kept _ (source.linked.1 index).2,center_kept packet source model index]
  exact site index

theorem simultaneous (model : Assignment) (valid : Models (initial packet.context root) model)
    (cross : GeneralNominalAllocation.Compatible packet.bindings model)
    (self : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks packet.context.state (GeneralNominalPacketSupport.report packet)))
    (projection : GeneralNominalRecursiveInspection.ProjectionModels packet.context.state (GeneralNominalPacketSupport.report packet) model) :
    Models (initial packet.context root) (extended packet model) ∧
      GeneralNominalVersionedPlans231.HeadModels packet (extended packet model) :=
  ⟨initial_models packet source model valid,
    GeneralNominalVersionedSemanticCompletion236.head_models packet model (fresh packet source) valid.1.1 cross self projection⟩
end Yulang.GeneralNominalVersionedInitialCompletion236
