import Yulang.GeneralNominalVersionedJournalFrame236
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedMixedFreshCompletion236
open GeneralNominalVersionedJournal232 GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedSemanticCompletion236 (extended)
open GeneralDictionaryDefault214ActualBodyFrame (classSources)
variable {roles : Roles.RoleDecls}

noncomputable def pool (state : State roles) (plan : Plan roles) : List Nat :=
  GeneralNominalVersionedJournalFrame236.sources state ++
    GeneralNominalSemanticRawFrame236.sources plan.packet.context.state ++
    classSources state.core plan.packet.site.occurrence plan

def Fresh (state : State roles) (plan : Plan roles) : Prop :=
  GeneralNominalVersionedAggregateRealization236.Fresh plan.packet.context.state.seed
    plan.packet.site.occurrence.identity plan.packet.declaration.id plan.packet.bindings
    plan.packet.declaration.inputNames (pool state plan)

theorem restrict_fresh (fresh : Fresh state plan) (included : inner ⊆ pool state plan) :
    GeneralNominalVersionedAggregateRealization236.Fresh plan.packet.context.state.seed
      plan.packet.site.occurrence.identity plan.packet.declaration.id plan.packet.bindings plan.packet.declaration.inputNames inner := by
  intro name named many
  exact ⟨fun member => (fresh name named many).1 (included member),
    fun member => (fresh name named many).2 (included member)⟩

theorem models (fresh : Fresh state plan) (valid : Models state model) :
    Models state (extended plan.packet model) :=
  GeneralNominalVersionedJournalFrame236.aggregate_models state plan.packet
    (restrict_fresh fresh (fun _ member => by simp [pool,member])) valid

theorem classes (fresh : Fresh state plan)
    (valid : GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan model) :
    GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan (extended plan.packet model) := by
  apply (GeneralNominalVersionedJournalFrame236.class_iff _ _ _ _).mp valid
  intro identity member
  have included : identity ∈ pool state plan := by simp [pool,member]
  exact (GeneralNominalVersionedAggregateRealization236.preserves _ _ _ _ _ fresh identity included).symm

theorem simultaneous (state : State roles) (plan : Plan roles) (model : Assignment)
    (current : plan.packet.context = state.core.erased.current.context)
    (fresh : Fresh state plan) (valid : Models state model)
    (cross : GeneralNominalAllocation.Compatible plan.packet.bindings model)
    (self : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)))
    (projection : GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state
      (GeneralNominalPacketSupport.report plan.packet) model)
    (live : GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan model) :
    Models state (extended plan.packet model) ∧
      GeneralNominalVersionedPlans231.HeadModels plan.packet (extended plan.packet model) ∧
      GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan (extended plan.packet model) := by
  refine ⟨models fresh valid,?_,classes fresh live⟩
  apply GeneralNominalVersionedSemanticCompletion236.head_models plan.packet model
    (restrict_fresh fresh (fun _ member => by simp [pool,member])) _ cross self projection
  rw [current]
  exact valid.1.1
end Yulang.GeneralNominalVersionedMixedFreshCompletion236
