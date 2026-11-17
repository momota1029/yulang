import Yulang.GeneralNominalVersionedSelectiveAggregate236
import Yulang.GeneralNominalVersionedModelSupport237
import Yulang.GeneralNominalReportSupport237
import Yulang.GeneralNominalVersionedAggregateLedger236
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralNominalVersionedSupportedCompletion237
open GeneralNominalCenters GeneralNominalVersionedJournal232
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalVersionedModelSupport237 (Support)
noncomputable def pool (names : List Nat) (state : State roles) (plan : Plan roles) : List Nat :=
 names ++ GeneralNominalReportSupport237.sources plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) ++
 GeneralDictionaryDefault214ActualBodyFrame.classSources state.core plan.packet.site.occurrence plan
open GeneralNominalVersionedAggregateRealization236 (entries)
variable {roles : Roles.RoleDecls}
noncomputable def extended (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment) : Assignment :=
  GeneralNominalVersionedSelectiveAggregate236.patch plan.packet.context.state.seed plan.packet.site.occurrence.identity
    plan.packet.declaration.id plan.packet.bindings plan.packet.declaration.inputNames (pool names state plan) model

def Reused (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment) : Prop :=
  ∀ entry ∈ entries plan.packet.context.state.seed plan.packet.site.occurrence.identity plan.packet.declaration.id
    plan.packet.bindings plan.packet.declaration.inputNames, entry.1 ∈ pool names state plan →
      PresenceNormalForm.All CommonNominalFullCarrier.model model (GeneralNominalAllocation.equations entry.1 entry.2)

theorem preserves (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment)
    (identity) (member : identity ∈ pool names state plan) : extended names state plan model identity = model identity :=
  GeneralNominalSelectiveEquationRealization236.preserves _ _ identity member

theorem raw_preserves (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment)
    (identity) (member : identity ∈ GeneralNominalReportSupport237.sources plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)) :
    extended names state plan model identity = model identity :=
  preserves names state plan model identity (by simp [pool,member])

theorem models (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment) (supported : Support state names) (valid : Models state model) :
    Models state (extended names state plan model) := by
  apply (supported model (extended names state plan model) _).mp valid
  intro identity member
  exact (preserves names state plan model identity (by simp [pool,member])).symm

theorem classes (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment)
    (valid : GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan model) :
    GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan (extended names state plan model) := by
  apply (GeneralNominalVersionedJournalFrame236.class_iff _ _ _ _).mp valid
  intro identity member
  exact (preserves names state plan model identity (by simp [pool,member])).symm

theorem compatible (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment)
    (valid : GeneralNominalAllocation.Compatible plan.packet.bindings model) :
    GeneralNominalAllocation.Compatible plan.packet.bindings (extended names state plan model) := by
  intro first one last two same
  have a := GeneralNominalReportSupport237.report_endpoints plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) first one
  have b := GeneralNominalReportSupport237.report_endpoints plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) last two
  change CommonNominalFullCarrier.Subtype (extended names state plan model first.2.1).1 (extended names state plan model last.2.2).1
  rw [raw_preserves names state plan model _ a.1,raw_preserves names state plan model _ b.2]
  exact valid first one last two same

theorem checks (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment)
    (valid : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet))) :
    PresenceNormalForm.All CommonNominalFullCarrier.model (extended names state plan model)
      (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)) := by
  intro atom member
  apply (GeneralNominalCenteredModelExtension.atom_same atom (fun identity present =>
    (raw_preserves names state plan model identity (GeneralNominalReportSupport237.checks_sources
      plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) atom member present)).symm)).mp
  exact valid atom member

theorem merges (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment) (reused : Reused names state plan model) :
    PresenceNormalForm.All CommonNominalFullCarrier.model (extended names state plan model)
      (GeneralNominalVersionedAllocation231.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings) := by
  apply GeneralNominalVersionedSelectiveAggregate236.merges _ _ _ _ _ _ reused
  intro binding member
  have supported := GeneralNominalReportSupport237.report_endpoints plan.packet.context.state
    (GeneralNominalPacketSupport.report plan.packet) binding member
  exact ⟨by simp [pool,supported.1],by simp [pool,supported.2]⟩

theorem projections (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment)
    (valid : GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) model) :
    GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) (extended names state plan model) := by
  apply (GeneralNominalReportSupport237.projection_iff _ _ (fun identity member =>
    (raw_preserves names state plan model identity member).symm)).mp valid

theorem simultaneous (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment)
    (current : plan.packet.context = state.core.erased.current.context)
    (supported : Support state names) (reused : Reused names state plan model) (valid : Models state model)
    (cross : GeneralNominalAllocation.Compatible plan.packet.bindings model)
    (self : PresenceNormalForm.All CommonNominalFullCarrier.model model
      (GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)))
    (projection : GeneralNominalRecursiveInspection.ProjectionModels plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet) model)
    (live : GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan model) :
    Models state (extended names state plan model) ∧
      GeneralNominalVersionedPlans231.HeadModels plan.packet (extended names state plan model) ∧
      GeneralNominalVersionedEffects231.ClassEffects state.core plan.packet.site.occurrence plan (extended names state plan model) := by
  refine ⟨models names state plan model supported valid,⟨?_,projections names state plan model projection⟩,classes names state plan model live⟩
  apply (GeneralNominalVersionedPlans231.private_models_iff ..).mpr
  refine ⟨?_,compatible names state plan model cross,merges names state plan model reused,checks names state plan model self⟩
  rw [current]
  exact (models names state plan model supported valid).1.1
theorem reused_of_ledger (names : List Nat) (state : State roles) (plan : Plan roles) (model : Assignment)
 (covered : GeneralNominalVersionedAggregateLedger236.ProtectedCovered (pool names state plan) state plan.packet)
 (valid : Models state model) : Reused names state plan model :=
 GeneralNominalVersionedAggregateLedger236.protected_equations covered valid

end Yulang.GeneralNominalVersionedSupportedCompletion237
