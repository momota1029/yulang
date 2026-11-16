import Yulang.GeneralDictionaryReadPacket226
import Yulang.GeneralDictionaryHeadSharing220
import Yulang.GeneralDictionaryCountedRawHead216

namespace Yulang.GeneralDictionaryReachablePacket226
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree siteSources site_iff captureSources capture_mem)
open GeneralDictionaryDefaultTotalFrame212 (resolve)
open GeneralDictionaryDefaultModeSupport213 (schemaSources)
open GeneralDictionaryDefaultModeEffects213 (plan_schema_iff)
open GeneralNominalCenteredHeadMatPlans (emittedSchema childSchema)
variable {roles : Roles.RoleDecls} {first last : Assignment}

def Rest (plan : Plan roles) (model : Assignment) : Prop :=
  plan.input.Holds model ∧ (∀ name, name ∈ plan.packet.declaration.inputNames ∨ GeneralNominalSharedCaptures.Needed plan.packet name →
    GeneralNominalCaptureMerges.Fits model ((GeneralNominalPacketSupport.capture plan.packet).inputs name) (model (plan.binder name)).1) ∧ plan.SchemaHolds plan.headSchema model ∧
  (emittedSchema plan).Holds (GeneralNominalCenteredHeadMatEffects.variables plan model) model ∧
  ∀ clause ∈ plan.packet.declaration.requirements, ∀ valid,
    (plan.childSite clause valid).Holds model ∧
    (childSchema plan clause valid).Holds (GeneralNominalCenteredHeadMatEffects.variables plan model) model

 open GeneralDictionaryDefaultPacketSupport213 (fits_iff childSources)

 def restSources (plan : Plan roles) : List Nat :=
  siteSources plan.input ++ captureSources plan ++
    GeneralNominalModeFrame181.schemaSources plan plan.headSchema ++
    schemaSources (resolve plan) (emittedSchema plan) ++ childSources plan

 theorem rest_iff (plan : Plan roles)
    (same : Agree (restSources plan) first last) :
    Rest plan first ↔ Rest plan last := by
  unfold Rest
  apply and_congr (site_iff plan.input (fun name member => same name (by simp [restSources,member])))
  apply and_congr (fits_iff plan (fun name member => same name (by simp [restSources,member])))
  apply and_congr (GeneralNominalModeFrame181.schema_iff plan plan.headSchema
    (fun name member => same name (by simp [restSources,member])))
  apply and_congr (plan_schema_iff plan (emittedSchema plan)
    (fun name member => same name (by simp [restSources,member])))
  apply forall_congr'; intro clause
  apply forall_congr'; intro member
  apply forall_congr'; intro valid
  have support : Agree (siteSources (plan.childSite clause valid) ++
      schemaSources (resolve plan) (childSchema plan clause valid)) first last := by
    intro name present
    apply same
    have contained : name ∈ childSources plan :=
      List.mem_flatMap.mpr ⟨⟨clause,member⟩,by simp,present⟩
    simp [restSources,contained]
  exact and_congr (site_iff _ (fun name member => support name (List.mem_append_left _ member)))
    (plan_schema_iff _ _ (fun name member => support name (List.mem_append_right _ member)))

end Yulang.GeneralDictionaryReachablePacket226

namespace Yulang.GeneralDictionaryReachablePacket226
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree)
variable {roles : Roles.RoleDecls} {state : State roles}

def mergeSources (plan : Plan roles) : List Nat :=
  (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
    plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings).flatMap GeneralNominalState.atomSources

def packetSources (plan : Plan roles) : List Nat := mergeSources plan ++ restSources plan

theorem packet_iff
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (plan : Plan roles) (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan)
    (one : Models state first) (two : Models state last)
    (same : Agree (packetSources plan) first last) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan first ↔
      GeneralNominalCenteredHeadMatStepPackets.Holds plan last := by
  have rest := rest_iff plan (fun n member => same n (List.mem_append_right _ member))
  have merges : PresenceNormalForm.All CommonNominalFullCarrier.model first
      (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings) ↔
      PresenceNormalForm.All CommonNominalFullCarrier.model last
      (GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
        plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings) := by
    unfold PresenceNormalForm.All
    apply forall_congr'; intro atom
    apply forall_congr'; intro member
    apply GeneralNominalCenteredModelExtension.atom_same
    intro n present
    exact same n (List.mem_append_left _ (List.mem_flatMap.mpr ⟨atom,member,present⟩))
  rw [← GeneralNominalCenteredHeadMatStepPackets.models_iff,← GeneralNominalCenteredHeadMatStepPackets.models_iff]
  change (_ ∧ Rest plan first) ↔ (_ ∧ Rest plan last)
  constructor
  · rintro ⟨head,tail⟩
    have next := rest.mp tail
    have sharedOne := GeneralDictionaryHeadSharing220.agreement_of_holds plan first
      (GeneralDictionaryHeadSharing220.schema_holds plan first tail.2.2.1)
    have sharedTwo := GeneralDictionaryHeadSharing220.agreement_of_holds plan last
      (GeneralDictionaryHeadSharing220.schema_holds plan last next.2.2.1)
    exact ⟨(GeneralDictionaryCountedRawHead216.head_iff_merges source point ground coverage path plan frame last two sharedTwo).mpr
      (merges.mp ((GeneralDictionaryCountedRawHead216.head_iff_merges source point ground coverage path plan frame first one sharedOne).mp head)),next⟩
  · rintro ⟨head,tail⟩
    have previous := rest.mpr tail
    have sharedOne := GeneralDictionaryHeadSharing220.agreement_of_holds plan first
      (GeneralDictionaryHeadSharing220.schema_holds plan first previous.2.2.1)
    have sharedTwo := GeneralDictionaryHeadSharing220.agreement_of_holds plan last
      (GeneralDictionaryHeadSharing220.schema_holds plan last tail.2.2.1)
    exact ⟨(GeneralDictionaryCountedRawHead216.head_iff_merges source point ground coverage path plan frame first one sharedOne).mpr
      (merges.mpr ((GeneralDictionaryCountedRawHead216.head_iff_merges source point ground coverage path plan frame last two sharedTwo).mp head)),previous⟩
end Yulang.GeneralDictionaryReachablePacket226

namespace Yulang.GeneralDictionaryReachablePacket226
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal GeneralDictionaryDefaultKernel208
open GeneralDictionarySemanticDelta223 (Depends liveSources live_iff)
open GeneralDictionaryDefault214ActualJournal (effectSources effect_iff)
variable {roles : Roles.RoleDecls} {state : State roles} {pool : List Nat}

noncomputable def installDelta (state : State roles) (effect : Effect roles) : List Nat :=
  packetSources effect.plan ++ effectSources (install state effect) effect ++
    liveSources state.effects (installCore state.core effect.plan)

/-- The reachable installation delta protects only merge atoms in its raw-head
part. The old journal and transported head schema discharge the other tests. -/
theorem install_depends
    (source : GeneralNominalSourceFormation.InitialSource registry context root)
    (point : ∀ index, (root.demand.arguments index).1 = (root.demand.arguments index).2)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root rootLabels)
    (coverage : GeneralNominalCenteredHeadWFSource.Coverage registry context.interpretation)
    (path : B4Target.Steps (Step registry root) (initial context root) state)
    (enabled : Installable registry state effect) (depends : Depends state pool) :
    Depends (install state effect) (pool ++ installDelta state effect) := by
  intro a b same
  rw [install_models enabled.snapshot_eq,install_models enabled.snapshot_eq]
  have old := depends a b (fun n member => same n (List.mem_append_left _ member))
  have packet (one : Models state a) (two : Models state b) := packet_iff source point ground coverage path
    effect.plan (GeneralDictionaryDefaultDepth208.frame enabled) one two
    (fun n member => same n (by simp [installDelta,member]))
  have joint : (Models state a ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan a) ↔
      (Models state b ∧ GeneralNominalCenteredHeadMatStepPackets.Holds effect.plan b) := by
    constructor
    · rintro ⟨valid,held⟩
      exact ⟨old.mp valid,(packet valid (old.mp valid)).mp held⟩
    · rintro ⟨valid,held⟩
      exact ⟨old.mpr valid,(packet (old.mpr valid) valid).mpr held⟩
  have current := effect_iff (install state effect) effect (fun n member => same n (by simp [installDelta,member]))
  have prior := live_iff state.effects (installCore state.core effect.plan)
    (fun n member => same n (by simp [installDelta,member]))
  simpa only [InstallationModels,install,and_assoc] using and_congr joint (and_congr current prior)

end Yulang.GeneralDictionaryReachablePacket226
