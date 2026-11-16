import Yulang.GeneralDictionaryTightPacket224
namespace Yulang.GeneralDictionaryRelativePacket225
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree siteSources site_iff captureSources capture_mem)
open GeneralDictionaryDefaultTotalFrame212 (resolve)
open GeneralDictionaryDefaultModeSupport213 (schemaSources)
open GeneralDictionaryDefaultModeEffects213 (plan_schema_iff)
open GeneralNominalCenteredHeadMatPlans (emittedSchema childSchema)
variable {roles : Roles.RoleDecls} {first last : Assignment}

 def ordinaryAtoms (plan : Plan roles) : List (PresenceNormalForm.Atom Nat) :=
  GeneralNominalAllocation.cross plan.packet.bindings ++
  GeneralNominalAllocation.merges plan.packet.context.state plan.packet.registry
    plan.packet.site.occurrence.identity plan.packet.declaration plan.packet.bindings ++
  GeneralNominalRecursiveInspection.selfChecks plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)

 theorem ordinary_exact (plan : Plan roles) (model : Assignment) :
    GeneralNominalPacketSupport.Ordinary plan.packet model ↔
      PresenceNormalForm.All CommonNominalFullCarrier.model model (ordinaryAtoms plan) := by
  simp only [ordinaryAtoms,PresenceNormalForm.all_append,GeneralNominalAllocation.cross_exact,
    GeneralNominalPacketSupport.Ordinary,and_assoc]

 def headSources (plan : Plan roles) : List Nat :=
  (ordinaryAtoms plan).flatMap GeneralNominalState.atomSources ++
    GeneralDictionaryTightProjection224.reportSources plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)

 theorem head_iff (plan : Plan roles)
    (one : GeneralNominalState.Models plan.packet.context.state first)
    (two : GeneralNominalState.Models plan.packet.context.state last)
    (same : Agree (headSources plan) first last) :
    GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds first ↔
    GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds last := by
  apply and_congr
  · change GeneralNominalState.Models plan.packet.privateContext.state first ↔
      GeneralNominalState.Models plan.packet.privateContext.state last
    rw [GeneralNominalPacketSupport.private_exact,GeneralNominalPacketSupport.private_exact]
    simp only [one,two,true_and]
    rw [ordinary_exact,ordinary_exact]
    unfold PresenceNormalForm.All
    apply forall_congr'; intro atom
    apply forall_congr'; intro member
    apply GeneralNominalCenteredModelExtension.atom_same
    intro n present
    exact same n (List.mem_append_left _ (List.mem_flatMap.mpr ⟨atom,member,present⟩))
  · exact GeneralDictionaryTightProjection224.projection_iff _ _
      (fun name member => same name (List.mem_append_right _ member))

 open GeneralDictionaryDefaultPacketSupport213 (fits_iff childSources)

 def packetSources (plan : Plan roles) : List Nat :=
  headSources plan ++ siteSources plan.input ++ captureSources plan ++
    GeneralNominalModeFrame181.schemaSources plan plan.headSchema ++
    schemaSources (resolve plan) (emittedSchema plan) ++ childSources plan

 theorem packet_iff (plan : Plan roles)
    (one : GeneralNominalState.Models plan.packet.context.state first)
    (two : GeneralNominalState.Models plan.packet.context.state last) (same : Agree (packetSources plan) first last) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan first ↔
    GeneralNominalCenteredHeadMatStepPackets.Holds plan last := by
  rw [← GeneralNominalCenteredHeadMatStepPackets.models_iff,← GeneralNominalCenteredHeadMatStepPackets.models_iff]
  unfold GeneralNominalCenteredHeadMatPlans.Models
  apply and_congr (head_iff plan one two (fun name member => same name (by simp [packetSources,member])))
  apply and_congr (site_iff plan.input (fun name member => same name (by simp [packetSources,member])))
  apply and_congr (fits_iff plan (fun name member => same name (by simp [packetSources,member])))
  apply and_congr (GeneralNominalModeFrame181.schema_iff plan plan.headSchema
    (fun name member => same name (by simp [packetSources,member])))
  apply and_congr (plan_schema_iff plan (emittedSchema plan)
    (fun name member => same name (by simp [packetSources,member])))
  apply forall_congr'; intro clause
  apply forall_congr'; intro member
  apply forall_congr'; intro valid
  have support : Agree (siteSources (plan.childSite clause valid) ++
      schemaSources (resolve plan) (childSchema plan clause valid)) first last := by
    intro name present
    apply same
    have contained : name ∈ childSources plan :=
      List.mem_flatMap.mpr ⟨⟨clause,member⟩,by simp,present⟩
    simp [packetSources,contained]
  exact and_congr (site_iff _ (fun name member => support name (List.mem_append_left _ member)))
    (plan_schema_iff _ _ (fun name member => support name (List.mem_append_right _ member)))

end Yulang.GeneralDictionaryRelativePacket225

namespace Yulang.GeneralDictionaryRelativePacket225
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionarySemanticDelta223 (Depends liveSources live_iff)
open GeneralDictionaryDefault214ActualJournal (effectSources effect_iff)
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {state : State roles} {pool : List Nat}

theorem joint_packet_iff (plan : GeneralNominalCenters.Plan roles)
    (context : plan.packet.context = state.core.erased.current.context)
    (depends : Depends state pool)
    (same : ∀ n ∈ pool ++ packetSources plan, a n = b n) :
    (Models state a ∧ GeneralNominalCenteredHeadMatStepPackets.Holds plan a) ↔
    (Models state b ∧ GeneralNominalCenteredHeadMatStepPackets.Holds plan b) := by
  have old := depends a b (fun n member => same n (List.mem_append_left _ member))
  have support : ∀ n ∈ packetSources plan, a n = b n :=
    fun n member => same n (List.mem_append_right _ member)
  constructor
  · rintro ⟨valid,held⟩
    have next := old.mp valid
    exact ⟨next,(packet_iff plan (context ▸ valid.1) (context ▸ next.1) support).mp held⟩
  · rintro ⟨valid,held⟩
    have previous := old.mpr valid
    exact ⟨previous,(packet_iff plan (context ▸ previous.1) (context ▸ valid.1) support).mpr held⟩

/-- Relative installation support: old raw constraints remain in Models state,
not in the added packet delta. New cross/merge/selfCheck constraints remain. -/
noncomputable def installDelta (state : State roles) (effect : Effect roles) : List Nat :=
  packetSources effect.plan ++ effectSources (install state effect) effect ++
    liveSources state.effects (installCore state.core effect.plan)

theorem install_depends (depends : Depends state pool)
    (snapshot : effect.snapshot = state.core) :
    Depends (install state effect) (pool ++ installDelta state effect) := by
  intro a b same
  rw [install_models snapshot,install_models snapshot]
  have context : effect.plan.packet.context = state.core.erased.current.context :=
    effect.frame.context_eq.trans (congrArg (fun s => s.erased.current.context) snapshot)
  have joint := joint_packet_iff effect.plan context depends (fun n member => same n (by
    rcases List.mem_append.mp member with old | fresh
    · exact List.mem_append_left _ old
    · simp [installDelta,fresh]))
  have current := effect_iff (install state effect) effect (fun n member => same n (by simp [installDelta,member]))
  have prior := live_iff state.effects (installCore state.core effect.plan)
    (fun n member => same n (by simp [installDelta,member]))
  simpa only [InstallationModels,install,and_assoc] using and_congr joint (and_congr current prior)
end Yulang.GeneralDictionaryRelativePacket225
