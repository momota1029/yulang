import Yulang.GeneralDictionarySemanticDelta223
import Yulang.GeneralDictionaryDefaultModeEffects213
import Yulang.GeneralDictionaryDefaultRawSupport213
import Yulang.GeneralDictionaryTightProjection224
import Yulang.GeneralDictionaryDefaultPacketSupport213

/-! Total-packet support with tight projection reads, retaining every genuine
raw/head/schema/child requirement. Only the old reportSources overapproximation
is removed; no global freshness or Overlap property is asserted. -/
namespace Yulang.GeneralDictionaryTightPacket224
open GeneralDeclarations GeneralNominalCenters
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalCenteredFrame179 (Agree siteSources site_iff captureSources capture_mem)
open GeneralDictionaryDefaultTotalFrame212 (resolve)
open GeneralDictionaryDefaultModeSupport213 (schemaSources)
open GeneralDictionaryDefaultModeEffects213 (plan_schema_iff)
open GeneralNominalCenteredHeadMatPlans (emittedSchema childSchema)
variable {roles : Roles.RoleDecls} {first last : Assignment}

 def headSources (plan : Plan roles) : List Nat :=
  GeneralDictionaryDefaultRawSupport213.sources plan.packet.privateContext.state ++
    GeneralDictionaryTightProjection224.reportSources plan.packet.context.state (GeneralNominalPacketSupport.report plan.packet)

 theorem head_iff (plan : Plan roles) (same : Agree (headSources plan) first last) :
    GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds first ↔
    GeneralNominalCenteredHeadCandidates.HeadModels plan.packet.registry plan.packet.context
      plan.packet.site.occurrence plan.packet.declaration plan.packet.bounds last := by
  have raw : Agree (GeneralDictionaryDefaultRawSupport213.sources plan.packet.privateContext.state) first last :=
    fun name member => same name (List.mem_append_left _ member)
  apply and_congr
  · exact GeneralDictionaryDefaultRawSupport213.models_iff _ raw
  · exact GeneralDictionaryTightProjection224.projection_iff _ _
      (fun name member => same name (List.mem_append_right _ member))

 open GeneralDictionaryDefaultPacketSupport213 (fits_iff childSources)

 def packetSources (plan : Plan roles) : List Nat :=
  headSources plan ++ siteSources plan.input ++ captureSources plan ++
    GeneralNominalModeFrame181.schemaSources plan plan.headSchema ++
    schemaSources (resolve plan) (emittedSchema plan) ++ childSources plan

 theorem packet_iff (plan : Plan roles) (same : Agree (packetSources plan) first last) :
    GeneralNominalCenteredHeadMatStepPackets.Holds plan first ↔
    GeneralNominalCenteredHeadMatStepPackets.Holds plan last := by
  rw [← GeneralNominalCenteredHeadMatStepPackets.models_iff,← GeneralNominalCenteredHeadMatStepPackets.models_iff]
  unfold GeneralNominalCenteredHeadMatPlans.Models
  apply and_congr (head_iff plan (fun name member => same name (by simp [packetSources,member])))
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

end Yulang.GeneralDictionaryTightPacket224

namespace Yulang.GeneralDictionaryTightPacket224
open GeneralNominalCenteredHeadMatStepJournal
open GeneralDictionarySemanticDelta223 (Depends liveSources live_iff)
open GeneralDictionaryDefault214ActualJournal (effectSources effect_iff)
variable {roles : Roles.RoleDecls} {state : State roles} {pool : List Nat}

/-- Tightened replacement for cycle223's install delta; genuine raw ordinary
sources are still retained, so this is not yet a historical freshness theorem. -/
noncomputable def installDelta (state : State roles) (effect : Effect roles) : List Nat :=
  packetSources effect.plan ++ effectSources (install state effect) effect ++
    liveSources state.effects (installCore state.core effect.plan)

theorem install_depends (depends : Depends state pool)
    (snapshot : effect.snapshot = state.core) :
    Depends (install state effect) (pool ++ installDelta state effect) := by
  intro a b same
  rw [install_models snapshot,install_models snapshot]
  unfold InstallationModels
  apply and_congr (depends a b (fun n member => same n (List.mem_append_left _ member)))
  apply and_congr (packet_iff effect.plan (fun n member => same n (by simp [installDelta,member])))
  have current := effect_iff (install state effect) effect (fun n member => same n (by simp [installDelta,member]))
  have prior := live_iff state.effects (installCore state.core effect.plan)
    (fun n member => same n (by simp [installDelta,member]))
  simpa only [install,and_assoc] using and_congr current prior
end Yulang.GeneralDictionaryTightPacket224
