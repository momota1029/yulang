import Yulang.GeneralNominalCenteredHeadMatStepRoles
import Yulang.GeneralNominalCenteredHeadMatStepSupport

set_option backward.isDefEq.respectTransparency false

/-! The direct center emitter retains a center for every raw occurrence.
The invariant is stated for journal updates, independently of the remaining
support and cycle guards of a complete transition relation. -/
namespace Yulang.GeneralNominalCenteredHeadMatStepCoverage
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadMatStepJournal
variable {roles : Roles.RoleDecls}
variable {state : State roles} {effect : Effect roles}
variable {after : GeneralNominalSaturationState.State roles}
variable {model : GeneralNominalCommonBridge.Assignment}

structure Recorded (state : State roles) : Prop where
  rawCenter : ∀ raw ∈ state.core.erased.current.sites,
    ∃ center ∈ state.core.sites, center.occurrence = raw.occurrence
  packetPlan : ∀ packet ∈ state.core.erased.current.packets,
    ∃ plan ∈ state.core.plans, plan.packet = packet
  effectPlan : ∀ effect ∈ state.effects, effect.plan ∈ state.core.plans

theorem initial_recorded (context : GeneralNominalCandidates.Context) (root : Occurrence roles) :
    Recorded (initial context root) := by
  refine ⟨?_,?_,?_⟩
  · intro raw member
    cases List.mem_singleton.mp member
    exact ⟨rootSite context.state.seed root,List.mem_singleton_self _,rfl⟩
  · intro packet member; cases member
  · intro effect member; cases member

theorem install_recorded (recorded : Recorded state) : Recorded (install state effect) := by
  refine ⟨?_,?_,?_⟩
  · intro raw member
    rcases List.mem_append.mp member with old | emitted
    · obtain ⟨center,member,equal⟩ := recorded.rawCenter raw old
      exact ⟨center,List.mem_append_left _ member,equal⟩
    · have mapped : raw ∈ effect.plan.emitted.map Site.observed := emitted
      obtain ⟨center,present,equal⟩ := List.mem_map.mp mapped
      subst raw
      exact ⟨center,List.mem_append_right _ present,rfl⟩
  · intro packet member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨effect.plan,List.mem_cons_self,rfl⟩
    · obtain ⟨plan,member,equal⟩ := recorded.packetPlan packet member
      exact ⟨plan,List.mem_cons_of_mem _ member,equal⟩
  · intro prior member
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (recorded.effectPlan prior member)

theorem change_recorded (recorded : Recorded state)
    (sites : after.sites = state.core.erased.current.sites)
    (packets : after.packets = state.core.erased.current.packets) : Recorded (change state after) := by
  exact ⟨fun raw member => recorded.rawCenter raw (sites ▸ member),
    fun packet member => recorded.packetPlan packet (packets ▸ member),recorded.effectPlan⟩

theorem refresh_recorded (recorded : Recorded state) : Recorded (refresh state context) :=
  change_recorded recorded rfl rfl

theorem merge_recorded (recorded : Recorded state) : Recorded (merge state first last) :=
  change_recorded recorded rfl rfl

theorem requests_have_centers (recorded : Recorded state)
    (request : output ∈ GeneralNominalCenteredHeadOutputs.requests state.core root) :
    ∃ center ∈ state.core.sites,
      GeneralNominalSaturationState.Alias state.core.erased.current root.identity center.occurrence.identity ∧
        output ∈ center.occurrence.demand.outputs := by
  obtain ⟨raw,member,alias,outputMember⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp request
  obtain ⟨center,present,equal⟩ := recorded.rawCenter raw member
  exact ⟨center,present,equal.symm ▸ alias,equal.symm ▸ outputMember⟩

theorem class_readback_covers_requests
    (recorded : Recorded (⟨effect.snapshot,[]⟩ : State roles))
    (readback : GeneralNominalCenteredHeadMatStepSupport.ClassReadback state facts effect)
    (request : output ∈ GeneralNominalCenteredHeadOutputs.requests effect.snapshot effect.plan.input.occurrence) :
    ∃ center ∈ effect.snapshot.sites, output ∈ center.occurrence.demand.outputs ∧
      SameInputs (GeneralNominalCenteredHeadMatStepSupport.Models state facts) effect.plan.input center := by
  obtain ⟨center,member,alias,outputMember⟩ := requests_have_centers recorded request
  exact ⟨center,member,outputMember,readback center member alias⟩

theorem ready (checked : Checked registry) (agree : registry.roles = roles)
    (invariant : GeneralNominalCenteredHeadMatStepRoles.Invariant registry seed root state.core)
    (covered : GeneralNominalCenteredHeadWFSource.Coverage registry state.core.erased.current.context.interpretation)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan) :
    GeneralNominalCenteredHeadMatEffects.Ready state.core focus plan := by
  apply GeneralNominalCenteredHeadMatEffects.ready_of_wf
  · rw [frame.registry_eq,frame.context_eq]
    exact covered
  · rw [frame.registry_eq]
    exact frame.visible
  · rw [frame.registry_eq]
    exact agree
  · exact GeneralNominalCenteredHeadMatStepRoles.requests_declared checked invariant frame

theorem emitted_complete
    (covered : GeneralNominalCenteredHeadWFSource.Coverage registry state.core.erased.current.context.interpretation)
    (frame : GeneralNominalCenteredHeadOutputs.Frame registry state.core focus key plan) :
    (GeneralNominalCenteredHeadMatPlans.emittedSchema plan).unknown = false := by
  apply GeneralNominalCenteredHeadMatPlans.emitted_complete
  rw [frame.registry_eq,frame.context_eq]
  exact covered.1 _ frame.visible

theorem installed_output_effect (valid : Models (install state effect) model)
    (requested : output ∈ GeneralNominalCenteredHeadOutputs.requests state.core effect.plan.packet.site.occurrence)
    (snapshot : effect.snapshot = state.core)
    (found : GeneralDictionaryAssociatedProvenance.lookup roles effect.plan.packet.declaration output.name = some body) :
    GeneralNominalCenteredHeadMatEffects.BodyHolds effect.plan output.target model body := by
  have effects := ((install_models snapshot).mp valid).2.2.1.2
  exact effects.1 output (snapshot ▸ requested) body found

end Yulang.GeneralNominalCenteredHeadMatStepCoverage
