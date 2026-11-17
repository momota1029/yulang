import Yulang.GeneralNominalVersionedMixedRoles235
import Yulang.GeneralNominalVersionedMixedSelectedFrame235
set_option backward.isDefEq.respectTransparency false
/-! Historical declaration visibility, site registration and role agreement on
actual mixed source traces. Neither current Prepared nor ChoiceCompatible is
assumed as an invariant. Historical packets are linked to full versioned plans. -/
namespace Yulang.GeneralNominalVersionedMixedChoiceHistory236
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedMixedKernel234
variable {roles : Roles.RoleDecls} {state : State roles}

def Recorded (registry : Registry) (state : State roles) : Prop :=
  (∀ packet ∈ state.core.erased.current.packets,
    packet.declaration ∈ registry.declarations ∧
    packet.site ∈ state.core.erased.current.sites ∧
    packet.declaration.role = packet.site.occurrence.demand.role) ∧
  state.core.erased.current.packets = state.plans.map Plan.packet

theorem initial (registry : Registry) (context : GeneralNominalCandidates.Context) (root : Occurrence roles) :
    Recorded registry (initial context root) := ⟨(by intro _ member; cases member),rfl⟩

theorem step (path : Step registry root before after) (recorded : Recorded registry before) : Recorded registry after := by
  obtain ⟨focus,generated,action⟩ := path
  have growth := GeneralNominalVersionedMixedGrowth234.at_growth action
  cases action with
  | administrative action =>
    cases action with
    | enqueue =>
      exact ⟨fun packet member => ⟨(recorded.1 packet member).1,
        growth.legacy.rawSites (recorded.1 packet member).2.1,(recorded.1 packet member).2.2⟩,recorded.2⟩
    | refresh | reobserve | equate => exact recorded
  | refresh | merge => exact recorded
  | install effect enabled novel =>
    refine ⟨?_,?_⟩
    · intro packet member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨enabled.registry_eq ▸ effect.frame.visible,
          List.mem_append_left _ (by simpa only [enabled.snapshot_eq] using effect.frame.raw_recorded),effect.frame.role_eq⟩
      · exact ⟨(recorded.1 packet member).1,
          growth.legacy.rawSites (recorded.1 packet member).2.1,(recorded.1 packet member).2.2⟩
    · change _ :: before.core.erased.current.packets = _ :: before.plans.map Plan.packet
      rw [recorded.2]

theorem steps (path : B4Target.Steps (Step registry root) before after) (recorded : Recorded registry before) : Recorded registry after := by
  induction path with
  | refl => exact recorded
  | tail path action ih => exact step action ih

theorem reachable
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) value root state) :
    Recorded (GeneralNominalCenteredHeadAllocEncoding.registry value) state := by
  obtain ⟨first,⟨legacy,⟨context,labels,source,point,ground,coverage,sameLegacy⟩,same⟩,path⟩ := path
  subst first
  subst legacy
  exact steps path (initial _ context root)

theorem visible
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) value root state)
    (member : packet ∈ state.core.erased.current.packets) :
    packet.declaration ∈ (GeneralNominalCenteredHeadAllocEncoding.registry value).declarations :=
  ((reachable path).1 packet member).1

theorem packet_plan
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) value root state)
    (member : packet ∈ state.core.erased.current.packets) :
    ∃ plan ∈ state.plans, plan.packet = packet := by
  rw [(reachable path).2] at member
  exact List.mem_map.mp member

theorem packet_full_model
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) value root state)
    (member : packet ∈ state.core.erased.current.packets) (valid : Models state model) :
    ∃ plan ∈ state.plans, plan.packet = packet ∧ GeneralNominalVersionedPlans231.Holds plan model := by
  obtain ⟨plan,present,same⟩ := packet_plan path member
  exact ⟨plan,present,same,valid.2.1 plan present⟩

theorem historical_role
    (checked : (GeneralNominalVersionedMixedSourceBoundary234.boundary roles).Checked value)
    (path : B4TargetV8.Reachable (GeneralNominalVersionedMixedSourceBoundary234.boundary roles) value root state)
    (selected : GeneralNominalVersionedMixedSourceBoundary234.Local value state focus (.selected key children))
    (member : prior ∈ state.core.erased.current.packets)
    (alias : GeneralNominalSaturationState.Alias state.core.erased.current focus.identity prior.site.occurrence.identity) :
    prior.declaration.role = focus.demand.role := by
  obtain ⟨plan,frame,_⟩ := GeneralNominalVersionedMixedSelectedFrame235.source_frame path selected
  have inv := GeneralNominalVersionedMixedRoles235.reachable checked path
  have compiled := (GeneralNominalVersionedMixedSourceBoundary234.checked_compiled checked).2
  have old := (reachable path).1 prior member
  have currentOrigin := frame.occurrence_eq ▸ inv.raw plan.packet.site frame.raw_recorded
  have colors := GeneralNominalCenteredHeadMatStepRoles.alias_color inv alias
  rw [GeneralNominalCenteredHeadMatStepRoles.color_of_origin compiled currentOrigin,
    GeneralNominalCenteredHeadMatStepRoles.color_of_origin compiled (inv.raw _ old.2.1)] at colors
  exact old.2.2.trans colors.symm
end Yulang.GeneralNominalVersionedMixedChoiceHistory236
