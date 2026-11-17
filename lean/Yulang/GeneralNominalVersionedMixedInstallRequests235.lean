import Yulang.GeneralNominalVersionedMixedReady235
import Yulang.GeneralNominalVersionedFrameTransport232
set_option backward.isDefEq.respectTransparency false
/-! Exact request conservation under installation, when emitted child output
requests are already represented. Includes all output-free-child plans, not just
terminal plans. This does not manufacture the simultaneous model witness. -/
namespace Yulang.GeneralNominalVersionedMixedInstallRequests235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232 GeneralNominalVersionedInstall232
open GeneralNominalCenteredHeadOutputs (requests)
variable {roles : Roles.RoleDecls} {state : State roles} {plan : Plan roles} {effect : Effect roles}

def Absorbed (state : State roles) (plan : Plan roles) : Prop :=
  ∀ raw ∈ GeneralNominalVersionedChildren232.rawSites plan, ∀ output ∈ raw.occurrence.demand.outputs,
    output ∈ requests state.core raw.occurrence

theorem no_outputs
    (empty : ∀ child ∈ GeneralNominalVersionedFrame231.children plan.packet, child.demand.outputs = []) :
    Absorbed state plan := by
  intro raw member output present
  obtain ⟨center,inEmitted,same⟩ := List.mem_map.mp member
  subst raw
  have child := (GeneralNominalVersionedChildren232.emitted_child_iff).mpr ⟨center,inEmitted,rfl⟩
  change output ∈ center.occurrence.demand.outputs at present
  rw [empty center.occurrence child] at present
  cases present

theorem recorded_raw
    (recorded : GeneralNominalVersionedChildren232.rawSites plan ⊆ state.core.erased.current.sites) :
    Absorbed state plan :=
  fun raw member _output present => GeneralNominalCenteredHeadOutputs.request_retained raw (recorded member) (.refl _) present

theorem requests_iff (absorbed : Absorbed state plan) :
    output ∈ requests (installCore state.core plan) root ↔ output ∈ requests state.core root := by
  constructor
  · intro member
    obtain ⟨raw,member,alias,present⟩ := GeneralNominalCenteredHeadOutputs.mem_requests_iff.mp member
    have oldAlias := GeneralNominalVersionedInstallProperties232.alias_iff.mp alias
    rcases List.mem_append.mp member with old | added
    · exact GeneralNominalCenteredHeadOutputs.request_retained raw old oldAlias present
    · exact (GeneralNominalCenteredHeadOutputs.same_class_requests oldAlias).mpr
        (absorbed raw added output present)
  · exact requests_included state.core plan output

theorem versioned_live_iff (absorbed : Absorbed state plan) (prior : Effect roles) :
    prior.Live (installCore state.core plan) model ↔ prior.Live state.core model :=
  GeneralNominalVersionedFrameTransport232.class_effects_iff (fun _ => requests_iff absorbed)

theorem legacy_live_iff (absorbed : Absorbed state plan)
    (prior : GeneralNominalCenteredHeadMatStepJournal.Effect roles) :
    prior.Live (installCore state.core plan) model ↔ prior.Live state.core model := by
  constructor
  · exact GeneralNominalCenteredHeadMatEffects.restrict (fun _ => (requests_iff absorbed).mpr)
  · exact GeneralNominalCenteredHeadMatEffects.restrict (fun _ => (requests_iff absorbed).mp)

theorem installation_iff (snapshot : effect.snapshot = state.core) (absorbed : Absorbed state effect.plan) :
    InstallationModels state effect model ↔
      Models state model ∧ GeneralNominalVersionedPlans231.Holds effect.plan model ∧ effect.Live state.core model := by
  constructor
  · rintro ⟨valid,held,_,live,_⟩
    exact ⟨valid,held,(versioned_live_iff absorbed effect).mp live⟩
  · rintro ⟨valid,held,live⟩
    refine ⟨valid,held,?_,(versioned_live_iff absorbed effect).mpr live,?_,?_⟩
    · exact ⟨GeneralNominalVersionedPlans231.head_models held,snapshot.symm ▸ live⟩
    · intro prior member
      exact (legacy_live_iff absorbed prior).mpr (valid.1.2.2.2.2.2 prior member).2
    · intro prior member
      exact (versioned_live_iff absorbed prior).mpr (valid.2.2 prior member).2

theorem no_outputs_installation_iff (snapshot : effect.snapshot = state.core)
    (empty : ∀ child ∈ GeneralNominalVersionedFrame231.children effect.plan.packet, child.demand.outputs = []) :
    InstallationModels state effect model ↔
      Models state model ∧ GeneralNominalVersionedPlans231.Holds effect.plan model ∧ effect.Live state.core model :=
  installation_iff snapshot (no_outputs empty)

end Yulang.GeneralNominalVersionedMixedInstallRequests235
