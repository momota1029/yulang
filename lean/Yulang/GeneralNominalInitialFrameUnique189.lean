import Yulang.GeneralNominalHeadInitialFrame188
import Yulang.GeneralNominalHeadRecursiveExtension188

/-! Initial sources have exactly one raw and centered site. A checked registry
therefore fixes the entire actual plan once its declaration key is fixed.
This identifies plan witnesses, not their satisfying assignments. -/
set_option backward.isDefEq.respectTransparency false

namespace Yulang.GeneralNominalInitialFrameUnique189
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs (Frame)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}

theorem initial_unique (checked : Checked registry) (context : GeneralNominalCandidates.Context)
    (first last : Plan roles)
    (one : Frame registry (initial context root).core root key first)
    (two : Frame registry (initial context root).core root key last) : first = last := by
  rcases first with ⟨⟨r₁,c₁,s₁,d₁,dc₁,b₁⟩,i₁,ie₁⟩
  rcases last with ⟨⟨r₂,c₂,s₂,d₂,dc₂,b₂⟩,i₂,ie₂⟩
  have rEq₁ : r₁ = registry := one.registry_eq
  have rEq₂ : r₂ = registry := two.registry_eq
  have cEq₁ : c₁ = context := one.context_eq
  have cEq₂ : c₂ = context := two.context_eq
  subst r₁; subst r₂; subst c₁; subst c₂
  have sEq₁ : s₁ = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp one.raw_recorded
  have sEq₂ : s₂ = GeneralNominalDemandMerging.pointSite root := List.mem_singleton.mp two.raw_recorded
  have iEq₁ : i₁ = rootSite context.state.seed root := List.mem_singleton.mp one.center_recorded
  have iEq₂ : i₂ = rootSite context.state.seed root := List.mem_singleton.mp two.center_recorded
  subst s₁; subst s₂; subst i₁; subst i₂
  have dEq : d₁ = d₂ := GeneralDictionaryEmissionPlans.declaration_key_unique registry checked
    d₁ d₂ one.visible two.visible (one.key_eq.trans two.key_eq.symm)
  subst d₂
  have bEq : b₁ = b₂ := Option.some.inj (one.located.symm.trans two.located)
  subst b₂
  rfl

theorem boundary_initial_unique (checked : Checked registry)
    (state : State roles)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (first last : Plan roles)
    (one : Frame registry state.core root key first)
    (two : Frame registry state.core root key last) : first = last := by
  obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
  subst state
  exact initial_unique checked context first last one two

/-- Any class-effect witness at the initial root uses the prescribed frame's
plan. The assignment is unchanged; additional properties of that assignment
are neither discarded nor manufactured. -/
theorem effects_on_frame (checked : Checked registry) (state : State roles)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (effects : GeneralNominalCenteredHeadOutputs.ChosenClassEffects registry state.core root key model) :
    GeneralNominalCenteredHeadOutputs.EffectsReady state.core root candidate ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate model ∧
      GeneralNominalCenteredHeadOutputs.OutputEquations state.core root candidate model := by
  obtain ⟨_,chosen,chosenFrame,ready,head,outputs⟩ := effects
  have same := boundary_initial_unique checked state source candidate chosen frame chosenFrame
  subst chosen
  exact ⟨ready,head,outputs⟩

/-- Initial selection with one prescribed actual Frame needs readiness only
for that frame. It obtains a common current/head/output assignment for that
same plan; no claim about its private HeadModels is added. -/
theorem selected_frame_model (checked : Checked registry) (state : State roles)
    (source : (GeneralNominalCenteredHeadWFBoundary.boundary roles).Initial registry root state)
    (selected : GeneralNominalCenteredHeadWFBoundary.Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (ready : GeneralNominalCenteredHeadOutputs.EffectsReady state.core root candidate) :
    ∃ model, Models state model ∧
      GeneralNominalCenteredHeadOutputs.HeadEquations candidate model ∧
      GeneralNominalCenteredHeadOutputs.OutputEquations state.core root candidate model := by
  obtain ⟨model,valid,effects⟩ := GeneralNominalHeadRecursiveExtension188.selected_effects checked source selected
    (fun other otherFrame => (boundary_initial_unique checked state source candidate other frame otherFrame) ▸ ready)
  have samePlan := effects_on_frame checked state source candidate frame effects
  exact ⟨model,valid,samePlan.2⟩

end Yulang.GeneralNominalInitialFrameUnique189
