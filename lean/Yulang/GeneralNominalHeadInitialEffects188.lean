import Yulang.GeneralNominalHeadVariableExtension188
import Yulang.GeneralNominalCenteredHeadStepAvailability

set_option backward.isDefEq.respectTransparency false

/-! Initial selection obtains a genuine chosen-class-effects witness rather
than assuming a positive chosen-head baseline. Variable-only heads and explicit
output schema coverage are retained restrictions. Installation is not asserted. -/
namespace Yulang.GeneralNominalHeadInitialEffects188
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
open GeneralNominalHeadVariableExtension188 (VariableQueries)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {state : State roles}

theorem chosen_head_exists (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (unique : GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context root key children)
    (variables : ∀ candidate, Frame registry state.core root key candidate → VariableQueries candidate)
    (ready : ∀ candidate, Frame registry state.core root key candidate → EffectsReady state.core root candidate) :
    ∃ model, Models state model ∧ ChosenHead registry state.core root key model := by
  obtain ⟨candidate,model,frame,_,valid,head,_,_⟩ :=
    GeneralNominalHeadVariableExtension188.survivor_extension checked source unique.1 variables
  exact ⟨model,valid,⟨children,unique⟩,candidate,frame,ready candidate frame,head⟩

theorem selected_effects (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (variables : ∀ candidate, Frame registry state.core root key candidate → VariableQueries candidate)
    (ready : ∀ candidate, Frame registry state.core root key candidate → EffectsReady state.core root candidate) :
    ∃ model, Models state model ∧ ChosenClassEffects registry state.core root key model := by
  have old := GeneralNominalCenteredHeadWFBoundary.local_iff.mp selected
  have unique : GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context root key children := by
    cases old with
    | selected _ unique _ => exact unique
  exact GeneralNominalCenteredHeadStepAvailability.selected_has_effects old
    (chosen_head_exists checked source unique variables ready)

theorem empty_effects_ready (empty : requests state.core root = []) (candidate : Plan roles) :
    EffectsReady state.core root candidate := by
  constructor
  · intro output present
    rw [empty] at present
    cases present
  · simp [outputSchema,empty,Plan.schema,GeneralNominalMaterialization.generated]

theorem selected_empty_effects (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (variables : ∀ candidate, Frame registry state.core root key candidate → VariableQueries candidate)
    (empty : requests state.core root = []) :
    ∃ model, Models state model ∧ ChosenClassEffects registry state.core root key model :=
  selected_effects checked source selected variables (fun candidate _ => empty_effects_ready empty candidate)

theorem initial_requests (context : GeneralNominalCandidates.Context) :
    requests (initial context root).core root = root.demand.outputs := by
  classical
  simp only [requests,initial,GeneralNominalCenteredSteps.initial,GeneralNominalCenteredSteps.initialAt,
    GeneralNominalSupport.initial,GeneralNominalSaturationState.initial,
    GeneralNominalDemandMerging.pointSite,List.filter_cons,List.filter_nil]
  simp [rootSite,GeneralNominalSaturationState.Alias.refl]

theorem selected_without_outputs (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (variables : ∀ candidate, Frame registry state.core root key candidate → VariableQueries candidate)
    (empty : root.demand.outputs = []) :
    ∃ model, Models state model ∧ ChosenClassEffects registry state.core root key model := by
  apply selected_empty_effects checked source selected variables
  obtain ⟨⟨context,labels,formed,point,ground,equal⟩,coverage⟩ := source
  subst state
  rw [initial_requests,empty]

end Yulang.GeneralNominalHeadInitialEffects188
