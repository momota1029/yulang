import Yulang.GeneralNominalHeadLeafPlan189

/-! Actual initial selection of a leaf declaration can install its full packet.
Novelty is semantic: an already-committed packet need not take a further step. -/
namespace Yulang.GeneralNominalInitialLeafStep189
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalCenteredHeadStepEffects
open GeneralNominalCenteredHeadOutputs
open GeneralNominalCenteredHeadStepKernel
open GeneralNominalCenteredHeadWFBoundary (boundary Local)
variable {roles : Roles.RoleDecls} {registry : Registry} {root : Occurrence roles}
variable {state : State roles}

theorem selected_candidate (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (leaf : ∀ declaration ∈ registry.declarations, declaration.id = key → declaration.requirements = [])
    (empty : root.demand.outputs = []) :
    ∃ candidate support, Frame registry state.core root key candidate ∧
      candidate.packet.children = children ∧ Installable registry state candidate support := by
  have old := GeneralNominalCenteredHeadWFBoundary.local_iff.mp selected
  have unique : GeneralNominalCenteredHeadCandidates.Unique registry state.core.erased.current.context root key children := by
    cases old with
    | selected _ unique _ => exact unique
  obtain ⟨candidate,frame,kids⟩ := GeneralNominalHeadInitialFrame188.initial_frame state source unique.1
  obtain ⟨support,enabled⟩ := GeneralNominalHeadLeafPlan189.initial_selected_installable checked source selected
    candidate frame (leaf candidate.packet.declaration frame.visible frame.key_eq) empty
  exact ⟨candidate,support,frame,kids,enabled⟩

theorem committed_or_step (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (leaf : ∀ declaration ∈ registry.declarations, declaration.id = key → declaration.requirements = [])
    (empty : root.demand.outputs = []) :
    ∃ candidate, Frame registry state.core root key candidate ∧
      (GeneralNominalFeedbackSteps.Committed state.core.erased.current candidate.packet ∨
        ∃ after, (boundary roles).Step registry root state after) := by
  obtain ⟨candidate,support,frame,_,enabled⟩ := selected_candidate checked source selected leaf empty
  refine ⟨candidate,frame,?_⟩
  exact GeneralNominalCenteredHeadStepAvailability.enabled_or_committed enabled
    (frame.occurrence_eq ▸ GeneralNominalSaturationState.Generated.root)

theorem selected_novel_step (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (leaf : candidate.packet.declaration.requirements = []) (empty : root.demand.outputs = [])
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.core.erased.current candidate.packet) :
    ∃ after, (boundary roles).Step registry root state after ∧
      ∃ model, Models after model := by
  obtain ⟨support,enabled⟩ := GeneralNominalHeadLeafPlan189.initial_selected_installable checked source selected
    candidate frame leaf empty
  refine ⟨install state candidate support enabled,?_,installed_inhabited enabled⟩
  exact ⟨candidate.packet.site.occurrence,
    frame.occurrence_eq ▸ GeneralNominalSaturationState.Generated.root,
    .install candidate support enabled novel⟩

theorem selected_novel_not_stable (checked : Checked registry)
    (source : (boundary roles).Initial registry root state)
    (selected : Local registry state root (.selected key children))
    (candidate : Plan roles) (frame : Frame registry state.core root key candidate)
    (leaf : candidate.packet.declaration.requirements = []) (empty : root.demand.outputs = [])
    (novel : ¬ GeneralNominalFeedbackSteps.Committed state.core.erased.current candidate.packet) :
    ¬ (boundary roles).Stable registry state root := by
  obtain ⟨after,⟨focus,generated,action⟩,_⟩ := selected_novel_step checked source selected candidate frame leaf empty novel
  exact fun stable => stable focus generated after action

end Yulang.GeneralNominalInitialLeafStep189
