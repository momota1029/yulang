import Yulang.GeneralNominalVersionedMixedCurrentCandidate235
set_option backward.isDefEq.respectTransparency false
/-! Any genuine current frame has the selected ordered children. The frame is
not assumed unique as a Plan, and no equality of two snapshots is fabricated. -/
namespace Yulang.GeneralNominalVersionedMixedFrameSelection235
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters
open GeneralNominalVersionedJournal232
open GeneralNominalVersionedCandidates231 (Survivor inputs)
open GeneralNominalVersionedEvidence231
variable {roles : Roles.RoleDecls} {state : State roles}

theorem frame_survivor
    (frame : Frame registry state.core root key plan)
    (known : ¬ GeneralNominalState.RootPending state.core.erased.current.context.state (inputs root).demand) :
    Survivor registry state.core.erased.current.context root key (GeneralNominalVersionedFrame231.children plan.packet) := by
  have regEq := frame.registry_eq
  subst registry
  have rootEq := frame.occurrence_eq
  subst root
  rw [← frame.context_eq] at known ⊢
  refine ⟨known,plan.packet.declaration,frame.visible,?_,frame.key_eq,frame.role_eq,plan.packet.bounds,?_,frame.context_eq.symm ▸ frame.prepared,?_⟩
  · exact frame.registry_eq ▸ plan.packet.checked
  · exact frame.located
  · unfold GeneralNominalVersionedCandidates231.children
    rfl

theorem selected_identifies
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state root (.selected chosen children))
    (frame : Frame registry state.core root key plan) :
    key = chosen ∧ GeneralNominalVersionedFrame231.children plan.packet = children :=
  (GeneralNominalVersionedMixedCurrentEvidence235.selected_unique selected).2 _ _
    (frame_survivor frame (GeneralNominalVersionedMixedCurrentCandidate235.selected_safe selected).1)

noncomputable def effect_of_selected
    (selected : GeneralNominalVersionedMixedBoundary234.Local registry state root (.selected key children))
    (frame : Frame registry state.core root key plan)
    (ready : GeneralNominalCenteredHeadMatEffects.Ready state.core root plan) : Effect roles := by
  have unique := GeneralNominalVersionedMixedCurrentEvidence235.selected_unique selected
  have same := (selected_identifies selected frame).2
  exact ⟨registry,state.core,plan,frame.occurrence_eq.symm ▸ frame.key_eq.symm ▸ frame,
    frame.occurrence_eq.symm ▸ frame.key_eq.symm ▸ same.symm ▸ unique,
    frame.occurrence_eq.symm ▸ ready⟩

theorem effect_registry (selected : GeneralNominalVersionedMixedBoundary234.Local registry state root (.selected key children)) (frame : Frame registry state.core root key plan) (ready) :
    (effect_of_selected selected frame ready).registry = registry := rfl

theorem effect_snapshot (selected : GeneralNominalVersionedMixedBoundary234.Local registry state root (.selected key children)) (frame : Frame registry state.core root key plan) (ready) :
    (effect_of_selected selected frame ready).snapshot = state.core := rfl

theorem effect_plan (selected : GeneralNominalVersionedMixedBoundary234.Local registry state root (.selected key children)) (frame : Frame registry state.core root key plan) (ready) :
    (effect_of_selected selected frame ready).plan = plan := rfl

end Yulang.GeneralNominalVersionedMixedFrameSelection235
