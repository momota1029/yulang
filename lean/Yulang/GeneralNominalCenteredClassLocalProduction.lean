import Yulang.GeneralNominalCenteredClassLocalExecutor
import Yulang.GeneralNominalCenteredCompletionParts

set_option backward.isDefEq.respectTransparency false

/-! Joint is supplied by class selection. The exact installation residuals
are raw uniqueness, value support, and a common centered model. -/
namespace Yulang.GeneralNominalCenteredClassLocalProduction
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredClassLocalBoundary
open GeneralNominalCenteredSelectedCompletion (Frame)
open GeneralNominalSaturationState (Generated Packet)
variable {roles : Roles.RoleDecls}

theorem selected_frame
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (generated : Generated state.erased.current root focus)
    (selected : Local registry state focus (.selected key children)) :
    ∃ plan, Frame registry state focus key children plan := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  obtain ⟨raw,member,same⟩ := GeneralNominalCenteredTrace.generated_registered path generated
  obtain ⟨center,recorded,centerSame⟩ := GeneralNominalCenteredTrace.raw_site_centered path raw member
  obtain ⟨_,declaration,visible,checked,identity,role,bounds,located,prepared,kids⟩ := selected_survivor selected
  let packet : Packet roles := ⟨registry,state.erased.current.context,raw,declaration,checked,bounds⟩
  let plan : Plan roles := ⟨packet,center,centerSame⟩
  refine ⟨plan,rfl,rfl,same,identity,?_,member,recorded,visible,role,located,prepared⟩
  change GeneralNominalAllocation.children _ registry raw.occurrence declaration checked _ = children
  rw [same]
  exact kids.symm

def Feasible (_registry : Registry) (state : State roles) (plan : Plan roles) : Prop :=
  ∃ support, GeneralNominalValueSupport.PacketGuard state.erased plan.packet support ∧
    ∃ model, Models state model ∧ plan.Holds model

theorem frame_installable_iff (checked : Checked registry)
    (selected : Local registry state focus (.selected key children))
    (frame : Frame registry state focus key children plan) :
    GeneralNominalCenteredBoundary.Installable registry state plan ↔
      RawUnique registry state focus key ∧ Feasible registry state plan := by
  constructor
  · intro enabled
    have old := GeneralNominalCenteredBoundary.installable_selected enabled
    rw [frame.occurrence_eq,frame.key_eq,frame.children_eq] at old
    have administrative := GeneralNominalCenteredAdministrativeLocal.selected_iff.mpr ⟨old,selected_ready selected⟩
    have raw := (selected_old_iff checked selected).mp administrative
    have parts := (GeneralNominalCenteredSelectedCompletion.frame_installable_iff administrative frame).mp enabled
    exact ⟨raw,parts.2⟩
  · rintro ⟨unique,feasible⟩
    have old := (selected_old_iff checked selected).mpr unique
    apply (GeneralNominalCenteredSelectedCompletion.frame_installable_iff old frame).mpr
    refine ⟨?_,feasible⟩
    rw [frame.occurrence_eq,frame.key_eq]
    exact selected_joint selected

def UncoveredFeasibility (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root focus key children,
    B4TargetV5.Reachable (boundary roles) registry root state →
    Generated state.erased.current root focus → Stable registry state focus →
    Local registry state focus (.selected key children) → children ≠ [] →
    (¬ ∃ plan, Frame registry state focus key children plan ∧
      GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet) →
    RawUnique registry state focus key ∧ ∃ plan, Frame registry state focus key children plan ∧ Feasible registry state plan

theorem generatedChildren (feasibility : UncoveredFeasibility roles) : B4SkeletonV5.GeneratedChildren (boundary roles) := by
  intro registry checked state root focus key children reachable reached stable safe unique child member
  have generated : Generated state.erased.current root focus := by
    rcases reached with rfl | generated
    · exact .root
    · exact generated
  have selected := (local_correspondence registry state focus _).mp (B4TargetV3.Local.selected safe unique)
  classical
  have committed : ∃ plan, Frame registry state focus key children plan ∧
      GeneralNominalFeedbackSteps.Committed state.erased.current plan.packet := by
    apply Classical.byContradiction
    intro missing
    have nonempty : children ≠ [] := by intro empty; simp [empty] at member
    obtain ⟨raw,plan,frame,feasible⟩ := feasibility registry checked state root focus key children
      reachable generated stable selected nonempty missing
    have installed := GeneralNominalCenteredSelection.stable_committed stable plan frame.occurrence_eq
      ((frame_installable_iff checked.2 selected frame).mpr ⟨raw,feasible⟩)
    exact missing ⟨plan,frame,installed⟩
  obtain ⟨plan,frame,committed⟩ := committed
  apply Generated.child generated
  rw [← frame.occurrence_eq]
  exact committed.2 child (frame.children_eq ▸ member)

end Yulang.GeneralNominalCenteredClassLocalProduction
