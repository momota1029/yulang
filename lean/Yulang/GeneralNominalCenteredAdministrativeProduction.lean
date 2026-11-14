import Yulang.GeneralNominalCenteredAdministrativeWhere
import Yulang.GeneralNominalCenteredInspection

/-! Required merge closure removes the merge premise from selected base-plan
construction. Joint applicability, old value support, and centered branch
feasibility remain explicit; they are not converted into pending diagnostics. -/
namespace Yulang.GeneralNominalCenteredAdministrativeProduction
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalCenters GeneralNominalCenteredSteps
open GeneralNominalCenteredAdministrativeLocal
open GeneralNominalSaturationState (Generated)

variable {roles : Roles.RoleDecls}

theorem selected_base_plan
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (generated : Generated state.erased.current root focus)
    (selected : Local registry state focus (.selected key children))
    (joint : GeneralNominalJointCandidates.Joint registry state.erased.current focus key) :
    ∃ plan : Plan roles, plan.packet.site.occurrence = focus ∧ plan.packet.declaration.id = key ∧
      plan.packet.children = children ∧ plan.input ∈ state.sites ∧
      GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet := by
  obtain ⟨start,⟨context,labels,source,point,ground,rfl⟩,path⟩ := reachable
  exact GeneralNominalCenteredSelection.selected_base_plan path generated (selected_old selected)
    joint (selected_ready selected).2.1

/-- The remaining obligations concern branch production, independently of the
local diagnostic tree or the generated-child conclusion. -/
def Production (registry : Registry) (state : State roles) (focus : Occurrence roles)
    (key : Nat) : Prop :=
  GeneralNominalJointCandidates.Joint registry state.erased.current focus key ∧
  ∀ plan : Plan roles, plan.packet.site.occurrence = focus → plan.packet.declaration.id = key →
    plan.input ∈ state.sites → GeneralNominalFeedbackSteps.Installable registry state.erased.current plan.packet →
    ∃ support, GeneralNominalValueSupport.PacketGuard state.erased plan.packet support ∧
      ∃ model, Models state model ∧ plan.Holds model

theorem selected_installable
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (generated : Generated state.erased.current root focus)
    (selected : Local registry state focus (.selected key children))
    (production : Production registry state focus key) :
    ∃ plan : Plan roles, plan.packet.site.occurrence = focus ∧
      GeneralNominalCenteredBoundary.Installable registry state plan := by
  obtain ⟨plan,same,identity,kids,recorded,enabled⟩ :=
    selected_base_plan reachable generated selected production.1
  have old := selected_old selected
  rw [← same] at old
  exact ⟨plan,same,(GeneralNominalCenteredInspection.selected_installable_iff plan old enabled recorded).mpr
    (production.2 plan same identity recorded enabled)⟩

theorem selected_children
    (reachable : B4TargetV5.Reachable (boundary roles) registry root state)
    (generated : Generated state.erased.current root focus)
    (stable : Stable registry state focus)
    (selected : Local registry state focus (.selected key children))
    (production : Production registry state focus key) :
    ∀ child ∈ children, Generated state.erased.current root child := by
  obtain ⟨plan,same,enabled⟩ := selected_installable reachable generated selected production
  exact GeneralNominalCenteredSelection.guarded_selected_children stable (selected_old selected)
    plan same enabled generated

/-- Leaves need no producer: their child-membership obligation is empty. -/
def ReachableProduction (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root focus key children,
    B4TargetV5.Reachable (boundary roles) registry root state →
    Generated state.erased.current root focus → Stable registry state focus →
    Local registry state focus (.selected key children) → children ≠ [] →
    Production registry state focus key

theorem generatedChildren (production : ReachableProduction roles) : B4SkeletonV5.GeneratedChildren (boundary roles) := by
  intro registry checked state root focus key children reachable reached stable safe unique child member
  have generated : Generated state.erased.current root focus := by
    rcases reached with rfl | generated
    · exact .root
    · exact generated
  have selected := (local_correspondence registry state focus _).mp (B4TargetV3.Local.selected safe unique)
  have nonempty : children ≠ [] := by intro empty; simp [empty] at member
  exact selected_children reachable generated stable selected
    (production registry checked state root focus key children reachable generated stable selected nonempty) child member

/-- The supervisor's evidence law for the previous ground boundary transfers
without any new production assumption. -/
theorem evidenceNode_of_ground
    (evidence : B4SkeletonV5.EvidenceNode (GeneralNominalCenteredGroundBoundary.groundBoundary roles)) :
    B4SkeletonV5.EvidenceNode (boundary roles) := by
  intro registry checked state root reachable model models focus key children dictionaries reached stable childStable safe unique premises
  have selected := selected_old ((local_correspondence registry state focus _).mp (B4TargetV3.Local.selected safe unique))
  cases selected with
  | selected oldSafe oldUnique =>
    exact evidence registry checked state root reachable model models focus key children dictionaries
      reached stable childStable oldSafe oldUnique premises

end Yulang.GeneralNominalCenteredAdministrativeProduction
