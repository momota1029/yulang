import Yulang.GeneralDictionaryReachableBoundary
import Yulang.B4SkeletonV5

/-! Honest residual for the V5 general feedback dictionary bridge. Joint means
actual same-input alias agreement and a model satisfying the selected branch;
it contains neither Evidence nor the desired B4 conclusion. Reachability is
not replaced by this residual: it is carried independently and exactly.
The residual is NOT proved for all reachable states. -/
namespace Yulang.GeneralDictionaryReachableJointBridge
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralDictionaryReachableBoundary
open GeneralNominalJointCandidates (Joint)

/-- The evidence residual needs Joint only in inhabited reachable journals.
The saturation root is separate from the classified occurrence. -/
def ModeledSelectedJoint (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ (state : State roles) root,
    B4TargetV5.Reachable (boundary roles) registry root state →
    ∀ focus key children, (focus = root ∨ Generated state root focus) →
    GeneralNominalFeedbackSteps.Stable registry state focus →
    GeneralNominalFeedbackK2.Local registry state focus (.selected key children) →
    (∃ model, Models state model) → Joint registry state focus key

/-- Generation must hold independently of model existence. It is only needed
on the saturation root and its actual generated descendants. -/
def GeneratedSelectedJoint (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ (state : State roles) root,
    B4TargetV5.Reachable (boundary roles) registry root state →
    ∀ focus key children, (focus = root ∨ Generated state root focus) →
    GeneralNominalFeedbackSteps.Stable registry state focus →
    GeneralNominalFeedbackK2.Local registry state focus (.selected key children) →
    Joint registry state focus key

theorem evidenceNode_of_modeled_joint (roles : Roles.RoleDecls)
    (joint : ModeledSelectedJoint roles) : B4SkeletonV5.EvidenceNode (boundary roles) := by
  intro registry checked state root reachable model valid focus key children dictionaries reached stable _ safe unique given
  have selected := (GeneralNominalFeedbackBoundary.local_correspondence roles
    (GeneralDictionaryFeedbackEvidence.evidence roles) registry state focus _).mp
      (B4TargetV3.Local.selected safe unique)
  exact GeneralDictionaryFeedbackEvidence.stable_joint_evidence registry state focus key children
    stable selected (joint registry checked state root reachable focus key children reached stable selected ⟨model,valid⟩)
    model valid dictionaries given

theorem generatedChildren_of_joint (roles : Roles.RoleDecls)
    (joint : GeneratedSelectedJoint roles) : B4SkeletonV5.GeneratedChildren (boundary roles) := by
  intro registry checked state root focus key children reachable reached stable safe unique child member
  have selected := (GeneralNominalFeedbackBoundary.local_correspondence roles
    (GeneralDictionaryFeedbackEvidence.evidence roles) registry state focus _).mp
      (B4TargetV3.Local.selected safe unique)
  have edge := (GeneralDictionaryFeedbackEvidence.stable_joint_instance registry state focus key children
    stable selected (joint registry checked state root reachable focus key children reached stable selected)).2 child member
  change Generated state root child
  rcases reached with same | generated
  · simpa only [same] using edge
  · exact GeneralNominalSaturationState.generated_trans generated edge

end Yulang.GeneralDictionaryReachableJointBridge
