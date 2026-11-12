import Yulang.GeneralDictionarySupportTree
import Yulang.GeneralNominalSupportExecutor

/-! Explicit residual composition for the actual support-aware V5 boundary.
This is conditional: Progress, where-accessibility, canonical final-local order,
and joint applicability are NOT proved here. In particular the existing driver
is noncomputable and this theorem is not an executable language implementation. -/
namespace Yulang.GeneralDictionarySupportComposition
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalSupportBoundary
open GeneralNominalSupportExecutor
open CommonRoleOutermostResolver
open B4TargetV5

/-- The remaining dictionary obligation is simultaneous branch applicability,
not the desired Evidence conclusion itself. -/
def JointAtSelected (roles : Roles.RoleDecls) : Prop :=
  ∀ registry, (boundary roles).Checked registry → ∀ state root,
    Reachable (boundary roles) registry root state → ∀ focus,
      Generated state.current root focus → GeneralNominalSupportSteps.Stable registry state focus →
      ∀ key children, GeneralNominalSupportBoundary.Local registry state focus (.selected key children) →
        GeneralNominalJointCandidates.Joint registry state.current focus key

theorem evidenceNode (roles : Roles.RoleDecls) (joint : JointAtSelected roles) :
    B4SkeletonV5.EvidenceNode (boundary roles) := by
  intro registry checked state root reachable model valid focus key children dictionaries reached stable _ safe unique given
  have generated : Generated state.current root focus := by
    rcases reached with same | reached
    · subst focus; exact .root
    · exact reached
  have selected := (local_correspondence registry state focus (.selected key children)).mp
    (B4TargetV3.Local.selected safe unique)
  exact GeneralDictionarySupportEvidence.reachable_joint_evidence registry state root focus reachable key children
    stable selected (joint registry checked state root reachable focus generated stable key children selected)
    model valid dictionaries given

theorem generatedChildren (roles : Roles.RoleDecls) (joint : JointAtSelected roles) :
    B4SkeletonV5.GeneratedChildren (boundary roles) := by
  intro registry checked state root focus key children reachable reached stable safe unique child member
  have generated : Generated state.current root focus := by
    rcases reached with same | reached
    · subst focus; exact .root
    · exact reached
  have selected := (local_correspondence registry state focus (.selected key children)).mp
    (B4TargetV3.Local.selected safe unique)
  have childrenGenerated := (GeneralDictionarySupportEvidence.reachable_joint_instance
    registry state root focus reachable key children stable selected
    (joint registry checked state root reachable focus generated stable key children selected)).2
  exact generated_trans generated (childrenGenerated child member)

/-- Three residuals in addition to the explicit Progress parameter. None is
silently supplied by this package or counted as a completed B4 field. -/
structure Remaining (roles : Roles.RoleDecls) (progress : Progress roles) : Prop where
  joint : JointAtSelected roles
  whereAccessible : ∀ registry, (boundary roles).Checked registry → ∀ state root,
    Reachable (boundary roles) registry root state →
      Acc (Child (B4TargetV3.Local (boundary roles).toSourceBoundary registry state)) root
  canonicalLocalOrder : ∀ registry other, (boundary roles).Checked registry →
    (boundary roles).Checked other → (boundary roles).Reorders registry other → ∀ state root,
      Reachable (boundary roles) registry root state → Reachable (boundary roles) other root state →
      ∀ focus frontier,
        B4TargetV3.Local (boundary roles).toSourceBoundary registry
          ((executor roles progress).run registry state root).1 focus frontier ↔
        B4TargetV3.Local (boundary roles).toSourceBoundary other
          ((executor roles progress).run other state root).1 focus frontier

theorem bridges (roles : Roles.RoleDecls) (progress : Progress roles) (rest : Remaining roles progress) :
    B4SkeletonV5.B4Bridges (boundary roles) (executor roles progress) (frontiers roles) where
  progress := progress
  execution := execution roles progress
  halted := halted roles progress
  closure := closure
  stepModels := stepModels
  frontierLocal := frontierLocal
  localIdentity := localIdentity
  whereAccessible := rest.whereAccessible
  treeExecution := treeExecution roles progress
  canonicalLocalOrder := rest.canonicalLocalOrder
  dictionaryRefl := dictionaryRefl
  evidenceNode := evidenceNode roles rest.joint
  generatedChildren := generatedChildren roles rest.joint
  initialReorders := initialReorders

/-- Conditional V5 composition with the four named residuals still explicit. -/
theorem statement (roles : Roles.RoleDecls) (progress : Progress roles) (rest : Remaining roles progress) :
    B4TargetV5.Statement (boundary roles) (executor roles progress) :=
  B4SkeletonV5.b4_of_bridges _ _ _ (bridges roles progress rest)

end Yulang.GeneralDictionarySupportComposition
