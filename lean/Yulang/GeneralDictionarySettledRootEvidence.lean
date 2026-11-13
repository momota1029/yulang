import Yulang.GeneralDictionarySettledTreeEvidence

/-! Root-only settled stability suffices for selected dictionary descendants.
Joint is still explicit at each selected descendant; all evidence is evaluated
in models of the final context. -/
namespace Yulang.GeneralDictionarySettledRootEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open GeneralNominalSaturationState GeneralDictionaryRecursiveEvidence
open CommonRoleOutermostResolver GeneralDictionarySettledProjection
open GeneralDictionarySettledTreeEvidence
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}

/-- Applicability only on selected descendants, without per-node stability. -/
def JointClosure (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ child, B4Target.Steps (fun parent child => Child
    (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) child parent) root child →
    ∀ key children, B4TargetV3.Local (fresh roles).toSourceBoundary registry state child
      (.selected key children) → GeneralNominalJointCandidates.Joint registry state.current child key

theorem stable_generated {root child : Occurrence roles}
    (stable : GeneralNominalSettledSteps.Stable registry state root)
    (generated : Generated state.current root child) :
    GeneralNominalSettledSteps.Stable registry state child :=
  fun focus reached => stable focus (generated_trans generated reached)

/-- Selected-child paths become actual generated paths using guarded committed
instances; syntactic selection alone is not treated as generation. -/
theorem selected_descendant_generated {source root child : Occurrence roles}
    (reachable : B4TargetV5.Reachable (fresh roles) registry source state)
    (stable : GeneralNominalSettledSteps.Stable registry state root)
    (joint : JointClosure registry state root)
    (path : B4Target.Steps (fun parent child => Child
      (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) child parent) root child) :
    Generated state.current root child := by
  induction path with
  | refl => exact .root
  | tail prior edge ih =>
    obtain ⟨key,children,selected,member⟩ := edge
    have instanceRule := GeneralDictionarySettledEvidence.reachable_joint_instance registry state source _
      reachable key children (stable_generated stable ih)
      ((GeneralNominalSettledBoundary.local_correspondence registry state _ _).mp selected)
      (joint _ prior key children selected)
    exact generated_trans ih (instanceRule.2 _ member)

theorem nodeClosure_of_root_stable {source root : Occurrence roles}
    (reachable : B4TargetV5.Reachable (fresh roles) registry source state)
    (stable : GeneralNominalSettledSteps.Stable registry state root)
    (joint : JointClosure registry state root) : NodeClosure registry state root := by
  intro child path
  exact ⟨stable_generated stable (selected_descendant_generated reachable stable joint path),joint child path⟩

/-- Full finite selected dictionary evidence from one root-stability premise. -/
theorem classified_evidence {source root : Occurrence roles} {dictionary : Dictionary}
    (reachable : B4TargetV5.Reachable (fresh roles) registry source state)
    (stable : GeneralNominalSettledSteps.Stable registry state root)
    (joint : JointClosure registry state root)
    (classified : B4TargetV3.Classify (fresh roles).toSourceBoundary registry state root (.selected dictionary))
    (model : Assignment) (valid : Models state.current model) :
    Evidence registry state.current.context model root dictionary :=
  GeneralDictionarySettledTreeEvidence.classified_evidence source root reachable dictionary classified
    (nodeClosure_of_root_stable reachable stable joint) model valid

theorem completed_evidence {source root : Occurrence roles} {tree : Tree} {dictionary : Dictionary}
    (reachable : B4TargetV5.Reachable (fresh roles) registry source state)
    (stable : GeneralNominalSettledSteps.Stable registry state root)
    (joint : JointClosure registry state root)
    (resolved : Resolves (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) root tree)
    (completed : B4TargetV3.Completed tree (.selected dictionary))
    (model : Assignment) (valid : Models state.current model) :
    Evidence registry state.current.context model root dictionary :=
  GeneralDictionarySettledTreeEvidence.completed_evidence reachable resolved completed
    (nodeClosure_of_root_stable reachable stable joint) model valid
end Yulang.GeneralDictionarySettledRootEvidence
