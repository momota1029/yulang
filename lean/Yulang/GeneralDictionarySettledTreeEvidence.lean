import Yulang.GeneralDictionarySettledEvidence

/-! Full finite dictionaries under explicit, descendant-local Stable and Joint
hypotheses. The conclusion concerns models of the final context only. This does
not discharge general Joint or construct the boundary's unconditional EvidenceNode. -/
namespace Yulang.GeneralDictionarySettledTreeEvidence
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSupport
open GeneralNominalSaturationState GeneralDictionaryRecursiveEvidence
open CommonRoleOutermostResolver GeneralDictionarySettledProjection
open GeneralNominalCommonBridge (Assignment)
variable {roles : Roles.RoleDecls} {registry : Registry} {state : Tracked roles}

/-- Only the selected descendants of the requested root need Stable and Joint.
The Joint premise is indexed by the selected key, not by an arbitrary declaration. -/
def NodeClosure (registry : Registry) (state : Tracked roles) (root : Occurrence roles) : Prop :=
  ∀ child, B4Target.Steps (fun parent child => Child
    (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) child parent) root child →
    GeneralNominalSettledSteps.Stable registry state child ∧
      ∀ key children, B4TargetV3.Local (fresh roles).toSourceBoundary registry state child
        (.selected key children) → GeneralNominalJointCandidates.Joint registry state.current child key

theorem nodeClosure_child {root child : Occurrence roles} (closed : NodeClosure registry state root)
    (edge : Child (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) child root) :
    NodeClosure registry state child := by
  intro descendant path
  apply closed descendant
  induction path with
  | refl => exact .tail .refl edge
  | tail _ next ih => exact .tail ih next

mutual
  theorem classified_evidence (source root : Occurrence roles)
      (reachable : B4TargetV5.Reachable (fresh roles) registry source state)
      (dictionary : Dictionary)
      (classified : B4TargetV3.Classify (fresh roles).toSourceBoundary registry state root (.selected dictionary))
      (closed : NodeClosure registry state root)
      (model : Assignment) (valid : Models state.current model) :
      Evidence registry state.current.context model root dictionary := by
    match dictionary, classified with
    | .node key dictionaries, .selected safe unique all =>
      have localRule : B4TargetV3.Local (fresh roles).toSourceBoundary registry state root
          (.selected key _) := .selected safe unique
      have rootReady := closed root .refl
      apply GeneralDictionarySettledEvidence.reachable_joint_evidence registry state source root reachable
        key _ rootReady.1
        ((GeneralNominalSettledBoundary.local_correspondence registry state root _).mp localRule)
        (rootReady.2 _ _ localRule) model valid dictionaries
      exact children_evidence source reachable dictionaries _ all
        (fun child member => nodeClosure_child closed ⟨key,_,localRule,member⟩) model valid
  termination_by sizeOf dictionary

  theorem children_evidence (source : Occurrence roles)
      (reachable : B4TargetV5.Reachable (fresh roles) registry source state)
      (dictionaries : List Dictionary) (roots : List (Occurrence roles))
      (classified : All₂ (fun root dictionary => B4TargetV3.Classify
        (fresh roles).toSourceBoundary registry state root (.selected dictionary)) roots dictionaries)
      (closed : ∀ child ∈ roots, NodeClosure registry state child)
      (model : Assignment) (valid : Models state.current model) :
      All₂ (Evidence registry state.current.context model) roots dictionaries := by
    cases classified with
    | nil => exact .nil
    | cons first rest =>
      exact .cons (classified_evidence source _ reachable _ first (closed _ (by simp)) model valid)
        (children_evidence source reachable _ _ rest (fun child member => closed child (by simp [member])) model valid)
  termination_by sizeOf dictionaries
end

/-- Completed diagnostic trees inherit the same conditional final-model soundness. -/
theorem completed_evidence {source root : Occurrence roles} {tree : Tree} {dictionary : Dictionary}
    (reachable : B4TargetV5.Reachable (fresh roles) registry source state)
    (resolved : Resolves (B4TargetV3.Local (fresh roles).toSourceBoundary registry state) root tree)
    (completed : B4TargetV3.Completed tree (.selected dictionary))
    (closed : NodeClosure registry state root)
    (model : Assignment) (valid : Models state.current model) :
    Evidence registry state.current.context model root dictionary :=
  classified_evidence source root reachable dictionary
    (B4TargetV3.tree_classifies _ _ _ _ _ _ resolved completed) closed model valid
end Yulang.GeneralDictionarySettledTreeEvidence
