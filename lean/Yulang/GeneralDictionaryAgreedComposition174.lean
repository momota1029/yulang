import Yulang.GeneralDictionaryAgreedGround174
import Yulang.GeneralDictionaryAgreedEvidence174

/-! Conditional composition only. Ground termination is proved; current-context
history, recursive diagnostic accessibility and registry-order independence
remain named obligations. The pending policy is an implementation restriction.
For the complete policy the separate provenance GapFree obligation remains. -/
namespace Yulang.GeneralDictionaryAgreedComposition174
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualAgreedLocal
open GeneralDictionaryAgreedGround174
open CommonRoleOutermostResolver B4TargetV5
variable {roles : Roles.RoleDecls} {defer : Bool} {gap : GapPredicate roles}

structure Remaining (defer : Bool) (gap : GapPredicate roles) : Prop where
  policy : defer = true ∨ GeneralNominalActualAgreedBoundary.GapFree gap
  history : GeneralDictionaryAgreedEvidence174.ReachableRecordedExtensions defer gap
  whereAccessible : ∀ registry, (boundary defer gap).Checked registry → ∀ state root,
    Reachable (boundary defer gap) registry root state →
      Acc (Child (B4TargetV3.Local (boundary defer gap).toSourceBoundary registry state)) root
  canonicalLocalOrder : ∀ registry other, (boundary defer gap).Checked registry →
    (boundary defer gap).Checked other → (boundary defer gap).Reorders registry other → ∀ state root,
    Reachable (boundary defer gap) registry root state → Reachable (boundary defer gap) other root state →
    ∀ focus frontier,
      B4TargetV3.Local (boundary defer gap).toSourceBoundary registry
        ((executor defer gap).run registry state root).1 focus frontier ↔
      B4TargetV3.Local (boundary defer gap).toSourceBoundary other
        ((executor defer gap).run other state root).1 focus frontier

theorem policy_at (rest : Remaining defer gap)
    (registry : Registry) (checked : (GeneralNominalActualAgreedBoundary.boundary defer gap).Checked registry)
    (state : Tracked roles) (root : Occurrence roles)
    (reachable : Reachable (GeneralNominalActualAgreedBoundary.boundary defer gap) registry root state)
    (focus : Occurrence roles) : defer = true ∨ ¬ gap registry state focus := by
  rcases rest.policy with yes | free
  · exact Or.inl yes
  · exact Or.inr (free registry checked state root reachable focus)

theorem evidenceNode (rest : Remaining defer gap) :
    B4SkeletonV5.EvidenceNode (boundary defer gap) := by
  intro registry checked state root reachable
  exact GeneralDictionaryAgreedEvidence174.evidenceNode_of_policy rest.history
    (policy_at rest) registry checked state root (reachable_agreed reachable)

theorem generatedChildren (rest : Remaining defer gap) :
    B4SkeletonV5.GeneratedChildren (boundary defer gap) := by
  intro registry checked state root focus key children reachable
  exact GeneralNominalActualAgreedBoundary.generatedChildren_of_policy (policy_at rest)
    registry checked state root focus key children (reachable_agreed reachable)

theorem generatedChildren_pending : B4SkeletonV5.GeneratedChildren (boundary true gap) := by
  intro registry checked state root focus key children reachable
  exact GeneralNominalActualAgreedBoundary.generatedChildren_pending
    registry checked state root focus key children (reachable_agreed reachable)

theorem bridges (defer : Bool) (gap : GapPredicate roles) (rest : Remaining defer gap) :
    B4SkeletonV5.B4Bridges (boundary defer gap) (executor defer gap)
      (GeneralNominalActualAgreedBoundary.frontiers defer gap) where
  progress := progress defer gap
  execution := execution defer gap
  halted := halted defer gap
  closure := fun registry checked state root reachable =>
    GeneralNominalActualAgreedBoundary.closure registry checked state root (reachable_agreed reachable)
  stepModels := fun registry checked root before after reachable =>
    GeneralNominalActualAgreedBoundary.stepModels registry checked root before after (reachable_agreed reachable)
  frontierLocal := fun registry checked state root reachable =>
    GeneralNominalActualAgreedBoundary.frontierLocal registry checked state root (reachable_agreed reachable)
  localIdentity := fun registry state root reachable =>
    GeneralNominalActualAgreedBoundary.localIdentity registry state root (reachable_agreed reachable)
  whereAccessible := rest.whereAccessible
  treeExecution := treeExecution defer gap
  canonicalLocalOrder := rest.canonicalLocalOrder
  dictionaryRefl := GeneralNominalActualAgreedBoundary.dictionaryRefl
  evidenceNode := evidenceNode rest
  generatedChildren := generatedChildren rest
  initialReorders := fun registry other _ _ order state root given =>
    initialReorders defer gap registry other order state root given

theorem statement (defer : Bool) (gap : GapPredicate roles) (rest : Remaining defer gap) :
    B4TargetV5.Statement (boundary defer gap) (executor defer gap) :=
  B4SkeletonV5.b4_of_bridges _ _ _ (bridges defer gap rest)

end Yulang.GeneralDictionaryAgreedComposition174
