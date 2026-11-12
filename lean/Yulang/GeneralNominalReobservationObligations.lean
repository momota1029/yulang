import Yulang.GeneralNominalReobservationExecutor
import Yulang.B4SkeletonV5

/-! Exact residuals for the point-reobservation boundary. Six V5 fields are
unconditional. Three execution fields follow from Progress alone. The other
four fields remain explicit, including final-state order agreement. -/
namespace Yulang.GeneralNominalReobservationObligations

open GeneralNominalReobservationBoundary GeneralNominalReobservationExecutor
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open CommonRoleOutermostResolver
open B4TargetV5
open B4TargetV3 (Local)

variable (roles : Roles.RoleDecls)

structure Remaining (progress : Progress roles) : Prop where
  whereAccessible : ∀ r, (boundary roles).Checked r → ∀ s root, Reachable (boundary roles) r root s →
    Acc (Child (Local (boundary roles).toSourceBoundary r s)) root
  canonicalLocalOrder : ∀ r r', (boundary roles).Checked r → (boundary roles).Checked r' →
    (boundary roles).Reorders r r' → ∀ s root, Reachable (boundary roles) r root s →
    Reachable (boundary roles) r' root s → ∀ d f,
    Local (boundary roles).toSourceBoundary r ((executor roles progress).run r s root).1 d f ↔
      Local (boundary roles).toSourceBoundary r' ((executor roles progress).run r' s root).1 d f
  evidenceNode : B4SkeletonV5.EvidenceNode (boundary roles)
  generatedChildren : B4SkeletonV5.GeneratedChildren (boundary roles)

theorem bridges (progress : Progress roles) (remaining : Remaining roles progress) :
    B4SkeletonV5.B4Bridges (boundary roles) (executor roles progress) (frontiers roles) where
  progress := progress
  execution := execution roles progress
  halted := halted roles progress
  closure := closure
  stepModels := stepModels
  frontierLocal := frontierLocal
  localIdentity := localIdentity
  whereAccessible := remaining.whereAccessible
  treeExecution := treeExecution roles progress
  canonicalLocalOrder := remaining.canonicalLocalOrder
  dictionaryRefl := dictionaryRefl
  evidenceNode := remaining.evidenceNode
  generatedChildren := remaining.generatedChildren
  initialReorders := initialReorders

/-- A precise unresolved final-state premise, not an asserted confluence law. -/
def HaltedLocalOrder : Prop :=
  ∀ r r', (boundary roles).Checked r → (boundary roles).Checked r' → (boundary roles).Reorders r r' →
    ∀ s root, Reachable (boundary roles) r root s → Reachable (boundary roles) r' root s →
    ∀ left right, B4Target.Steps ((boundary roles).Step r root) s left →
      B4Target.Steps ((boundary roles).Step r' root) s right →
      (∀ next, ¬ (boundary roles).Step r root left next) →
      (∀ next, ¬ (boundary roles).Step r' root right next) →
      ∀ d f, Local (boundary roles).toSourceBoundary r left d f ↔ Local (boundary roles).toSourceBoundary r' right d f

theorem canonicalLocalOrder_of_halted_order (progress : Progress roles) (agreement : HaltedLocalOrder roles) :
    ∀ r r', (boundary roles).Checked r → (boundary roles).Checked r' → (boundary roles).Reorders r r' →
      ∀ s root, Reachable (boundary roles) r root s → Reachable (boundary roles) r' root s →
      ∀ d f, Local (boundary roles).toSourceBoundary r ((executor roles progress).run r s root).1 d f ↔
        Local (boundary roles).toSourceBoundary r' ((executor roles progress).run r' s root).1 d f := by
  intro r r' checked checked' order s root reached reached'
  exact agreement r r' checked checked' order s root reached reached' _ _
    (execution roles progress r checked s root reached) (execution roles progress r' checked' s root reached')
    (halted roles progress r checked s root reached) (halted roles progress r' checked' s root reached')

end Yulang.GeneralNominalReobservationObligations
