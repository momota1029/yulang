import Yulang.GeneralNominalRefreshDivergence

/-! Exact residual execution order obligation for the progress-based driver.
Agreement of arbitrary halted outcomes would suffice, but the actual feedback
relation refutes that proposed confluence premise, even without reordering. -/
namespace Yulang.GeneralDictionaryExecutorOrderResidual

open GeneralDictionaryReachableBoundary GeneralDictionaryFeedbackExecutor
open GeneralDictionaryCanonicalLocalOrder
open B4TargetV5
open B4TargetV3 (Local)
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState

def HaltedLocalOrder (roles : Roles.RoleDecls) : Prop :=
  ∀ r r', (boundary roles).Checked r → (boundary roles).Checked r' →
    (boundary roles).Reorders r r' → ∀ s root,
    Reachable (boundary roles) r root s → Reachable (boundary roles) r' root s → ∀ left right,
    B4Target.Steps ((boundary roles).Step r root) s left →
    B4Target.Steps ((boundary roles).Step r' root) s right →
    (∀ next, ¬ (boundary roles).Step r root left next) →
    (∀ next, ¬ (boundary roles).Step r' root right next) → ∀ d f,
    Local (boundary roles).toSourceBoundary r left d f ↔
      Local (boundary roles).toSourceBoundary r' right d f

theorem canonicalLocalOrder_of_halted_order (roles : Roles.RoleDecls) (progress : Progress roles)
    (agree : HaltedLocalOrder roles) : CanonicalLocalOrder roles (executor roles progress) := by
  intro r r' checked checked' reordered s root reached reached' d f
  exact agree r r' checked checked' reordered s root reached reached' _ _
    (execution roles progress r checked s root reached) (execution roles progress r' checked' s root reached')
    (halted roles progress r checked s root reached) (halted roles progress r' checked' s root reached') d f

theorem not_halted_local_order : ¬ HaltedLocalOrder GeneralDeclarationExamples.roles := by
  intro agree
  open GeneralNominalRefreshFork GeneralNominalRefreshDivergence in
    have contradictory := agree registry registry ⟨rfl,registry_checked⟩ ⟨rfl,registry_checked⟩
      (GeneralRegistryReordering.reorders_refl registry) before root initial_reachable initial_reachable
      (after false) (after true) (.tail .refl (refresh_step false)) (.tail .refl (refresh_step true))
      (GeneralNominalRefreshDivergence.halted false) (GeneralNominalRefreshDivergence.halted true)
    exact different_local contradictory

/-- Only four obligations remain as fields here; progress is an explicit
parameter, not a theorem derived by this package. -/
structure Remaining (roles : Roles.RoleDecls) (progress : Progress roles) : Prop where
  whereAccessible : ∀ r, (boundary roles).Checked r → ∀ s root, Reachable (boundary roles) r root s →
    Acc (CommonRoleOutermostResolver.Child (Local (boundary roles).toSourceBoundary r s)) root
  canonicalLocalOrder : CanonicalLocalOrder roles (executor roles progress)
  evidenceNode : B4SkeletonV5.EvidenceNode (boundary roles)
  generatedChildren : B4SkeletonV5.GeneratedChildren (boundary roles)

theorem remaining (roles : Roles.RoleDecls) (progress : Progress roles) (rest : Remaining roles progress) :
    GeneralDictionaryReachableObligations.Remaining roles (executor roles progress) where
  progress := progress
  execution := execution roles progress
  halted := halted roles progress
  whereAccessible := rest.whereAccessible
  treeExecution := treeExecution roles progress
  canonicalLocalOrder := rest.canonicalLocalOrder
  evidenceNode := rest.evidenceNode
  generatedChildren := rest.generatedChildren

theorem bridges (roles : Roles.RoleDecls) (progress : Progress roles) (rest : Remaining roles progress) :
    B4SkeletonV5.B4Bridges (boundary roles) (executor roles progress) (frontiers roles) :=
  GeneralDictionaryReachableObligations.bridges_of_remaining roles (executor roles progress) (remaining roles progress rest)

end Yulang.GeneralDictionaryExecutorOrderResidual
