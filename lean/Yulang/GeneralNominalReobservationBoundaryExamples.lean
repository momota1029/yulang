import Yulang.GeneralNominalReobservationExamples
import Yulang.GeneralNominalReobservationBoundary

/-! The repaired fork in the new concrete V5 boundary, with the actual Local
and diagnostic tree. This is a finite regression, not arbitrary trace confluence. -/
namespace Yulang.GeneralNominalReobservationBoundaryExamples

open GeneralNominalRefreshFork GeneralNominalReobservationExamples
open GeneralNominalReobservationBoundary
open GeneralDeclarationExamples (roles)
open CommonRoleOutermostResolver

theorem point_local : B4TargetV3.Local (boundary roles).toSourceBoundary
    registry (after false) root (.selected 90 []) :=
  (local_iff_old roles registry (after false) root _).mpr GeneralNominalRefreshDivergence.point_local

theorem point_tree : Resolves (B4TargetV3.Local (boundary roles).toSourceBoundary
    registry (after false)) root (.selected 90 []) := .selected point_local .nil

theorem same_diagnostic : B4TargetV3.SameDiagnostic (boundary roles).toSourceBoundary
    (.selected 90 []) (.selected 90 []) :=
  B4TargetV3.same_diagnostic_refl _ dictionaryRefl _

theorem reachable_point : B4TargetV5.Reachable (boundary roles) registry root (after false) :=
  old_reachable registry (after false) root (after_reachable false)

theorem repaired_fork :
    (boundary roles).Checked registry ∧
    (boundary roles).Initial registry root before ∧
    (∀ wide, (boundary roles).Step registry root before (after wide)) ∧
    (∀ wide, B4Target.Steps ((boundary roles).Step registry root) (after wide) (after false)) ∧
    (∀ next, ¬ (boundary roles).Step registry root (after false) next) ∧
    (boundary roles).Stable registry (after false) root ∧
    (∀ wide model, (boundary roles).Models (after wide) model ↔ (boundary roles).Models (after false) model) ∧
    B4TargetV3.Local (boundary roles).toSourceBoundary registry (after false) root (.selected 90 []) ∧
    Resolves (B4TargetV3.Local (boundary roles).toSourceBoundary registry (after false)) root (.selected 90 []) ∧
    B4TargetV3.SameDiagnostic (boundary roles).toSourceBoundary (.selected 90 []) (.selected 90 []) :=
  ⟨⟨rfl,registry_checked⟩,⟨context none,initial_source,rfl⟩,
    fun wide => GeneralNominalReobservationSteps.old_step (refresh_step wide),fork_extension,point_halted,point_stable,
    fun wide model => (same_models wide model).trans (same_models false model).symm,
    point_local,point_tree,same_diagnostic⟩

end Yulang.GeneralNominalReobservationBoundaryExamples
