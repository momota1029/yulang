import Yulang.GeneralNominalActualBoundary
import Yulang.GeneralNominalIndexedHoleReadback
import Yulang.GeneralNominalGroundExamples

/-! Exact V5 progress for point sources, conditional on the remaining hole
phase construction. Ground sources already construct the phase certificate. -/
namespace Yulang.GeneralNominalActualPhaseBoundary
open GeneralDeclarations GeneralSourceDictionaries GeneralNominalSaturationState
open GeneralNominalSupport GeneralNominalActualInspectionSteps B4TargetV5
open GeneralNominalActualBoundary (vocabulary)

variable {roles : Roles.RoleDecls}

def boundary (roles : Roles.RoleDecls) : SourceBoundary (vocabulary roles) :=
  { GeneralNominalActualBoundary.boundary roles with
    Initial := fun registry root state => ∃ context,
      GeneralNominalSourceFormation.InitialSource registry context root ∧
      GeneralNominalActualBudget.PointSource context root ∧ state = GeneralNominalSupport.initial context root }

theorem progress (phases : GeneralNominalHolePhases.ClassPHolePhases roles)
    (registry : Registry) (checked : (boundary roles).Checked registry)
    (state : Tracked roles) (root : Occurrence roles) (reachable : Reachable (boundary roles) registry root state) :
    Acc (fun next current => (boundary roles).Step registry root current next) state := by
  obtain ⟨start,⟨context,source,point,rfl⟩,path⟩ := reachable
  have accessible := GeneralNominalHolePhases.class_p_accessible phases checked.2 source point
  induction path with
  | refl => exact accessible
  | tail path step ih => exact ih.inv step

theorem initialReorders (registry other : Registry) (order : (boundary roles).Reorders registry other)
    (state : Tracked roles) (root : Occurrence roles) (given : (boundary roles).Initial registry root state) :
    (boundary roles).Initial other root state := by
  obtain ⟨context,source,point,same⟩ := given
  exact ⟨context,GeneralDictionaryInitialSource.source_reorders registry other order context root source,point,same⟩

theorem ground_phase_cover (checked : Checked registry)
    (source : GeneralNominalSourceFormation.InitialSource registry context (root : Occurrence roles))
    (point : GeneralNominalActualBudget.PointSource context root)
    (ground : GeneralNominalGroundAccessibility.GroundRoots context root labels) :
    Nonempty (GeneralNominalHolePhases.PhaseCover registry context root) :=
  GeneralNominalHolePhases.of_depth_bound checked source
    (GeneralNominalGroundHeadMatching.installed_depth_bound source point.rootInputs ground)

namespace Show
open GeneralNominalGroundExamples

theorem phase_accessible :
    Acc (fun next current => Step registry root current next) (GeneralNominalSupport.initial context root) := by
  obtain ⟨cover⟩ := ground_phase_cover checked initial_source point_source ground
  exact GeneralNominalHolePhases.accessible cover initial_source

theorem v5_progress :
    Acc (fun next current => (GeneralNominalActualBoundary.groundBoundary GeneralDeclarationExamples.roles).Step registry root current next)
      (GeneralNominalSupport.initial context root) := by
  apply GeneralNominalActualBoundary.ground_progress registry ⟨rfl,checked⟩ _ root
  exact reachable_initial (GeneralNominalActualBoundary.groundBoundary GeneralDeclarationExamples.roles)
    ⟨context,labels,initial_source,point_source,ground,rfl⟩

end Show
end Yulang.GeneralNominalActualPhaseBoundary
