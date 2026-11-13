import Yulang.GeneralNominalGroundHeadMatching
import Yulang.GeneralNominalGroundExamples

/-! The branching Show source is an instance of the general ground-root
accessibility theorem, with no fixture-specific recursion hypothesis. -/
namespace Yulang.GeneralNominalGroundHeadMatchingExample
open GeneralNominalGroundExamples

theorem show_pair_list_int_accessible :
    Acc (fun next current => GeneralNominalActualInspectionSteps.Step registry root current next)
      (GeneralNominalSupport.initial context root) :=
  GeneralNominalGroundHeadMatching.ground_class_p_accessible checked initial_source point_source ground

theorem show_depth_bound :
    GeneralNominalInvocationAncestry.InstalledDepthBound registry context root 4 := by
  simpa only [labels,GeneralNominalPatersonLineage.mass,GeneralDeclarationPatterns.counted,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralDeclarationPatterns.encodeArgs,GeneralDeclarationPatterns.Pattern.encode,Roles.argsSize,Roles.Term.size]
    using GeneralNominalGroundHeadMatching.installed_depth_bound initial_source point_source.rootInputs ground

theorem inhabited_ground_instance :
    GeneralDeclarations.Checked registry ∧
      GeneralNominalSourceFormation.InitialSource registry context root ∧
      GeneralNominalActualBudget.PointSource context root ∧
      GeneralNominalGroundAccessibility.GroundRoots context root labels ∧
      (∃ model, GeneralNominalState.Models source model) ∧
      Acc (fun next current => GeneralNominalActualInspectionSteps.Step registry root current next)
        (GeneralNominalSupport.initial context root) :=
  ⟨checked,initial_source,point_source,ground,⟨witness,inhabited⟩,show_pair_list_int_accessible⟩

end Yulang.GeneralNominalGroundHeadMatchingExample
