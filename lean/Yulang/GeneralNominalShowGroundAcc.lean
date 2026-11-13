import Yulang.GeneralNominalBranchingAccessibility
import Yulang.GeneralNominalGroundExamples

/-! Unconditional accessibility of the inhabited branching Show source.
Its proof follows both pair positions and the list position through actual
emission, refreshing, reobservation and aliases. -/
namespace Yulang.GeneralNominalShowGroundAcc
open GeneralDeclarations GeneralDeclarationPatterns
open GeneralDeclarationExamples (roles constructors)
open GeneralNominalGroundExamples
open GeneralNominalBranchingReadback GeneralNominalBranchingAccessibility
open GeneralNominalBranchingCaptures
open CommonNominalFullCarrier

theorem branching : Branching roles registry context (fun role => role = 0) := by
  constructor
  · intro role live; cases live; rfl
  · intro declaration visible live nonempty
    rcases List.mem_cons.mp visible with rfl | visible
    · refine ⟨.node .pair [.variables [0],.variables [1]],?_,⟨0,1,rfl⟩,?_⟩
      · simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
          GeneralNominalInspection.translate,interpretation]
      · intro clause member
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨rfl,0,rfl⟩
        · cases List.mem_singleton.mp member; exact ⟨rfl,1,rfl⟩
    rcases List.mem_cons.mp visible with rfl | visible
    · refine ⟨.nominal 0 [.variables [0]],?_,⟨[0],rfl⟩,?_⟩
      · simp [GeneralNominalInspection.queries,Declaration.normalHead,normalizeArgs,normalize,
          GeneralNominalInspection.translate,interpretation,
          show source.constructors = constructors from rfl]
      · intro clause member
        cases List.mem_singleton.mp member
        exact ⟨rfl,0,rfl⟩
    · cases List.mem_singleton.mp visible
      exact False.elim (nonempty rfl)

abbrev inputTree : Tree := .pair (.nominal 0 [.scalar .int]) (.scalar .int)

theorem input_ground (model : GeneralNominalCommonBridge.Assignment)
    (valid : GeneralNominalState.Models source model) : Equivalent (model 2).1 inputTree.value := by
  have facts := (GeneralNominalGroundExamples.models model).mp valid
  have left := GeneralNominalPeelingSources.ground 0 model facts.1
  have right := (GeneralNominalPeelingSources.source_models 0 model).mp facts.1 |>.2
  have pairEqual : Equivalent (pair (model 0).1 (model 1).1)
      (pair (nominal 0 [.inl (.base .int)]) (.base .int)) :=
    ⟨(common_pair_iff ..).mpr ⟨left.1,right.1⟩,(common_pair_iff ..).mpr ⟨left.2,right.2⟩⟩
  exact ⟨subtype_trans facts.2.1 pairEqual.1,subtype_trans pairEqual.2 facts.2.2⟩

theorem depth_bound : GeneralNominalInvocationAncestry.InstalledDepthBound registry context root 4 :=
  installed_depth_bound branching initial_source rfl rfl inputTree input_ground

theorem show_pair_list_int_accessible :
    Acc (fun next current => GeneralNominalActualInspectionSteps.Step registry root current next)
      (GeneralNominalSupport.initial context root) :=
  GeneralNominalActualBudget.accessible_of_installed_depth_bound checked initial_source depth_bound

theorem inhabited_closed_example :
    Checked registry ∧ GeneralNominalSourceFormation.InitialSource registry context root ∧
      GeneralNominalActualBudget.PointSource context root ∧
      (∃ model, GeneralNominalState.Models source model) ∧
      Acc (fun next current => GeneralNominalActualInspectionSteps.Step registry root current next)
        (GeneralNominalSupport.initial context root) :=
  ⟨checked,initial_source,point_source,⟨witness,inhabited⟩,show_pair_list_int_accessible⟩

end Yulang.GeneralNominalShowGroundAcc
