import Yulang.GeneralDeclarativeNormalizedLocal321
import Yulang.GeneralDeclarativeFixtureSupport321

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
namespace Yulang.GeneralDeclarativeFixtureGenerate321
open GeneralDeclarativeExampleSource320
open GeneralDeclarativeExampleRead320 (headExpr rhsExpr childCapture)
open GeneralDeclarativeFixtureSupport321 (support current root_point both_linked one_linked)
open GeneralDeclarationExamples (wrap containerChild outDefinition itemEquation)
open GeneralDeclarativeTraceHead321 (Read)
open GeneralDeclarativeOrdinaryReads321 (Reads)
open GeneralDeclarativeWhereProducer321 (Operand Child ChildName)
open GeneralDeclarativeNodeProducer321 (ReturnRead)
open GeneralDeclarativeNormalizedLocal321 (Generates)
open GeneralDeclarativeSubstitution320 (EquationRead)
open GeneralNominalMaterialization (Mode)
open GeneralDictionaryAssociatedProvenance (Supplies)
open CommonRoleOutermostResolver (All₂)

theorem root_operand : Operand state registry.constructors interp capture (point 3) (.var 0) := by
  have direct (mode : Mode) : Reads state capture mode 3 (.variable 0) := by
    cases mode <;> exact .fact (.structural (.capture (.refl _) (.refl _)))
  exact ⟨.variable 0,rfl,direct _,direct _,direct _⟩

theorem named_item : ChildName state registry.constructors interp capture itemEquation ⟨1,5⟩ :=
  ⟨rfl,.variable 1,rfl,.fact (.structural (.capture (.refl _) (.refl _)))⟩

theorem ordered_child : Child state registry interp capture containerChild child :=
  ⟨rfl,.cons root_operand .nil,.cons named_item .nil⟩

theorem root_return : ReturnRead state registry interp wrap root capture ⟨0,6⟩ := by
  refine ⟨.explicit outDefinition,rhsExpr,.explicit _ List.mem_cons_self rfl,rfl,.fact (.whole ?_)⟩
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))))

theorem leaf_return : ReturnRead state registry interp leaf child childCapture ⟨1,5⟩ := by
  refine ⟨.explicit association,.variable 0,.explicit _ List.mem_cons_self rfl,rfl,.fact (.whole ?_)⟩
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem root_generation : Generates state support registry interp root wrap [child] := by
  refine ⟨capture,[current,current],⟨.cons ⟨headExpr,headExpr,[current,current],rfl,rfl,root_point,?_⟩
    .nil,both_linked⟩,?_,?_,.cons ordered_child .nil,?_⟩
  · intro _ there
    exact there
  · intro n used
    change n ∈ [0] at used
    cases List.mem_singleton.mp used
    exact point_bounds 3
  · intro arg used
    cases List.mem_singleton.mp used
    exact input_bounds
  · intro out used
    cases List.mem_singleton.mp used
    exact root_return

theorem leaf_generation : Generates state support registry interp child leaf [] := by
  refine ⟨childCapture,[current],
    ⟨.cons ⟨.variable 0,.variable 0,[current],rfl,rfl,.actual .capture,?_⟩ .nil,one_linked⟩,
    fun _ _ => point_bounds 3,?_,.nil,?_⟩
  · intro _ there
    exact there
  · intro arg used
    cases List.mem_singleton.mp used
    exact point_bounds 3
  · intro out used
    cases List.mem_singleton.mp used
    exact leaf_return

end Yulang.GeneralDeclarativeFixtureGenerate321
