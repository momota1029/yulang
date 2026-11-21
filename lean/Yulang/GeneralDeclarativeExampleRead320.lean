import Yulang.GeneralDeclarativeExampleSource320

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
namespace Yulang.GeneralDeclarativeExampleRead320
open GeneralDeclarationExamples (wrap containerChild outDefinition itemEquation constructors roles)
open GeneralDeclarativeExampleSource320
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeHead320 (Read)
open GeneralDeclarativeAssembly320 (Prepared Named WhereChild ChosenRecipe)
open GeneralDeclarativeNormalized320 (NormalArg Center)
open GeneralDeclarativeSubstitution320 (EquationRead)
open GeneralDeclarativePoint320 (frozen_nominal)
open GeneralDeclarativeOutputs320 (ChildOutput)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDictionaryAssociatedProvenance (Body)

abbrev headExpr : Expr := .nominal 0 [.variable 0]
abbrev rhsExpr : Expr := .nominal 0 [.variable 1]

theorem root_only (d) (visible : d ∈ registry.declarations) (same : d.role = root.role) :
    d = wrap := by
  rcases List.mem_cons.mp visible with rfl|tail
  · rfl
  · cases List.mem_singleton.mp tail
    have impossible : (2 : Nat) = 1 := same
    cases impossible

theorem leaf_only (d) (visible : d ∈ registry.declarations) (same : d.role = child.role) :
    d = leaf := by
  rcases List.mem_cons.mp visible with rfl|tail
  · have impossible : (1 : Nat) = 2 := same
    cases impossible
  · exact List.mem_singleton.mp tail

theorem root_head_read : Center state capture input headExpr := by
  refine Center.endpoints input_bounds (frozen_nominal state capture 0 [.variable 0]) ?_ ?_
  · exact .whole List.mem_cons_self
  · exact .whole (List.mem_cons_of_mem _ List.mem_cons_self)

theorem argument : NormalArg state constructors interp capture (point 3) (.var 0) := by
  have pr : ∀ mode, EquationRead state capture mode 3 (.variable 0) := by
    intro mode
    cases mode <;> exact .structural (.capture (.refl _) (.refl _))
  exact ⟨.variable 0,rfl,pr .lower,pr .upper,.direct (pr .actual)⟩

theorem child_out :
    ChildOutput state constructors interp capture itemEquation ⟨1,5⟩ := by
  exact ⟨rfl,.variable 1,rfl,.capture (.refl _) (.refl _)⟩

theorem issued :
    WhereChild state constructors interp capture containerChild child :=
  ⟨rfl,.cons argument .nil,.cons child_out .nil⟩

theorem root_output :
    Named state registry interp root wrap capture ⟨0,6⟩ := by
  refine ⟨.explicit outDefinition,rhsExpr,rfl,rfl,.whole ?_⟩
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ (List.mem_singleton_self _))))

theorem root_prepared : Prepared state registry interp wrap root capture [child] := by
  refine ⟨List.mem_cons_self,rfl,?_,.cons ⟨input_bounds,headExpr,rfl,root_head_read⟩ .nil,
    .cons issued .nil,?_⟩
  · intro n used
    change n ∈ [0] at used
    cases List.mem_singleton.mp used
    exact point_bounds 3
  · intro out used
    cases List.mem_singleton.mp used
    exact root_output

abbrev childCapture : Nat → Capture := fun _ => point 3

theorem leaf_prepared : Prepared state registry interp leaf child childCapture [] := by
  have read : EquationRead state childCapture .actual 3 (.variable 0) :=
    .structural (.capture (.refl _) (.refl _))
  refine ⟨List.mem_cons_of_mem _ (List.mem_singleton_self _),rfl,fun _ _ => point_bounds 3,
    .cons ⟨point_bounds 3,.variable 0,rfl,.direct read⟩ .nil,.nil,?_⟩
  intro out used
  cases List.mem_singleton.mp used
  refine ⟨.explicit association,.variable 0,rfl,rfl,.whole ?_⟩
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))

theorem root_recipe : ChosenRecipe state registry interp root wrap.id [child] :=
  ⟨wrap,capture,rfl,root_prepared⟩

theorem leaf_recipe : ChosenRecipe state registry interp child leaf.id [] :=
  ⟨leaf,childCapture,rfl,leaf_prepared⟩

end Yulang.GeneralDeclarativeExampleRead320
