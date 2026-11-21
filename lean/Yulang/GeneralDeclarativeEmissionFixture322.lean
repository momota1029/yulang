import Yulang.GeneralDeclarativeEmissionLocal322
import Yulang.GeneralDeclarativeExistingFixtureRead322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeEmissionFixture322
open GeneralDeclarativeExistingFixture322 (state supported pointBounds rootBounds parentCapture equations)
open GeneralDeclarativeExistingFixtureRead322 (rootActual rootReturn hit head)
open GeneralDeclarativeExampleSource320 (registry interp input root leaf child point association)
open GeneralDeclarationExamples (wrap containerChild itemEquation)
open GeneralDeclarativeSourceEmission322 (Names)
open GeneralDeclarativeEmissionForest322 (Placement children)
open GeneralDeclarativeEmissionLocal322 (Data Generates)
open GeneralDeclarativeEmissionClause322 (Ready)
open GeneralDeclarativeExistingReturn322 (Settled)
open GeneralDeclarativeTermHead322 (Actual)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarationPatterns (normalize)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open CommonRoleOutermostResolver (All₂)

abbrev names : Names := ⟨parentCapture,fun binder => (parentCapture binder).center⟩
abbrev place : Placement := ⟨fun _ _ => point 400,fun _ _ => 401⟩

theorem actual_names : children wrap names place = [child] := rfl

/-- Both placements are source-defined. Neither a compound operand name
nor a separate output target lookup is used by this real clause. -/
theorem no_materializer_needed :
    Ready state registry interp wrap containerChild names (place.compound containerChild)
      (place.targets containerChild) := by
  constructor
  · refine ⟨[.variable 0],.cons rfl .nil,?_⟩
    intro i pat code one two assumesCompound
    have h := List.mem_singleton.mp (List.mem_of_getElem? one)
    subst pat
    exact False.elim (assumesCompound 0 rfl)
  · intro output member
    cases List.mem_singleton.mp member
    refine ⟨.variable 1,.variable 1,rfl,rfl,?_⟩
    intro notDirect
    exact False.elim (notDirect ⟨1,rfl,List.mem_cons_self⟩)

theorem root_source : Generates state supported registry interp root wrap [child] := by
  refine ⟨names,place,actual_names.symm,.inr (.cons ⟨head,head,rfl,rfl,rootActual⟩ .nil),
    ?_,?_,fun _ _ => rfl,?_,?_⟩
  · intro binder present
    change binder ∈ [0] at present
    cases List.mem_singleton.mp present
    exact pointBounds 3
  · intro arg present
    cases List.mem_singleton.mp present
    exact rootBounds
  · intro clause present
    cases List.mem_singleton.mp present
    exact no_materializer_needed
  · intro out present
    cases List.mem_singleton.mp present
    exact rootReturn

abbrev leafNames : Names := ⟨fun _ => point 3,fun _ => 3⟩

theorem leaf_source : Generates state supported registry interp child leaf [] := by
  have actual : Actual state leafNames.input (point 3) (.variable 0) := by
    refine ⟨.variable 3,[⟨0,.actual,.variable 3⟩],.refl _,.capture,?_⟩
    intro found known
    cases List.mem_singleton.mp known
    exact .refl _
  refine ⟨leafNames,place,rfl,.inr (.cons ⟨.variable 0,.variable 0,rfl,rfl,actual⟩ .nil),
    fun _ _ => pointBounds 3,?_,fun _ _ => rfl,?_,?_⟩
  · intro arg member
    cases List.mem_singleton.mp member
    exact pointBounds 3
  · intro _ empt
    cases empt
  · intro out member
    cases List.mem_singleton.mp member
    exact ⟨.explicit association,.variable 0,.variable 0,.explicit _ List.mem_cons_self rfl,
      rfl,rfl,hit 5 (.variable 3) (by simp [equations])⟩

end Yulang.GeneralDeclarativeEmissionFixture322
