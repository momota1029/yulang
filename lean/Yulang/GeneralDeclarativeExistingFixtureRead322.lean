import Yulang.GeneralDeclarativeExistingFixture322
import Yulang.GeneralDeclarativeSourceCodes321

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 14000
namespace Yulang.GeneralDeclarativeExistingFixtureRead322
open GeneralDeclarativeExistingFixture322
open GeneralDeclarativeExampleSource320 (registry interp root input leaf association)
open GeneralDeclarationExamples (wrap containerChild outDefinition itemEquation)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeHead320 (Equation)
open GeneralDeclarativeExistingClause322 (Refers NamedRefers Existing)
open GeneralDeclarativeExistingReturn322 (Settled)
open GeneralDeclarativeExistingLocal322 (Proven Heads)
open GeneralDeclarativeTermHead322 (Actual)
open GeneralDeclarativeTermWalk322 (Walk Occurrence Binds)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralDictionaryAssociatedProvenance (Supplies)
open CommonRoleOutermostResolver (All₂)

abbrev head : Expr := .nominal 0 [.variable 0]
abbrev ownRhs : Expr := .nominal 0 [.variable 1]

theorem hit (n : Nat) (term : Expr) (known : (⟨n,term⟩ : Equation) ∈ equations) :
    Derives state (.variable n) term := .row known

theorem rootActual : Actual state parentCapture input head := by
  let read : Occurrence := ⟨0,.actual,product⟩
  refine ⟨nominalCode product,[read],hit 1 (nominalCode product) (by simp [equations]),
    .nominal (.cons .capture .nil),?_⟩
  intro o found
  cases List.mem_singleton.mp found
  exact .symm (hit 3 product (by simp [equations]))

theorem centerPath : Derives state (.variable 9) (.variable 3) :=
  .trans (hit 9 (.variable 4) (by simp [equations])) (hit 4 (.variable 3) (by simp [equations]))

theorem whereRead : Refers state parentCapture (.variable 0) frame :=
  ⟨hit 8 (.variable 3) (by simp [equations]),centerPath,hit 10 (.variable 3) (by simp [equations])⟩

theorem namedPath : Derives state (.variable 12) (.variable 5) :=
  .trans (hit 12 (.variable 13) (by simp [equations])) (hit 13 (.variable 5) (by simp [equations]))

theorem whereExisting : Existing state registry interp parentCapture containerChild child :=
  ⟨rfl,[.variable 0],[(1,.variable 1)],⟨.cons rfl .nil,.cons ⟨rfl,rfl⟩ .nil⟩,
    .cons whereRead .nil,.cons ⟨rfl,namedPath⟩ .nil⟩

theorem rootReturn : Settled state registry interp wrap root parentCapture ⟨0,6⟩ := by
  refine ⟨.explicit outDefinition,ownRhs,ownRhs,.explicit _ List.mem_cons_self rfl,rfl,rfl,?_⟩
  exact .trans (hit 6 (.variable 14) (by simp [equations]))
    (.trans (hit 14 (nominalCode (.variable 15)) (by simp [equations]))
      (.nominal (.cons (hit 15 (.variable 5) (by simp [equations])) .nil)))

theorem leafReturn : Settled state registry interp leaf child leafCapture ⟨1,12⟩ := by
  refine ⟨.explicit association,.variable 0,.variable 0,.explicit _ List.mem_cons_self rfl,rfl,rfl,?_⟩
  exact .trans namedPath (.trans (hit 5 (.variable 3) (by simp [equations])) (.symm centerPath))

theorem rootBuilt : Proven state supported registry interp root wrap [child] := by
  refine ⟨parentCapture,.inr (.cons ⟨head,head,rfl,rfl,rootActual⟩ .nil),
    ?_,?_,.cons whereExisting .nil,?_⟩
  · intro n seen
    change n ∈ [0] at seen
    cases List.mem_singleton.mp seen
    exact pointBounds 3
  · intro arg seen
    cases List.mem_singleton.mp seen
    exact rootBounds
  · intro out seen
    cases List.mem_singleton.mp seen
    exact rootReturn

theorem childBuilt : Proven state supported registry interp child leaf [] := by
  have actual : Actual state leafCapture frame (.variable 0) := by
    refine ⟨.variable 9,[⟨0,.actual,.variable 9⟩],.refl _,.capture,?_⟩
    intro o seen
    cases List.mem_singleton.mp seen
    exact .refl _
  refine ⟨leafCapture,.inr (.cons ⟨.variable 0,.variable 0,rfl,rfl,actual⟩ .nil),
    fun _ _ => pointBounds 9,?_,.nil,?_⟩
  · intro arg seen
    cases List.mem_singleton.mp seen
    exact childBounds
  · intro out seen
    cases List.mem_singleton.mp seen
    exact leafReturn

end Yulang.GeneralDeclarativeExistingFixtureRead322
