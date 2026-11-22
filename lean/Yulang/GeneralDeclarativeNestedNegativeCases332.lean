import Yulang.GeneralDeclarativeNestedNegative332

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeNestedNegativeCases332
open GeneralDeclarativeNestedNegative332 (detect actual_obstruction)
open GeneralDeclarativeNestedBracket332 (src state support wanted model model_exists wider pattern)
open GeneralDeclarativeNestedOpaque332 (rhs)
open GeneralDeclarativeNestedExample332 (interpretation)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeHead320 (Models)
open GeneralDeclarativeOpaqueNominal328 (point point_bounded)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeNestedClash332 (pairExpr)
open GeneralNominalCenteredHeadMatExpressions (Expr translate)
open GeneralDeclarationPatterns (normalize)
open GeneralDeclarativeNestedView332 (Sources)
open GeneralDeclarationExamples (constructors)

abbrev target : Expr := .variant 4 (pairExpr (.variable 0) (.record 7 (.variable 1) (.variable 2)))

theorem printed : translate constructors interpretation (normalize pattern) = some target := rfl

theorem detects_lower : (detect 3 wider target).isSome = true := rfl
theorem no_false_from_inside_unknown :
    (detect 4 (.variant 4 (pairExpr (.variable 3) (.variable 20))) target).isSome = false := rfl

/-- A real source read through the actual normalized declaration pattern.
The same syntax at the upper endpoint alone is not such a refutation. -/
theorem checked_point (m) (fit : Models state m) :
    ∃ shape, translate constructors interpretation (normalize pattern) = some shape ∧
      ¬eqAt m (.variable (point 2).center) shape :=
  actual_obstruction (p := support) src (point_bounded state 2) printed rfl detects_lower m fit

end Yulang.GeneralDeclarativeNestedNegativeCases332
