import Yulang.GeneralDeclarativeProjectedSharing323
import Yulang.GeneralDeclarativeRepeat320

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeProjectionCheck323
open GeneralDeclarativeProjectedSharing323 (Step Path Compared subAt path_forward)
open GeneralDeclarativeRepeat320 (weak model fits top_not_int)
open GeneralDeclarativeInequality322 (Le sound)
open GeneralDeclarativeRepeatedActual323 (eqAt)
open GeneralDeclarativeHead320 (State Models)
open GeneralNominalCenteredHeadMatExpressions (Expr)
open GeneralNominalCommonBridge (Assignment)

/-- Arbitrary ordinary one-way comparison over a pair of invariant
nominals forces equality under a further covariant projection. -/
theorem nested {s : State} (known : Le s
      (.primitive .pair [.nominal tag [.primitive .pair [x,other]],extra1])
      (.primitive .pair [.nominal tag [.primitive .pair [y,last]],extra2]))
    (m : Assignment) (valid : Models s m) : eqAt m x y := by
  have route :
      Path (.primitive .pair [.nominal tag [.primitive .pair [x,other]],extra1])
        (.primitive .pair [.nominal tag [.primitive .pair [y,last]],extra2]) x y true :=
    .next .left (.next (.invariant 0 rfl rfl) (.next .left .here))
  have got := path_forward route (sound known m valid)
  exact ⟨got.goes,got.returns rfl⟩

abbrev x : Expr := .variable 0
abbrev y : Expr := .variable 2
abbrev tail : Expr := .variable 1
abbrev lhs : Expr := .primitive .pair [x,tail]
abbrev rhs : Expr := .primitive .pair [y,tail]

theorem ordinary_covariant_comparison : Le weak lhs rhs :=
  .pair (.name (.interval (by decide +kernel))) (.refl _)

theorem covariant_not_shared : subAt (model true) x y ∧ ¬eqAt (model true) x y := by
  have route : Path lhs rhs x y false := .next .left .here
  have known := path_forward route (sound ordinary_covariant_comparison _ (fits true))
  exact ⟨known.goes,fun e => top_not_int e.2⟩

end Yulang.GeneralDeclarativeProjectionCheck323
