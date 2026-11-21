import Yulang.GeneralDeclarativeRepeatedActual323
import Yulang.GeneralDeclarativeInequality322

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativePairCenters326
open GeneralDeclarativeHead320 (State Models)
open GeneralDeclarativeWhere319 (Capture)
open GeneralDeclarativeEqualities322 (Derives)
open GeneralDeclarativeDemand320 (Bounds)
open GeneralDeclarativeInequality322 (Le Equal equal_sound)
open GeneralNominalCenteredHeadMatExpressions (Expr)

def pair (a b : Expr) : Expr := .primitive .pair [a,b]

/-- Real ordinary projection from a named parent seen in two forms.
No endpoint is substituted for the covariant component's actual value. -/
theorem project_first {s : State}
    (parent : Derives s (.variable host) (pair (.variable child) spare))
    (visible : Derives s (.variable host) (pair first second)) :
    Derives s (.variable child) first :=
  .pairFirst (.trans (.symm parent) visible)

theorem project_second {s : State}
    (parent : Derives s (.variable host) (pair spare (.variable child)))
    (visible : Derives s (.variable host) (pair first second)) :
    Derives s (.variable child) second :=
  .pairSecond (.trans (.symm parent) visible)

/-- Compare the actual covariant pair to its two endpoints. Both
coordinates keep separate lower, actual and upper expressions. -/
theorem coordinate_ranges {s : State} {a : Capture} (bound : Bounds s a)
    (lower : Derives s (.variable a.lower) (pair l₁ l₂))
    (actual : Derives s (.variable a.center) (pair c₁ c₂))
    (upper : Derives s (.variable a.upper) (pair u₁ u₂)) :
    (Le s l₁ c₁ ∧ Le s c₁ u₁) ∧ (Le s l₂ c₂ ∧ Le s c₂ u₂) := by
  have toward : Le s (pair l₁ l₂) (pair c₁ c₂) :=
    .trans (.eqn (.symm lower)) (.trans (.name bound.1) (.eqn actual))
  have away : Le s (pair c₁ c₂) (pair u₁ u₂) :=
    .trans (.eqn (.symm actual)) (.trans (.name bound.2) (.eqn upper))
  exact ⟨⟨.pairFirst toward,.pairFirst away⟩,⟨.pairSecond toward,.pairSecond away⟩⟩

/-- An ordinary equality between projected centers shares a repeated
binder. Coincidence of the two endpoint projections is not used. -/
theorem shared_actual {s : State} (folded : Derives s x y) :
    ∀ m, Models s m → GeneralDeclarativeRepeatedActual323.eqAt m x y :=
  fun m valid => GeneralDeclarativeEqualities322.semantic folded m valid

end Yulang.GeneralDeclarativePairCenters326
