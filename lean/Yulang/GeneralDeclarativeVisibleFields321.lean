import Yulang.GeneralDeclarativeInspect321

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeVisibleFields321
open GeneralDeclarativeGraphRows321 (fields shapeOf observed)
open GeneralDeclarativeInspect321 (fieldPatterns Visit)
open GeneralDeclarativeK2Graph321 (Shape)
open GeneralDeclarativeHead320 (State)
open GeneralNominalCenteredHeadMatExpressions (Expr)

theorem normalized_fields_skip_shadowed (label kept hidden : Nat) :
    shapeOf (.record label (.variable kept)
      (.record label (.variable hidden) (.primitive .emptyRecord []))) =
      some (.record [(label,kept)]) := by
  simp [shapeOf,fields]

theorem normalized_queries_skip_shadowed (label : Nat) (kept hidden : Expr) :
    fieldPatterns (.record label kept (.record label hidden (.primitive .emptyRecord []))) =
      [(label,kept)] := by simp [fieldPatterns]

/-- No K2 observation may descend into a syntactically hidden record field.
An otherwise cyclic apparent payload is not an edge of the admitted view. -/
theorem no_hidden_payload (label kept hidden : Nat) (different : kept ≠ hidden) :
    ∀ head, shapeOf (.record label (.variable kept)
      (.record label (.variable hidden) (.primitive .emptyRecord []))) = some head →
      hidden ∉ head.children := by
  intro head seen
  rw [normalized_fields_skip_shadowed] at seen
  cases seen
  simpa [Shape.children] using different.symm

end Yulang.GeneralDeclarativeVisibleFields321
