import Yulang.CommonCanonicalRowSyntax

/-!
# Finite row equations expressed by finite public type syntax

An intersection test is compiled to a union of ordinary arrows. No row-meet
constructor or residual parameter constraint is added to the interface.
-/

namespace Yulang.CommonCanonicalRowTests

open CommonCanonicalRowSyntax
open CommonCanonicalRowConstraints

def rowForm (row : Row scopes parameters) : Form scopes parameters :=
  .arrow .unit row .unit .empty

def lockForm (form : Form scopes parameters) : Form scopes parameters :=
  .arrow form .empty form .empty

def meetForm (first : Row scopes parameters) : List (Row scopes parameters) → Form scopes parameters
  | [] => rowForm first
  | next :: rest => .union (rowForm next) (meetForm first rest)

def meetEval (parameters : Fin count → Common.Row) (first : Row scopes count) :
    List (Row scopes count) → Common.Row
  | [] => rowEval parameters first
  | next :: rest => meetRow (rowEval parameters next) (meetEval parameters first rest)

/-- Every nonempty finite row intersection is represented by ordinary
type syntax, with every repeated row parameter shared exactly. -/
theorem meetForm_exact (first : Row scopes count) (rest : List (Row scopes count))
    (parameters : Fin count → Common.Row) :
    Common.Equivalent ((meetForm first rest).eval parameters)
      (rowType (meetEval parameters first rest)) := by
  induction rest with
  | nil => exact Common.equivalent_refl _
  | cons next rest ih =>
      exact Common.equivalent_trans
        (CommonCanonicalShapes.union_congr (Common.equivalent_refl _) ih)
        (arrow_union_input_rows (.base .unit) (.base .unit)
          (rowEval parameters next) (meetEval parameters first rest) Common.rowEmpty)

end Yulang.CommonCanonicalRowTests
