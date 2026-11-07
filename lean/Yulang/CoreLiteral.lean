import Yulang.CoreExpr

/-! LiteralValues supplies values and matching, not an expression judgement.
The kind model preserves contents and the existing match relation unchanged;
it does not turn kind classification into a whole-language principal type. -/
namespace Yulang.Core.Literal
open LiteralValues
abbrev Term (F : Type) := Core.Expr ⟨Empty, Empty, Empty, F, Empty⟩

def embed (value : LiteralValues.Literal F) : Term F := .literal value

inductive Typing : Term F → Kind → Prop where
  | literal : Typing (embed value) value.kind

def model (F : Type) : TypingModel ⟨Empty, Empty, Empty, F, Empty⟩ :=
  ⟨Unit, Kind, fun _ => Typing⟩

theorem conservative (value : LiteralValues.Literal F) (kind : Kind) :
    value.kind = kind ↔ Core.Typing (model F) () (embed value) kind := by
  constructor
  · intro eq; cases eq; exact .literal
  · intro h; cases h; rfl

inductive Matches (floatRel : F → F → Prop) : Term F → Term F → Prop where
  | literal : LiteralValues.Matches floatRel expected actual →
      Matches floatRel (embed expected) (embed actual)

theorem matches_conservative (floatRel : F → F → Prop)
    (expected actual : LiteralValues.Literal F) :
    LiteralValues.Matches floatRel expected actual ↔
      Matches floatRel (embed expected) (embed actual) := by
  constructor
  · exact .literal
  · intro h; cases h with | literal h => exact h

end Yulang.Core.Literal
