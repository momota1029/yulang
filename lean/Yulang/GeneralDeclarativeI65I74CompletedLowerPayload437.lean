import Yulang.GeneralDeclarativeI65B6MixedLexical401

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.CompletedLower437

open CommonNominalFullCarrier (Equivalent)
open GeneralDeclarativeHead320 (Equation)
open GeneralNominalCenteredHeadMatExpressions (Expr)

/-- This low-level object is indexed by the whole receipt; it contains
no selected trace, release token or model. -/
structure Payload {s : State} (lower : Nat) (receipt : NamedMixedReceipt401 s) where
  target : receipt.original.target = lower
  code : Expr
  rowOrdinal : Nat
  row : s.current.ordinary.equations[rowOrdinal]? = some (⟨lower,code⟩ : Equation)

def Payload.Means {s lower receipt} (_ : Payload (s := s) lower receipt) (m : Model) : Prop :=
  ∃ ty, receipt.actualEquation m = some (lower,ty) ∧ Equivalent (m.assignment lower).1 ty

end Yulang.GeneralDeclarativeI65.CompletedLower437
