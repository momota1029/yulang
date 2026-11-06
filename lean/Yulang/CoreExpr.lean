import Yulang.CasePatterns
import Yulang.NominalConstructions
import Yulang.MultiOperationPayloadHandlers
import Yulang.RowInference

/-!
# Shared, untyped syntax (M0)

Only `var` refers to a local binder, by de Bruijn index. `free` retains an
unbound resolved name when translating the historical named data syntax.
The carriers below are resolved identities/values, not type annotations.
`app` retains the historical computation-argument application; `strictApp`
retains the independently proved written-order application. Their integration
through elaboration is outside M0.
-/

namespace Yulang.Core

structure Signature where
  Op : Type
  Key : Type
  Scope : Type
  Float : Type
  Atom : Type

def Signature.empty : Signature := ⟨Empty, Empty, Empty, Empty, Empty⟩

inductive Expr (s : Signature) where
  | var : Nat → Expr s
  | free : Nat → Expr s
  /-- A historical base marker does not invent literal contents. -/
  | lit : Inference.Base → Expr s
  | literal : LiteralValues.Literal s.Float → Expr s
  | atom : s.Atom → Expr s
  | data : CaseValues.Value s.Float → Expr s
  | method : Nat → Expr s
  | lam : Expr s → Expr s
  | app : Expr s → Expr s → Expr s
  | strictApp : Expr s → Expr s → Expr s
  /-- Optional binder identity is provenance for named legacy inputs; references
  still use de Bruijn indices. -/
  | letE : Option Nat → Expr s → Expr s → Expr s
  | leaf : Expr s → Expr s
  | branch : Expr s → Expr s → Expr s → Expr s
  | pair : Expr s → Expr s → Expr s
  | fst : Expr s → Expr s
  | snd : Expr s → Expr s
  | emptyRecord : Expr s
  | record : Nat → Expr s → Expr s → Expr s
  | recordDefault : Nat → Expr s → Expr s → Expr s
  | field : Nat → Expr s → Expr s
  | variant : Nat → Expr s → Expr s
  | nominal : Nat → Nat → Expr s → Expr s
  | nil : Expr s
  | cons : Expr s → Expr s → Expr s
  | request : s.Op → Expr s → Expr s
  | boundary : RowInference.Boundary s.Key s.Scope → Expr s → Expr s
  /-- Return body binds one value; operation body binds payload then resumption. -/
  | handler : s.Op → Expr s → Expr s → Expr s → Expr s
  | multiHandler {count : Nat} : MultiOperationHandlers.Operations s.Key count →
      Expr s → Expr s → (Fin count → Expr s) → Expr s
  | partialHandler {count : Nat} :
      (Fin count → MultiOperationPayloadHandlers.Arm s.Key s.Atom) →
      Expr s → Expr s → (Fin count → Expr s) → Expr s
  /-- List order is arm order; default expressions live in patterns. -/
  | caseE : Expr s →
      List (CasePatterns.Pattern s.Float (Expr s) × Option (Expr s) × Expr s) → Expr s
  | cast : Nat → Casts.Ty → Casts.Ty → Expr s → Expr s
  /-- Each site retains its parameter assignment and original ground type. -/
  | construction : NominalConstructions.Constructor → Nat → Nat →
      List (Nat × LiteralCasts.Element × Expr s) → Expr s

/-- Historical nonexpansiveness test used by the required/effect restrictions.
This does not specify value restriction for the other Core constructors. -/
def Expr.isValue : Expr s → Bool
  | .var _ | .lit _ | .method _ | .lam _ | .emptyRecord => true
  | .pair a b | .record _ a b | .recordDefault _ a b => a.isValue && b.isValue
  | .variant _ a => a.isValue
  | _ => false

/-- A model supplies its own independent constructor judgement on shared
syntax. In particular required-field and presence models are not identified. -/
structure TypingModel (s : Signature) where
  Context : Type
  Result : Type
  judgment : Context → Expr s → Result → Prop

abbrev Typing (model : TypingModel s) := model.judgment

/-- SCCs stay outside expressions, as in `RecursiveInference`: bodies refer to
the jointly supplied recursive environment through ordinary local indices.
Declaration signatures and slot closure remain the caller's interface. -/
structure SCC (s : Signature) (Declaration : Type) where
  members : List (Declaration × Expr s)

end Yulang.Core
