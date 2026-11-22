import Yulang.GeneralStoppedLower335

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeStoppedStructural339
open Core.PresenceGeneration (TyTerm)
open GeneralNominalCenteredHeadMatExpressions (Expr value values primitiveValue)
open GeneralNominalCommonBridge (Assignment assignment)
open GeneralDeclarativeHead320 (environment)
open CommonNominalFullCarrier (model)

/-- Static extension of the scalar raw encoder. Names are actual raw
source identities. Unsupported semantic forms still cause none. -/
def encode (base : GeneralSourceState.State) : TyTerm (Fin base.slots) → Option Expr
  | .var n => some (.variable (base.source n))
  | .base tag => some (.primitive (.scalar tag) [])
  | .emptyRecord => some (.primitive .emptyRecord [])
  | .exactEmpty => some (.primitive .exactEmpty [])
  | .pair a b => do
      return .primitive .pair [← encode base a, ← encode base b]
  | .record label a b => do
      return .record label (← encode base a) (← encode base b)
  | .variant label a => (encode base a).map (.variant label)
  | .union a b => do
      return .join (← encode base a) (← encode base b)
  | _ => none

theorem meaning (base : GeneralSourceState.State) (m : Assignment)
    (t : TyTerm (Fin base.slots)) {e : Expr} (encoded : encode base t = some e) :
    t.eval model (assignment base m) = value (environment m) .actual e := by
  induction t generalizing e with
  | var n | base n | emptyRecord | exactEmpty =>
    have eq := Option.some.inj encoded
    cases eq
    rfl
  | bottom | top | inter | required | recordDefault | arrow => cases encoded
  | variant tag a ih =>
    obtain ⟨expr,observed,rfl⟩ := Option.map_eq_some_iff.mp encoded
    simp only [TyTerm.eval,value,ih observed]
    rfl
  | pair a b ia ib =>
    cases sa : encode base a with
    | none => simp [encode,sa] at encoded
    | some x =>
      cases sb : encode base b with
      | none => simp [encode,sa,sb] at encoded
      | some y =>
        have eq : Expr.primitive .pair [x,y] = e := by simpa [encode,sa,sb] using encoded
        cases eq
        simp only [TyTerm.eval,value,values,primitiveValue,ia sa,ib sb]
        rfl
  | union a b ia ib =>
    cases sa : encode base a with
    | none => simp [encode,sa] at encoded
    | some x =>
      cases sb : encode base b with
      | none => simp [encode,sa,sb] at encoded
      | some y =>
        have eq : Expr.join x y = e := by simpa [encode,sa,sb] using encoded
        cases eq
        simp only [TyTerm.eval,value,ia sa,ib sb]
        rfl
  | record tag a b ia ib =>
    cases sa : encode base a with
    | none => simp [encode,sa] at encoded
    | some x =>
      cases sb : encode base b with
      | none => simp [encode,sa,sb] at encoded
      | some y =>
        have eq : Expr.record tag x y = e := by simpa [encode,sa,sb] using encoded
        cases eq
        simp only [TyTerm.eval,value,ia sa,ib sb]
        rfl

end Yulang.GeneralDeclarativeStoppedStructural339
