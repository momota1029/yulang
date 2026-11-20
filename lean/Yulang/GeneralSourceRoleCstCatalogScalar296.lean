import Yulang.GeneralSourceRoleCstTrimCatalog296

/-! Exact scalar forms of the test evidence codec. A missing row is not null. -/
namespace Yulang.GeneralSourceRoleCstCatalogScalar296
open Lean (Json JsonNumber)

def encodeNat (n : Nat) : Json := .num (JsonNumber.fromNat n)

def decodeNat : Json → Option Nat
  | .num a => if a.exponent = 0 then
    match a.mantissa with
    | .ofNat n => some n
    | .negSucc _ => none
    else none
  | _ => none

theorem nat_exact (j : Json) (n : Nat) : decodeNat j = some n ↔ j = encodeNat n := by
  cases j
  case num a =>
    rcases a with ⟨m,places⟩
    cases m with
    | ofNat k =>
      cases places with
      | zero =>
        change some k = some n ↔ Json.num ⟨.ofNat k,0⟩ = Json.num ⟨.ofNat n,0⟩
        simp only [Option.some.injEq,Json.num.injEq,JsonNumber.mk.injEq,and_true]
        exact ⟨congrArg Int.ofNat,Int.ofNat.inj⟩
      | succ d => simp [decodeNat,encodeNat,JsonNumber.fromNat]
    | negSucc k => cases places <;> simp [decodeNat,encodeNat,JsonNumber.fromNat]
  all_goals simp [decodeNat,encodeNat]

def encodeValue : Option Nat → Json
  | none => .null
  | some n => encodeNat n

def decodeValue : Json → Option (Option Nat)
  | .null => some none
  | j => (decodeNat j).map some

theorem value_exact (j : Json) (v : Option Nat) :
    decodeValue j = some v ↔ j = encodeValue v := by
  cases j
  case num a =>
    cases v with
    | none =>
      cases h : decodeNat (.num a) <;> simp [decodeValue,h,encodeValue]
    | some n =>
      change (decodeNat (.num a)).map some = some (some n) ↔ Json.num a = encodeNat n
      rw [← nat_exact (.num a) n]
      cases decodeNat (.num a) <;> simp
  all_goals cases v <;> simp [decodeValue,decodeNat,encodeValue,encodeNat]

end Yulang.GeneralSourceRoleCstCatalogScalar296
