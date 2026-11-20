import Yulang.GeneralSourceRoleCstSelectedOutcome295

/-! Verify the finite selected handoff starting at the existing portable JSON
schema. No Yulang grammar parse is provided by this entry point. -/
namespace Yulang.GeneralSourceRoleCstSelectedJson295
open Lean (Json)
open GeneralSourceRoleCstJson293 (read encode depth read_exact)
open GeneralSourceRoleCstWire293 (Wire)
open GeneralSourceRoleCstSelectedOutcome295 (Error run ok_iff_checked)
open GeneralSourceRoleCstNamingPacket295 (FiniteBoundary checked)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)
open GeneralSourceRoleSpelling292 (Environment)
open GeneralSourceMetadataRoles291 (RoleSource)

def fromValue {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (j : Json) (policy : Policy) (scope : S) (brand : B) (a : Address B)
    (sealed : FiniteBoundary S B) (env : S → Environment) (arity : Nat) : Except Error RoleSource :=
  match read fuel j with
  | none => .error .schemaOrDepth
  | some w => run policy scope w brand a sealed env arity

def fromText {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (str : String) (policy : Policy) (scope : S) (brand : B) (a : Address B)
    (sealed : FiniteBoundary S B) (env : S → Environment) (arity : Nat) : Except Error RoleSource :=
  match Json.parse str with
  | .error reason => .error (.badJson reason)
  | .ok j => fromValue fuel j policy scope brand a sealed env arity

theorem value_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (j : Json) (policy : Policy) (scope : S) (brand : B) (a : Address B)
    (sealed : FiniteBoundary S B) (env : S → Environment) (arity : Nat) (table : RoleSource) :
    fromValue fuel j policy scope brand a sealed env arity = .ok table ↔
      ∃ w, encode w = j ∧ depth w ≤ fuel ∧
        checked policy scope w brand a sealed env arity = some table := by
  constructor
  · intro ok
    cases h : read fuel j with
    | none => simp [fromValue,h] at ok
    | some w =>
      have e := (read_exact ..).mp h
      exact ⟨w,e.1,e.2,(ok_iff_checked ..).mp (by simpa [fromValue,h] using ok)⟩
  · rintro ⟨w,encoding,d,go⟩
    simp [fromValue,(read_exact ..).mpr ⟨encoding,d⟩,(ok_iff_checked ..).mpr go]

theorem text_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (str : String) (policy : Policy) (scope : S) (brand : B) (a : Address B)
    (sealed : FiniteBoundary S B) (env : S → Environment) (arity : Nat) (table : RoleSource) :
    fromText fuel str policy scope brand a sealed env arity = .ok table ↔
      ∃ j w, Json.parse str = .ok j ∧ encode w = j ∧ depth w ≤ fuel ∧
        checked policy scope w brand a sealed env arity = some table := by
  constructor
  · intro h
    cases json : Json.parse str with
    | error msg => simp [fromText,json] at h
    | ok j =>
      obtain ⟨w,e,d,out⟩ := (value_exact fuel j policy scope brand a sealed env arity table).mp
        (by simpa [fromText,json] using h)
      exact ⟨j,w,rfl,e,d,out⟩
  · rintro ⟨j,w,parse,e,d,out⟩
    have h := (value_exact fuel j policy scope brand a sealed env arity table).mpr ⟨w,e,d,out⟩
    simp [fromText,parse,h]

end Yulang.GeneralSourceRoleCstSelectedJson295
