import Yulang.GeneralSourceRoleCstMarkReport294

/-! Report directly from portable JSON wire. Parsing here is JSON parsing,
not a new Rust source parse. -/
namespace Yulang.GeneralSourceRoleCstReportWire294
open Lean (Json)
open GeneralSourceRoleCstJson293 (read encode depth read_exact)
open GeneralSourceRoleCstWire293 (decode Transfer decode_exact)
open GeneralSourceRoleCstMarkReport294 (Report run)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstRustEntry293 (Error)

def value {Scope Brand : Type} [DecidableEq Brand] (fuel : Nat) (j : Json)
    (scope : Scope) (brand : Brand) (selected : Address Brand) : Except Error (Report Scope Brand) :=
  match read fuel j with
  | none => .error .schemaOrDepth
  | some wire => match decode wire with
    | none => .error .unknownTag
    | some root => .ok (run scope ⟨brand,root⟩ selected)

def input {Scope Brand : Type} [DecidableEq Brand] (fuel : Nat) (text : String)
    (scope : Scope) (brand : Brand) (selected : Address Brand) : Except Error (Report Scope Brand) :=
  match Json.parse text with
  | .error why => .error (.json why)
  | .ok j => value fuel j scope brand selected

theorem value_exact {Scope Brand : Type} [DecidableEq Brand] (fuel : Nat) (j : Json)
    (scope : Scope) (brand : Brand) (selected : Address Brand) (r : Report Scope Brand) :
    value fuel j scope brand selected = .ok r ↔
      ∃ wire root, encode wire = j ∧ depth wire ≤ fuel ∧ Transfer wire root ∧
        run scope ⟨brand,root⟩ selected = r := by
  constructor
  · intro h
    cases shape : read fuel j with
    | none => simp [value,shape] at h
    | some wire =>
      cases tree : decode wire with
      | none => simp [value,shape,tree] at h
      | some root =>
        have e := (read_exact ..).mp shape
        exact ⟨wire,root,e.1,e.2,(decode_exact ..).mp tree,by simpa [value,shape,tree] using h⟩
  · rintro ⟨wire,root,e,d,t,rfl⟩
    simp [value,(read_exact ..).mpr ⟨e,d⟩,(decode_exact ..).mpr t]

theorem input_exact {Scope Brand : Type} [DecidableEq Brand] (fuel : Nat) (text : String)
    (scope : Scope) (brand : Brand) (selected : Address Brand) (r : Report Scope Brand) :
    input fuel text scope brand selected = .ok r ↔
      ∃ j, Json.parse text = .ok j ∧ value fuel j scope brand selected = .ok r := by
  constructor
  · intro h
    cases parse : Json.parse text with
    | error e => simp [input,parse] at h
    | ok res => exact ⟨res,rfl,by simpa [input,parse] using h⟩
  · rintro ⟨j,parse,done⟩
    simp [input,parse,done]

end Yulang.GeneralSourceRoleCstReportWire294
