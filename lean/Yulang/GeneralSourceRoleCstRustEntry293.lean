import Lean.Data.Json.Parser
import Yulang.GeneralSourceRoleCstJson293
import Yulang.GeneralSourceRoleCstRustSnapshot293

/-! Executable entry from a tagged JSON snapshot. This parser parses wire
JSON, never Yulang text. The source scope and snapshot brand are external. -/
namespace Yulang.GeneralSourceRoleCstRustEntry293
open Lean (Json)
open GeneralSourceRoleCstJson293 (read depth encode read_exact)
open GeneralSourceRoleCstWire293 (Transfer decode decode_exact)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstRustSnapshot293 (exportAt)
open GeneralSourceRoleTrack292 (Tracked)

inductive Error where
  | json (message : String)
  | schemaOrDepth
  | unknownTag
  | foreignOrUnsupportedRole
  deriving DecidableEq, Repr

def extractValue {Scope Brand : Type} [DecidableEq Brand] (fuel : Nat) (j : Json)
    (scope : Scope) (brand : Brand) (address : Address Brand) :
    Except Error (Tracked Scope (Address Brand)) :=
  match read fuel j with
  | none => .error .schemaOrDepth
  | some w => match decode w with
    | none => .error .unknownTag
    | some tree => match exportAt scope ⟨brand,tree⟩ address with
      | none => .error .foreignOrUnsupportedRole
      | some out => .ok out

def extractText {Scope Brand : Type} [DecidableEq Brand] (fuel : Nat) (text : String)
    (scope : Scope) (brand : Brand) (address : Address Brand) :
    Except Error (Tracked Scope (Address Brand)) :=
  match Json.parse text with
  | .error reason => .error (.json reason)
  | .ok json => extractValue fuel json scope brand address

theorem value_exact {Scope Brand : Type} [DecidableEq Brand] (fuel : Nat) (j : Json)
    (scope : Scope) (brand : Brand) (address : Address Brand) (out : Tracked Scope (Address Brand)) :
    extractValue fuel j scope brand address = .ok out ↔
      ∃ wire tree, encode wire = j ∧ depth wire ≤ fuel ∧ Transfer wire tree ∧
        exportAt scope ⟨brand,tree⟩ address = some out := by
  constructor
  · intro done
    cases wire : read fuel j with
    | none => simp [extractValue,wire] at done
    | some w =>
      cases mapped : decode w with
      | none => simp [extractValue,wire,mapped] at done
      | some tree =>
        cases result : exportAt scope ⟨brand,tree⟩ address with
        | none => simp [extractValue,wire,mapped,result] at done
        | some t =>
          have same : t = out := by simpa [extractValue,wire,mapped,result] using done
          subst t
          have good := (read_exact ..).mp wire
          exact ⟨w,tree,good.1,good.2,(decode_exact ..).mp mapped,result⟩
  · rintro ⟨w,t,encoded,limited,tags,find⟩
    simp [extractValue,(read_exact ..).mpr ⟨encoded,limited⟩,(decode_exact ..).mpr tags,find]

theorem text_exact {Scope Brand : Type} [DecidableEq Brand] (fuel : Nat) (text : String)
    (scope : Scope) (brand : Brand) (address : Address Brand) (out : Tracked Scope (Address Brand)) :
    extractText fuel text scope brand address = .ok out ↔
      ∃ j, Json.parse text = .ok j ∧ extractValue fuel j scope brand address = .ok out := by
  constructor
  · intro done
    cases parsed : Json.parse text with
    | error e => simp [extractText,parsed] at done
    | ok j => exact ⟨j,rfl,by simpa [extractText,parsed] using done⟩
  · rintro ⟨j,e,success⟩
    simp [extractText,e,success]

end Yulang.GeneralSourceRoleCstRustEntry293
