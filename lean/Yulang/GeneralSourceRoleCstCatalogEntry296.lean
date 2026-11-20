import Yulang.GeneralSourceRoleCstCatalogWire296

/-! Compose the existing selected CST boundary with the finite catalog codec.
The pure entry does not manufacture its own selection or recovery receipt. -/
namespace Yulang.GeneralSourceRoleCstCatalogEntry296
open Lean (Json)
open GeneralSourceRoleCstJson293 (read encode depth read_exact)
open GeneralSourceRoleCstCatalogWire296 (decodeCatalog encodeCatalog catalog_exact)
open GeneralSourceRoleCstCatalogExport296 (Failure Exported run)
open GeneralSourceRoleCstSelectedCompile295 (Boundary)
open GeneralSourceRoleCstSnapshot293 (Address)
open GeneralSourceRoleCstMarkPolicy294 (Policy)

inductive Error where
  | sourceText (details : String)
  | evidenceText (details : String)
  | sourceSchemaOrDepth
  | evidenceSchema
  | selected (why : Failure)
  deriving DecidableEq, Repr

def fromValue {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (source names : Json) (policy : Policy) (scope : S) (brand : B)
    (selected : Address B) (sealed : Boundary S B) (fallback : Nat) : Except Error Exported :=
  match read fuel source with
  | none => .error .sourceSchemaOrDepth
  | some w =>
    match decodeCatalog names with
    | none => .error .evidenceSchema
    | some c => (run policy scope w brand selected sealed c fallback).mapError Error.selected

def fromText {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (source names : String) (policy : Policy) (scope : S) (brand : B)
    (selected : Address B) (sealed : Boundary S B) (fallback : Nat) : Except Error Exported :=
  match Json.parse source with
  | .error why => .error (.sourceText why)
  | .ok s =>
    match Json.parse names with
    | .error why => .error (.evidenceText why)
    | .ok n => fromValue fuel s n policy scope brand selected sealed fallback

theorem value_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (source names : Json) (policy : Policy) (scope : S) (brand : B)
    (selected : Address B) (sealed : Boundary S B) (fallback : Nat) (out : Exported) :
    fromValue fuel source names policy scope brand selected sealed fallback = .ok out ↔
      ∃ w c, source = encode w ∧ depth w ≤ fuel ∧ names = encodeCatalog c ∧
        run policy scope w brand selected sealed c fallback = .ok out := by
  constructor
  · intro h
    cases s : read fuel source with
    | none => simp [fromValue,s] at h
    | some w =>
      cases n : decodeCatalog names with
      | none => simp [fromValue,s,n] at h
      | some c =>
        have ⟨wire,fit⟩ := (read_exact ..).mp s
        have rows := (catalog_exact ..).mp n
        refine ⟨w,c,wire.symm,fit,rows,?_⟩
        cases r : run policy scope w brand selected sealed c fallback <;>
          simp [fromValue,s,n,r,Except.mapError] at h ⊢ <;> exact h
  · rintro ⟨w,c,format,fit,rows,result⟩
    have s := (read_exact fuel source w).mpr ⟨format.symm,fit⟩
    have n := (catalog_exact names c).mpr rows
    simp [fromValue,s,n,result,Except.mapError]

theorem text_exact {S B : Type} [DecidableEq S] [DecidableEq B]
    (fuel : Nat) (source names : String) (policy : Policy) (scope : S) (brand : B)
    (selected : Address B) (sealed : Boundary S B) (fallback : Nat) (out : Exported) :
    fromText fuel source names policy scope brand selected sealed fallback = .ok out ↔
      ∃ s n w c, Json.parse source = .ok s ∧ Json.parse names = .ok n ∧
        s = encode w ∧ depth w ≤ fuel ∧ n = encodeCatalog c ∧
        run policy scope w brand selected sealed c fallback = .ok out := by
  cases s : Json.parse source with
  | error why => simp [fromText,s]
  | ok v =>
    cases n : Json.parse names with
    | error why => simp [fromText,s,n]
    | ok x => simp [fromText,s,n,value_exact]

end Yulang.GeneralSourceRoleCstCatalogEntry296
