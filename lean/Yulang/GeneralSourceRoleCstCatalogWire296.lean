import Yulang.GeneralSourceRoleCstCatalogQueryWire296

/-! Versioned array transport for verification. Every input row is kept in
order, including duplicates. This is not a Rust production wire schema. -/
namespace Yulang.GeneralSourceRoleCstCatalogWire296
open Lean (Json)
open GeneralSourceRoleCstNameCatalog296 (Catalog)
open GeneralSourceRoleCstNamingRequests295 (Query)
open GeneralSourceRoleCstCatalogScalar296 (encodeValue decodeValue value_exact)
open GeneralSourceRoleCstCatalogQueryWire296 (encodeQuery decodeQuery query_exact)
open GeneralSourceRoleExport292 (Aligned collect collect_exact)

abbrev Row := Query × Option Nat

def encodeRow (p : Row) : Json := .arr #[encodeQuery p.1,encodeValue p.2]

def decodeRowFields : List Json → Option Row
  | [q,v] => (decodeQuery q).bind fun key => (decodeValue v).map (key,·)
  | _ => none

theorem row_fields_exact (xs : List Json) (p : Row) :
    decodeRowFields xs = some p ↔ xs = [encodeQuery p.1,encodeValue p.2] := by
  cases xs with
  | nil => simp [decodeRowFields]
  | cons q rest =>
    cases rest with
    | nil => simp [decodeRowFields]
    | cons v tail =>
      cases tail with
      | cons w more => simp [decodeRowFields]
      | nil =>
        rcases p with ⟨key,value⟩
        rw [show decodeRowFields [q,v] = (decodeQuery q).bind
              (fun x => (decodeValue v).map (x,·)) by rfl]
        cases qd : decodeQuery q <;> cases vd : decodeValue v <;>
          simp [qd,vd,←query_exact,←value_exact]

def decodeRow : Json → Option Row
  | .arr a => decodeRowFields a.toList
  | _ => none

theorem row_exact (j : Json) (p : Row) : decodeRow j = some p ↔ j = encodeRow p := by
  cases j <;> try simp [decodeRow,encodeRow]
  simp [row_fields_exact,←Array.toList_inj]

theorem aligned_rows_exact (js : List Json) (c : Catalog) :
    Aligned (fun j p => j = encodeRow p) js c ↔ js = c.map encodeRow := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons first tail ih => simp [first,ih]
  · rintro rfl
    induction c with
    | nil => exact .nil
    | cons entry rest ih => exact .cons rfl ih

theorem rows_exact (js : List Json) (c : Catalog) :
    collect decodeRow js = some c ↔ js = c.map encodeRow :=
  (collect_exact _ _ row_exact _ _).trans (aligned_rows_exact ..)

def schema : String := "yulang-name-evidence-v1"

def encodeCatalog (c : Catalog) : Json :=
  .arr #[.str schema,.arr (c.map encodeRow).toArray]

def decodeCatalogFields : List Json → Option Catalog
  | [.str tag,.arr rows] => if tag = schema then collect decodeRow rows.toList else none
  | _ => none

theorem catalog_fields_exact (js : List Json) (c : Catalog) :
    decodeCatalogFields js = some c ↔ js = [.str schema,.arr (c.map encodeRow).toArray] := by
  constructor
  · intro yes
    unfold decodeCatalogFields at yes
    split at yes
    · rename_i _ tag rows
      by_cases h : tag = schema
      · subst tag
        have found : collect decodeRow rows.toList = some c := by simpa using yes
        have e := Array.toList_inj.mp (show rows.toList = (c.map encodeRow).toArray.toList by
          simpa using (rows_exact ..).mp found)
        rw [e]
      · simp [h] at yes
    · cases yes
  · rintro rfl
    simp [decodeCatalogFields,rows_exact]

def decodeCatalog : Json → Option Catalog
  | .arr a => decodeCatalogFields a.toList
  | _ => none

theorem catalog_exact (j : Json) (c : Catalog) :
    decodeCatalog j = some c ↔ j = encodeCatalog c := by
  cases j <;> try simp [decodeCatalog,encodeCatalog]
  simp [catalog_fields_exact,←Array.toList_inj]

end Yulang.GeneralSourceRoleCstCatalogWire296
