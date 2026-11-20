import Yulang.GeneralSourceRoleCstCatalogScalar296

namespace Yulang.GeneralSourceRoleCstCatalogQueryWire296
open Lean (Json)
open GeneralSourceRoleCstNamingRequests295 (Query)
open GeneralSourceRoleCstCatalogScalar296 (encodeNat decodeNat nat_exact)

def encodeFields : Query → List Json
  | .role n => [.str "role",.str n]
  | .output r n => [.str "output",encodeNat r,.str n]
  | .constructor n => [.str "constructor",.str n]

def decodeFields : List Json → Option Query
  | [.str "role",.str n] => some (.role n)
  | [.str "output",i,.str n] => (decodeNat i).map (fun r => .output r n)
  | [.str "constructor",.str n] => some (.constructor n)
  | _ => none

theorem fields_exact (xs : List Json) (q : Query) :
    decodeFields xs = some q ↔ xs = encodeFields q := by
  constructor
  · intro yes
    unfold decodeFields at yes
    split at yes
    · cases yes; rfl
    · rename_i _ i n
      cases h : decodeNat i with
      | none => simp [h] at yes
      | some k =>
        have proper : Query.output k n = q := by simpa [h] using yes
        subst q
        have eq := (nat_exact ..).mp h
        simp [encodeFields,eq]
    · cases yes; rfl
    · cases yes
  · rintro rfl
    cases q with
    | role n => rfl
    | constructor n => rfl
    | output r n => simp [encodeFields,decodeFields,(nat_exact ..).mpr rfl]

def encodeQuery (q : Query) : Json := .arr (encodeFields q).toArray

def decodeQuery : Json → Option Query
  | .arr a => decodeFields a.toList
  | _ => none

theorem query_exact (j : Json) (q : Query) :
    decodeQuery j = some q ↔ j = encodeQuery q := by
  cases j <;> try simp [decodeQuery,encodeQuery]
  rename_i a
  simp [fields_exact,←Array.toList_inj]

end Yulang.GeneralSourceRoleCstCatalogQueryWire296
