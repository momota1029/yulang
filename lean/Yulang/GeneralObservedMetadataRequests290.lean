import Yulang.GeneralObservedMetadataActual290

/-! The normalized materialization request patterns have their own
metadata reads. Their finite coverage controls actual generated schemas. -/
namespace Yulang.GeneralObservedMetadataRequests290
open GeneralDeclarationPatterns (Constructors normalize)
open GeneralNominalInspection (Interpretation translate)
open GeneralNominalMaterialization (Request Schema schema)
open GeneralObservedMetadataKeys290 (keys)
open GeneralObservedMetadataEntry290 (LocalEqual)

def requestKeys (requests : List Request) : List Nat :=
  requests.flatMap fun request => keys (normalize request.pattern)

theorem request_key {rs : List Request} {r : Request} {key : Nat}
    (request : r ∈ rs) (seen : key ∈ keys (normalize r.pattern)) : key ∈ requestKeys rs :=
  List.mem_flatMap.mpr ⟨r,request,seen⟩

def schemaFrom (c : Constructors) (i : Interpretation) (rs : List Request) : Schema :=
  (rs.map fun r => schema (translate c i (normalize r.pattern)) (.source r.target) r.mode).foldr Schema.append {}

theorem schema_actual (s : GeneralNominalState.State) (i : Interpretation) (rs : List Request) :
    schemaFrom s.constructors i rs = GeneralNominalMaterialization.generated s i rs := rfl

theorem schema_eq (c : Constructors) (i : Interpretation) (d : Constructors) (j : Interpretation)
    (rs : List Request) (h : LocalEqual (requestKeys rs) c i d j) :
    schemaFrom c i rs = schemaFrom d j rs := by
  unfold schemaFrom
  congr 1
  apply List.map_congr_left
  intro request member
  rw [GeneralObservedMetadataTranslation290.translate_eq c i d j (normalize request.pattern)
    (h.restrict (fun _ seen => request_key member seen))]

end Yulang.GeneralObservedMetadataRequests290
