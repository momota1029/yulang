import Yulang.GeneralObservedMetadataHistoryFixture290

/-! A serializable finite record of the actual metadata entries in one
scope. Exact byte-level data equality need not compare opaque functions.
The chosen list can have repetitions and uses its original order. -/
namespace Yulang.GeneralObservedMetadataBook290
open GeneralDeclarationPatterns (Constructors)
open GeneralNominalInspection (Interpretation)
open GeneralObservedMetadataEntry290 (Entry entry LocalEqual entry_exact)

abbrev Book := List (Nat × Entry)

def book (keys : List Nat) (c : Constructors) (i : Interpretation) : Book :=
  keys.map fun k => (k,entry c i k)

theorem records_key {keys : List Nat} (c : Constructors) (i : Interpretation) {k : Nat}
    (member : k ∈ keys) : (k,entry c i k) ∈ book keys c i :=
  List.mem_map.mpr ⟨k,member,rfl⟩

theorem keys_exact (keys : List Nat) (c : Constructors) (i : Interpretation) :
    (book keys c i).map Prod.fst = keys := by
  unfold book
  rw [List.map_map]
  exact List.map_id _

theorem book_exact (keys : List Nat) (c d : Constructors) (i j : Interpretation) :
    book keys c i = book keys d j ↔ LocalEqual keys c i d j := by
  constructor
  · intro same k belongs
    have entryFound := records_key c i belongs
    rw [same] at entryFound
    obtain ⟨other,_,value⟩ := List.mem_map.mp entryFound
    have which := congrArg Prod.fst value
    change other = k at which
    subst other
    exact (entry_exact _ _ _ _ _).mp (congrArg Prod.snd value).symm
  · intro h
    unfold book
    exact List.map_congr_left (fun k key => congrArg (Prod.mk k) ((entry_exact ..).mpr (h k key)))

theorem included_transfers {whole slice : List Nat} {c d : Constructors} {i j : Interpretation}
    (same : book whole c i = book whole d j) (included : ∀ k ∈ slice, k ∈ whole) :
    book slice c i = book slice d j :=
  (book_exact ..).mpr (((book_exact ..).mp same).restrict included)

end Yulang.GeneralObservedMetadataBook290
