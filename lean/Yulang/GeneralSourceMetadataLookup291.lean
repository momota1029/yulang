import Yulang.GeneralSourceMetadataRows291

/-! All three exported projections refer to the same resolved row, or
to their named default if no row matches. -/
namespace Yulang.GeneralSourceMetadataLookup291
open GeneralSourceMetadataRows291
open GeneralObservedMetadataOverlay290 (overlay)

def locate (key : Nat) : List Row → Option Row
  | [] => none
  | row :: rest => if key = row.key then some row else locate key rest

theorem present {key : Nat} {rows : List Row} {row : Row} (h : locate key rows = some row) :
    row ∈ rows ∧ row.key = key := by
  induction rows with
  | nil => cases h
  | cons first rest ih =>
    by_cases found : key = first.key
    · simp only [locate,ite_eq_left found] at h
      cases Option.some.inj h
      exact ⟨List.mem_cons_self,found.symm⟩
    · simp only [locate,ite_eq_right found] at h
      exact ⟨List.mem_cons_of_mem _ (ih h).1,(ih h).2⟩

theorem projected (fallback : DefaultCode) (rows : List Row) (key : Nat) :
    let src : Source := ⟨fallback,rows⟩
    (constructors src key,primitives src key,invariants src key) =
      match locate key rows with
      | none => (fallback.decode key,none,false)
      | some row => (row.ctor,row.classification.primitiveValue,row.classification.invariantFlag) := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    by_cases found : key = row.key
    · simp [constructors,constructorRows,primitives,primitiveRows,invariants,invariantRows,overlay,locate,found]
    · simpa [constructors,constructorRows,primitives,primitiveRows,invariants,invariantRows,overlay,locate,found] using ih

end Yulang.GeneralSourceMetadataLookup291
