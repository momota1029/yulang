import Yulang.GeneralDeclarativeI65I74StructuralWhereChildRead427

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.StructuralWhere427
open CommonRoleOutermostResolver (Dictionary)

structure WhereAt427 {s q} (f : AuthoredBodyFrame393 s q) (atlas : B6OccurrenceAtlas401 s)
    (k : Nat) where
  original : OriginalRecordArgument427 f k 0
  positive : ReadClosedChild427 original atlas

inductive OrderedWhere427 {s q} (f : AuthoredBodyFrame393 s q) (atlas : B6OccurrenceAtlas401 s) :
    List Nat → Type where
  | nil : OrderedWhere427 f atlas []
  | cons : WhereAt427 f atlas k → OrderedWhere427 f atlas ks → OrderedWhere427 f atlas (k::ks)

def OrderedWhere427.requests {s q f atlas kk}
    (xs : OrderedWhere427 (s:=s) (q:=q) f atlas kk) : List Request :=
  match xs with
  | .nil => []
  | .cons a as => a.original.child :: as.requests

def OrderedWhere427.dictionaries {s q f atlas kk}
    (xs : OrderedWhere427 (s:=s) (q:=q) f atlas kk) : List Dictionary :=
  match xs with
  | .nil => []
  | .cons a as => .node a.positive.source.decl.id [] :: as.dictionaries

theorem ordered_requests_take_exact_source_positions427 {s q f atlas kk}
    (xs : OrderedWhere427 (s:=s) (q:=q) f atlas kk) (i : Nat) :
    xs.requests[i]? = (kk[i]?).bind (fun k => (frameWhereKids400 f)[k]?) := by
  induction xs generalizing i with
  | nil => simp [OrderedWhere427.requests]
  | cons a rest ih =>
    cases i with
    | zero =>
      simpa [OrderedWhere427.requests] using
        (structural_where_keeps_original_child_at_ordinal427 a.original).symm
    | succ i => exact ih i

theorem entire_where_order_reconstructs_original_request_list427 {s q f atlas}
    (xs : OrderedWhere427 (s:=s) (q:=q) f atlas (List.range f.decl.requirements.length)) :
    xs.requests = frameWhereKids400 f := by
  apply List.ext_getElem?
  intro i
  rw [ordered_requests_take_exact_source_positions427]
  by_cases pos : i < f.decl.requirements.length
  · rw [List.getElem?_range pos]; rfl
  · have absent : (List.range f.decl.requirements.length)[i]? = none :=
      List.getElem?_eq_none (by simpa using Nat.le_of_not_lt pos)
    have noneAt : (frameWhereKids400 f)[i]? = none := List.getElem?_eq_none (by
      simpa [frameWhereKids400,children,AuthoredBodyFrame393.clauses] using Nat.le_of_not_lt pos)
    simp [absent,noneAt]

theorem ordered_where_packet_has_same_model_dictionary_forest427 {s q f atlas kk}
    (xs : OrderedWhere427 (s:=s) (q:=q) f atlas kk) (m : Model) (fit : Fits s m) :
    I72.DictionaryEvidenceForest ⟨s,atlas⟩ m xs.requests xs.dictionaries := by
  induction xs with
  | nil => exact .nil
  | cons first _ later =>
    exact .cons (original_compound_child_has_positive_same_model_dictionary427
      first.positive.source m fit) later

/-- Data for the next original clause. The wire contains no child
ordinal: the checker advances it, even when roles or types agree. -/
structure OrderedWhereWire427 where
  rowOrdinal : Nat
  leaf : LeafWire427

def readWhereAt427 {s q} (f : AuthoredBodyFrame393 s q) (atlas : B6OccurrenceAtlas401 s)
    (k : Nat) (w : OrderedWhereWire427) : Option (WhereAt427 f atlas k) := do
  let original ← readOriginalRecordArgument427 f ⟨k,0,w.rowOrdinal⟩
  let positive ← readClosedChild427 original atlas w.leaf
  pure ⟨original,positive⟩

def readWhereSuffix427 {s q} (f : AuthoredBodyFrame393 s q) (atlas : B6OccurrenceAtlas401 s)
    (start : Nat) (data : List OrderedWhereWire427) :
    Option (OrderedWhere427 f atlas (List.range' start data.length)) :=
  match data with
  | [] => some .nil
  | next :: later => do
    let a ← readWhereAt427 f atlas start next
    let b ← readWhereSuffix427 f atlas (start+1) later
    pure (by simpa [List.range'_succ] using OrderedWhere427.cons a b)

def readAllOriginalWhere427 {s q} (f : AuthoredBodyFrame393 s q) (atlas : B6OccurrenceAtlas401 s)
    (data : List OrderedWhereWire427) :
    Option (OrderedWhere427 f atlas (List.range f.decl.requirements.length)) :=
  if count : data.length = f.decl.requirements.length then
    by simpa only [List.range_eq_range',count] using readWhereSuffix427 f atlas 0 data
  else none

theorem checked_original_where_list_has_exact_same_model_forest427 {s q f atlas data xs}
    (_ : readAllOriginalWhere427 (s:=s) (q:=q) f atlas data = some xs)
    (m : Model) (fit : Fits s m) :
    I72.DictionaryEvidenceForest ⟨s,atlas⟩ m (frameWhereKids400 f) xs.dictionaries :=
  (entire_where_order_reconstructs_original_request_list427 xs) ▸
    ordered_where_packet_has_same_model_dictionary_forest427 xs m fit

end Yulang.GeneralDeclarativeI65.StructuralWhere427
