import Yulang.GeneralDeclarativeFreshTail326

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeOrderedRecord326
open CommonRoleCanonicalRows (Row lookup normalize selected normalize_unique mem_selected)

def order (row : Row α) : List Nat → Option (Row α)
  | [] => some []
  | l::ls => do
    let e ← lookup l row
    let rest ← order row ls
    pure ((l,e)::rest)

theorem lookup_member {row : Row α} (read : lookup key row = some payload) :
    (key,payload) ∈ row := by
  induction row with
  | nil => cases read
  | cons first rest ih =>
    obtain ⟨label,value⟩ := first
    by_cases same : key = label
    · subst label
      have matched : value = payload := by simpa [lookup] using read
      subst value
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by simpa [lookup,same] using read))

theorem lookup_unique {row : Row α} (unique : (row.map Prod.fst).Nodup)
    (member : (key,payload) ∈ row) : lookup key row = some payload := by
  induction row with
  | nil => cases member
  | cons first rest ih =>
    obtain ⟨label,value⟩ := first
    rcases List.mem_cons.mp member with h|later
    · cases h
      simp [lookup]
    · have distinct := List.nodup_cons.mp unique
      have otherwise : key ≠ label := by
        intro same
        apply distinct.1
        exact List.mem_map.mpr ⟨(key,payload),later,same⟩
      simpa [lookup,otherwise] using ih distinct.2 later

theorem exact_order {row : Row α} {keys : List Nat} {printed : Row α}
    (unique : (row.map Prod.fst).Nodup) (actual : order row keys = some printed) :
    printed.map Prod.fst = keys ∧
       ∀ e, e ∈ printed ↔ e ∈ row ∧ e.1 ∈ keys := by
  induction keys generalizing printed with
  | nil =>
    have same : ([] : Row α) = printed := Option.some.inj actual
    subst printed
    simp
  | cons wanted more ih =>
    cases first : lookup wanted row with
    | none => simp [order,first] at actual
    | some chosen =>
      cases next : order row more with
      | none => simp [order,first,next] at actual
      | some rest =>
        have same : (wanted,chosen) :: rest = printed := by simpa [order,first,next] using actual
        subst printed
        obtain ⟨labels,correct⟩ := ih next
        refine ⟨by simp [labels],?_⟩
        intro e
        constructor
        · intro member
          rcases List.mem_cons.mp member with rfl|later
          · exact ⟨lookup_member first,List.mem_cons_self⟩
          · obtain ⟨inRow,asked⟩ := (correct e).mp later
            exact ⟨inRow,List.mem_cons_of_mem _ asked⟩
        · rintro ⟨inRow,lives⟩
          rcases List.mem_cons.mp lives with top|later
          · obtain ⟨l,p⟩ := e
            change l = wanted at top
            subst l
            obtain rfl := Option.some.inj (first.symm.trans (lookup_unique unique inRow))
            exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ ((correct e).mpr ⟨inRow,later⟩)

theorem to_permutation {raw : Row α} {keys : List Nat} {printed : Row α}
    (distinct : keys.Nodup) (shown : order (normalize raw) keys = some printed) :
    (selected keys (normalize raw)).Perm printed := by
  classical
  letI : DecidableEq (Nat × α) := Classical.typeDecidableEq _
  letI : BEq (Nat × α) := instBEqOfDecidableEq
  have ⟨same,out⟩ := exact_order (normalize_unique raw) shown
  have left : (selected keys (normalize raw)).Nodup := by
    have sub : (selected keys (normalize raw)).Sublist (normalize raw) := List.filter_sublist
    exact ((normalize_unique raw).sublist (sub.map Prod.fst)).of_map _ (fun _ _ ne equal => ne (congrArg Prod.fst equal))
  have right : printed.Nodup := (show (printed.map Prod.fst).Nodup from same.symm ▸ distinct).of_map _ (fun _ _ ne equal => ne (congrArg Prod.fst equal))
  apply List.perm_iff_count.mpr
  intro item
  have visits : item ∈ selected keys (normalize raw) ↔ item ∈ printed :=
    (mem_selected _ _ _).trans (out item).symm
  by_cases seen : item ∈ printed
  · exact (left.count_of_mem (visits.mpr seen)).trans (right.count_of_mem seen).symm
  · exact (List.count_eq_zero_of_not_mem (fun hit => seen (visits.mp hit))).trans
      (List.count_eq_zero_of_not_mem seen).symm

end Yulang.GeneralDeclarativeOrderedRecord326
