import Yulang.GeneralRebaseCachedDriver283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSlice283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (SafeOrder)
open GeneralPresenceUsedSupport245 (typedReads)

structure Slice where
  keep : List (Entry Nat)
  needs : List Nat

def build : List (Entry Nat) → List Nat → Slice
  | [], query => ⟨[],query⟩
  | row :: rest, query =>
    let later := build rest query
    if later.needs.contains row.1 then
      ⟨row :: later.keep,typedReads row.2 ++ later.needs⟩
    else later

theorem subset (defs : List (Entry Nat)) (query : List Nat) :
    (build defs query).keep ⊆ defs := by
  intro row member
  induction defs with
  | nil => exact member
  | cons head tail ih =>
    simp only [build] at member
    split at member
    · rcases List.mem_cons.mp member with rfl|found
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih found)
    · exact List.mem_cons_of_mem _ (ih member)

theorem grows (defs : List (Entry Nat)) (query : List Nat) :
    query ⊆ (build defs query).needs := by
  intro n member
  induction defs with
  | nil => exact member
  | cons row tail ih =>
    simp only [build]
    split
    · exact List.mem_append_right _ ih
    · exact ih

theorem safe (defs : List (Entry Nat)) (query : List Nat) (order : SafeOrder defs) :
    SafeOrder (build defs query).keep := by
  induction defs with
  | nil => trivial
  | cons head tail ih =>
    obtain ⟨self,distinct,reads,remaining⟩ := order
    simp only [build]
    split
    · exact ⟨self,fun row m => distinct row (subset _ _ m),
        fun row m => reads row (subset _ _ m),ih remaining⟩
    · exact ih remaining

theorem fulfills_query (defs : List (Entry Nat)) (query : List Nat)
    (row : Entry Nat) (member : row ∈ defs) (asked : row.1 ∈ query) :
    row ∈ (build defs query).keep := by
  induction defs with
  | nil => simp at member
  | cons head tail ih =>
    simp only [build]
    rcases List.mem_cons.mp member with rfl|member
    · have yes := grows tail query asked
      rw [ite_eq_left (by simpa using yes)]
      exact List.mem_cons_self ..
    · have tail := ih member
      split
      · exact List.mem_cons_of_mem _ tail
      · exact tail

theorem needed_reads (defs : List (Entry Nat)) (query : List Nat) (row : Entry Nat)
    (chosen : row ∈ (build defs query).keep) : typedReads row.2 ⊆ (build defs query).needs := by
  intro n member
  induction defs with
  | nil => cases chosen
  | cons head tail ih =>
    simp only [build] at chosen ⊢
    by_cases hit : (build tail query).needs.contains head.1 = true
    · rw [ite_eq_left hit] at chosen ⊢
      rcases List.mem_cons.mp chosen with rfl|chosen
      · exact List.mem_append_left _ member
      · exact List.mem_append_right _ (ih chosen)
    · rw [ite_eq_right hit] at chosen ⊢; exact ih chosen

theorem closed (defs : List (Entry Nat)) (query : List Nat) (order : SafeOrder defs)
    (consumer provider : Entry Nat) (isKept : consumer ∈ (build defs query).keep)
    (available : provider ∈ defs) (read : provider.1 ∈ typedReads consumer.2) :
    provider ∈ (build defs query).keep := by
  induction defs with
  | nil => cases available
  | cons head tail ih =>
    obtain ⟨_,_,late,safeTail⟩ := order
    simp only [build] at isKept ⊢
    by_cases hit : (build tail query).needs.contains head.1 = true
    · rw [ite_eq_left hit] at isKept ⊢
      rcases List.mem_cons.mp available with rfl|later
      · exact List.mem_cons_self ..
      · rcases List.mem_cons.mp isKept with rfl|kept
        · exact False.elim (late provider later read)
        · exact List.mem_cons_of_mem _ (ih safeTail kept later)
    · rw [ite_eq_right hit] at isKept ⊢
      rcases List.mem_cons.mp available with rfl|later
      · exact False.elim (hit (by simpa using needed_reads tail query consumer isKept read))
      · exact ih safeTail isKept later

end Yulang.GeneralRebaseSlice283
