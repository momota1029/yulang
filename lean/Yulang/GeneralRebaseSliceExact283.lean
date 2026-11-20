import Yulang.GeneralRebaseSlice283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseSliceExact283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (SafeOrder solve solve_rows solve_outside)
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralNominalAcyclicEquations237 (Descending)
open GeneralRebaseSlice283 (build subset grows safe fulfills_query needed_reads closed)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)

theorem needs_exact (defs : List (Entry Nat)) (query : List Nat) (n : Nat) :
    n ∈ (build defs query).needs ↔
    n ∈ query ∨ ∃ row ∈ (build defs query).keep, n ∈ typedReads row.2 := by
  induction defs with
  | nil => simp [build]
  | cons head tail ih =>
    simp only [build]
    by_cases hit : (build tail query).needs.contains head.1 = true
    · rw [ite_eq_left hit]
      constructor
      · intro member
        rcases List.mem_append.mp member with atHead|atTail
        · exact Or.inr ⟨head,List.mem_cons_self ..,atHead⟩
        · rcases ih.mp atTail with asked|⟨row,picked,used⟩
          · exact Or.inl asked
          · exact Or.inr ⟨row,List.mem_cons_of_mem _ picked,used⟩
      · rintro (asked|⟨row,picked,used⟩)
        · exact List.mem_append_right _ (ih.mpr (Or.inl asked))
        · rcases List.mem_cons.mp picked with rfl|picked
          · exact List.mem_append_left _ used
          · exact List.mem_append_right _ (ih.mpr (Or.inr ⟨row,picked,used⟩))
    · rw [ite_eq_right hit]; exact ih

theorem required (defs : List (Entry Nat)) (query : List Nat) (ordered : SafeOrder defs)
    (row : Entry Nat) (available : row ∈ defs) (hit : row.1 ∈ (build defs query).needs) :
    row ∈ (build defs query).keep := by
  rcases (needs_exact defs query row.1).mp hit with asked|⟨consumer,kept,read⟩
  · exact fulfills_query defs query row available asked
  · exact closed defs query ordered consumer row kept available read

inductive Demand (defs : List (Entry Nat)) (query : List Nat) : Nat → Prop
  | root (id : Nat) : id ∈ query → Demand defs query id
  | read (row : Entry Nat) (id : Nat) : row ∈ defs → id ∈ typedReads row.2 →
      Demand defs query row.1 → Demand defs query id

theorem demand_mono {defs smaller : List (Entry Nat)} {query : List Nat} {n : Nat}
    (includes : smaller ⊆ defs) (needed : Demand smaller query n) : Demand defs query n := by
  induction needed with
  | root n q => exact .root n q
  | read row n listed read _ ih => exact .read row n (includes listed) read ih

theorem minimal (defs : List (Entry Nat)) (query : List Nat) (n : Nat)
    (needed : n ∈ (build defs query).needs) : Demand defs query n := by
  induction defs generalizing n with
  | nil => exact .root n needed
  | cons head tail ih =>
    simp only [build] at needed
    by_cases hit : (build tail query).needs.contains head.1 = true
    · rw [ite_eq_left hit] at needed
      rcases List.mem_append.mp needed with read|seen
      · exact .read head n List.mem_cons_self read
          (demand_mono (fun {_} h => List.mem_cons_of_mem _ h) (ih _ (by simpa using hit)))
      · exact demand_mono (fun {_} h => List.mem_cons_of_mem _ h) (ih _ seen)
    · rw [ite_eq_right hit] at needed
      exact demand_mono (fun {_} h => List.mem_cons_of_mem _ h) (ih _ needed)

theorem exact_support (defs : List (Entry Nat)) (query : List Nat) (order : SafeOrder defs)
    {n : Nat} : n ∈ (build defs query).needs ↔ Demand defs query n := by
  constructor
  · exact minimal defs query n
  · intro need
    induction need with
    | root n member => exact grows defs query member
    | read row n stored reads _ ih =>
      exact needed_reads defs query row (required defs query order row stored ih) reads

theorem agrees (defs : List (Entry Nat)) (query : List Nat) (order : SafeOrder defs)
    (rank : Descending defs) (base : Assignment) (n : Nat) (used : n ∈ (build defs query).needs) :
    solve model (build defs query).keep base n = solve model defs base n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases seen : ∃ row ∈ defs, row.1 = n
    · obtain ⟨row,member,rfl⟩ := seen
      have stays := required defs query order row member used
      apply Prod.ext
      · rw [GeneralRebaseExactHistory283.equation _ (safe defs query order) base row stays,
          GeneralRebaseExactHistory283.equation defs order base row member]
        apply GeneralRebaseExactHistory283.eval_equal row.2
        · intro j
          exact (solve_rows model _ _ j).trans (solve_rows model _ _ j).symm
        · intro j read
          have smaller := rank row member j (GeneralNominalOrderedSupport248.typed_reads_subset _ read)
          exact congrArg Prod.fst (ih j smaller (needed_reads defs query row stays read))
      · exact (solve_rows model _ _ _).trans (solve_rows model _ _ _).symm
    · have absent : ∀ row ∈ defs, row.1 ≠ n := fun row present same => seen ⟨row,present,same⟩
      rw [solve_outside model defs base n absent,
        solve_outside model (build defs query).keep base n (fun r member => absent r (subset _ _ member))]

theorem queries (defs : List (Entry Nat)) (query : List Nat) (order : SafeOrder defs)
    (rank : Descending defs) (base : Assignment) (n : Nat) (asked : n ∈ query) :
    solve model (build defs query).keep base n = solve model defs base n :=
  agrees defs query order rank base n (grows defs query asked)

end Yulang.GeneralRebaseSliceExact283
