import Yulang.GeneralRebaseFrontierPairs283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseFutureWatch284
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceUsedSupport245 (typedReads)
open GeneralPresenceOrderedBlock247 (SafeOrder solve solve_rows solve_outside)
open GeneralNominalAcyclicEquations237 (Descending)
open GeneralNominalCommonBridge (Assignment)
open CommonNominalFullCarrier (model)

def trim (watch : List Nat) (defs : List (Entry Nat)) :=
  defs.filter (fun row => watch.contains row.1)

theorem member_exact (watch : List Nat) (defs : List (Entry Nat)) (row : Entry Nat) :
    row ∈ trim watch defs ↔ row ∈ defs ∧ row.1 ∈ watch := by
  simp [trim]

def Closed (watch : List Nat) (defs : List (Entry Nat)) : Prop :=
  ∀ row ∈ defs, row.1 ∈ watch → typedReads row.2 ⊆ watch

structure Covers (watch : List Nat) (full kept : List (Entry Nat)) : Prop where
  closed : Closed watch full
  sound : kept ⊆ full
  enough : ∀ row ∈ full, row.1 ∈ watch → row ∈ kept

theorem trimmed (closed : Closed watch full) : Covers watch full (trim watch full) :=
  ⟨closed,fun {_} found => (member_exact _ _ _).mp found |>.1,
    fun row member yes => (member_exact _ _ row).mpr ⟨member,yes⟩⟩

theorem safe_trim (watch : List Nat) (defs : List (Entry Nat)) (safe : SafeOrder defs) :
    SafeOrder (trim watch defs) := by
  induction defs with
  | nil => trivial
  | cons row tail ih =>
    obtain ⟨self,distinct,later,rest⟩ := safe
    unfold trim at *
    by_cases needed : watch.contains row.1 = true
    · simp only [List.filter_cons,needed,ite_true]
      refine ⟨self,fun e h => distinct e (List.mem_filter.mp h).1,
        fun e h => later e (List.mem_filter.mp h).1,ih rest⟩
    · simp only [List.filter_cons,ite_eq_right needed]
      exact ih rest

theorem preserves (cover : Covers watch full kept) (ranked : Descending full)
    (sFull : SafeOrder full) (sKept : SafeOrder kept) {a b : Assignment}
    (rows : ∀ n, (a n).2 = (b n).2)
    (bases : ∀ n ∈ watch, a n = b n) (n : Nat) (requested : n ∈ watch) :
    solve model kept a n = solve model full b n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases found : ∃ row ∈ full, row.1 = n
    · obtain ⟨row,member,rfl⟩ := found
      have retained := cover.enough row member requested
      apply Prod.ext
      · rw [GeneralRebaseExactHistory283.equation kept sKept a row retained,
          GeneralRebaseExactHistory283.equation full sFull b row member]
        apply GeneralRebaseExactHistory283.eval_equal row.2
        · intro k
          exact (solve_rows model _ _ k).trans ((rows k).trans (solve_rows model _ _ k).symm)
        · intro k uses
          have less := ranked row member k (GeneralNominalOrderedSupport248.typed_reads_subset _ uses)
          exact congrArg Prod.fst (ih k less (cover.closed row member requested uses))
      · exact (solve_rows model _ _ _).trans ((rows _).trans (solve_rows model _ _ _).symm)
    · have clear : ∀ row ∈ full, row.1 ≠ n := fun row member hit => found ⟨row,member,hit⟩
      rw [solve_outside model kept a n (fun row member => clear row (cover.sound member)),
        solve_outside model full b n clear]
      exact bases n requested

theorem trim_exact (closed : Closed watch full) (ranked : Descending full) (sFull : SafeOrder full)
    (a : Assignment) (n : Nat) (requested : n ∈ watch) :
    solve model (trim watch full) a n = solve model full a n :=
  preserves (trimmed closed) ranked sFull (safe_trim _ _ sFull) (fun _ => rfl) (fun _ _ => rfl) n requested

end Yulang.GeneralRebaseFutureWatch284
