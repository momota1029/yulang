import Yulang.GeneralRebaseExactHistory283

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseDirtyHistory283
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (SafeOrder)
open GeneralPresenceUsedSupport245 (typedReads)

def needs (old dirty : List Nat) (row : Entry Nat) : Bool :=
  !(old.contains row.1) || (typedReads row.2).any dirty.contains

def select (old : List Nat) : List (Entry Nat) → List Nat → List (Entry Nat)
  | [], _ => []
  | row :: rest, dirty =>
      if needs old dirty row then row :: select old rest (row.1 :: dirty)
      else select old rest dirty

theorem subset (old : List Nat) (full : List (Entry Nat)) (dirty : List Nat) :
    select old full dirty ⊆ full := by
  intro row found
  induction full generalizing dirty with
  | nil => exact found
  | cons head tail ih =>
    by_cases hit : needs old dirty head = true
    · rw [select,ite_eq_left hit] at found
      rcases List.mem_cons.mp found with rfl | found
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih _ found)
    · rw [select,ite_eq_right hit] at found
      exact List.mem_cons_of_mem _ (ih _ found)

theorem safe (old : List Nat) (full : List (Entry Nat)) (dirty : List Nat)
    (order : SafeOrder full) : SafeOrder (select old full dirty) := by
  induction full generalizing dirty with
  | nil => trivial
  | cons head tail ih =>
    obtain ⟨noSelf,distinct,late,rest⟩ := order
    by_cases hit : needs old dirty head = true
    · rw [select,ite_eq_left hit]
      refine ⟨noSelf,?_,?_,ih _ rest⟩
      · exact fun row mem => distinct row (subset _ _ _ mem)
      · exact fun row mem => late row (subset _ _ _ mem)
    · rw [select,ite_eq_right hit]
      exact ih _ rest

theorem no_need (old dirty : List Nat) (row : Entry Nat)
    (skip : ¬ needs old dirty row = true) :
    row.1 ∈ old ∧ ∀ n ∈ typedReads row.2, n ∉ dirty := by
  have sk : needs old dirty row = false := Bool.eq_false_iff.mpr skip
  simpa [needs, Bool.or_eq_false_iff,List.any_eq_false] using sk

theorem skipped (old : List Nat) (full : List (Entry Nat)) (dirty : List Nat)
    (order : SafeOrder full) (row : Entry Nat) (inside : row ∈ full)
    (skip : row ∉ select old full dirty) :
    row.1 ∈ old ∧
      (∀ n ∈ typedReads row.2, n ∉ dirty) ∧
      (∀ write ∈ select old full dirty, write.1 ∉ typedReads row.2) := by
  induction full generalizing dirty with
  | nil => simp at inside
  | cons head tail ih =>
    obtain ⟨_,_,late,rest⟩ := order
    by_cases hit : needs old dirty head = true
    · rw [select,ite_eq_left hit] at skip ⊢
      have notHead : row ≠ head := fun same => skip (same ▸ List.mem_cons_self ..)
      have inTail := (List.mem_cons.mp inside).resolve_left notHead
      obtain ⟨known,read,after⟩ :=
        ih _ rest inTail (fun mem => skip (List.mem_cons_of_mem _ mem))
      refine ⟨known,(fun n used found => read n used (List.mem_cons_of_mem _ found)),?_⟩
      intro write written dep
      rcases List.mem_cons.mp written with rfl | later
      · exact read _ dep (List.mem_cons_self ..)
      · exact after write later dep
    · rw [select,ite_eq_right hit] at skip ⊢
      rcases List.mem_cons.mp inside with rfl | inTail
      · exact ⟨(no_need old dirty row hit).1,(no_need old dirty row hit).2,
          fun write written => late write (subset _ _ _ written)⟩
      · exact ih _ rest inTail skip

theorem chosen_eq_of_target (old : List Nat) (full : List (Entry Nat)) (dirty : List Nat)
    (coherent : ∀ a ∈ full, ∀ b ∈ full, a.1 = b.1 → a.2 = b.2)
    {row write : Entry Nat} (inFull : row ∈ full) (chosen : write ∈ select old full dirty)
    (target : write.1 = row.1) : write = row :=
  Prod.ext target (coherent _ (subset _ _ _ chosen) _ inFull target)
end Yulang.GeneralRebaseDirtyHistory283
