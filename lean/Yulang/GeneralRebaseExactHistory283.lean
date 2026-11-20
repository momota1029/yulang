import Yulang.GeneralRebaseProspective282

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralRebaseExactHistory283
open Core.PresenceGeneration PresenceNormalForm
open GeneralPresenceDefinitionRewrite244 (Entry)
open GeneralPresenceOrderedBlock247 (put solve SafeOrder solve_outside solve_rows)
open GeneralPresenceUsedSupport245 (typedReads)
open CommonNominalFullCarrier (model)
open GeneralNominalCommonBridge (Assignment)
open GeneralNominalAcyclicEquations237 (Descending)

theorem eval_equal {a b : Assignment} (term : TyTerm Nat)
    (rows : ∀ n, (a n).2 = (b n).2)
    (reads : ∀ n ∈ typedReads term, (a n).1 = (b n).1) :
    term.eval model a = term.eval model b :=
  GeneralPresenceConsumerSupport246.type_eval_equal model a b rows term reads

theorem equation (defs : List (Entry Nat)) (safe : SafeOrder defs) (base : Assignment)
    (row : Entry Nat) (member : row ∈ defs) :
    (solve model defs base row.1).1 = row.2.eval model (solve model defs base) := by
  induction defs generalizing base with
  | nil => simp at member
  | cons head tail ih =>
    obtain ⟨self,distinct,late,safety⟩ := safe
    rcases List.mem_cons.mp member with rfl | member
    · have written : (solve model (row :: tail) base row.1).1 = row.2.eval model base := by
        change (solve model tail (put model base row.1 (row.2.eval model base)) row.1).1 = _
        rw [solve_outside model tail _ row.1 distinct]
        simp [put]
      rw [written]
      apply eval_equal row.2 (fun n => (solve_rows model (row::tail) base n).symm)
      intro n read
      symm
      apply congrArg Prod.fst (solve_outside model (row::tail) base n ?_)
      intro item inside hit
      rcases List.mem_cons.mp inside with rfl | inside
      · exact self (hit ▸ read)
      · exact late item inside (hit ▸ read)
    · exact ih safety (put model base head.1 (head.2.eval model base)) member

theorem unique (defs : List (Entry Nat)) (ranked : Descending defs) {a b : Assignment}
    (rows : ∀ n, (a n).2 = (b n).2)
    (outside : ∀ n, (∀ row ∈ defs, row.1 ≠ n) → a n = b n)
    (aeq : ∀ row ∈ defs, (a row.1).1 = row.2.eval model a)
    (beq : ∀ row ∈ defs, (b row.1).1 = row.2.eval model b) : a = b := by
  funext n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases found : ∃ row ∈ defs, row.1 = n
    · obtain ⟨row,member,hit⟩ := found
      apply Prod.ext _ (rows n)
      rw [← hit,aeq row member,beq row member]
      apply eval_equal row.2 rows
      intro j reads
      have lower := ranked row member j (GeneralNominalOrderedSupport248.typed_reads_subset _ reads)
      exact congrArg Prod.fst (ih j (hit ▸ lower))
    · exact outside n (fun row member hit => found ⟨row,member,hit⟩)

theorem order_independent {first last : List (Entry Nat)}
    (members : ∀ row, row ∈ first ↔ row ∈ last)
    (ranked : Descending first) (sf : SafeOrder first) (sl : SafeOrder last) (base : Assignment) :
    solve model first base = solve model last base := by
  apply unique first ranked
  · intro n
    exact (solve_rows model first base n).trans (solve_rows model last base n).symm
  · intro n absent
    exact (solve_outside model first base n absent).trans
      (solve_outside model last base n (fun row used => absent row ((members row).mpr used))).symm
  · exact fun row => equation first sf base row
  · exact fun row member => equation last sl base row ((members row).mp member)
end Yulang.GeneralRebaseExactHistory283
