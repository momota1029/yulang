import Yulang.Inference

/-!
# Syntax work for actual scheme instantiation

The counted interpreter visits formula, type and row constructors. A lookup
of an existing substitution value is charged at its supplied cost; lifting a
substitution under a binder traverses and renames both components of that
value. Thus binder renaming is not silently treated as constant time.

The abstract units exclude the bit complexity of identifiers and allocation
or hash-table implementation details. Instantiating a stored scheme traverses
its syntax, not the source body from which the scheme was obtained.
-/

namespace Yulang.InferenceSubstitutionCost

open Inference

def rowNodes : RowTerm α → Nat
  | .var _ | .empty => 1
  | .join first last => 1 + rowNodes first + rowNodes last

def tyNodes : TyTerm α → Nat
  | .var _ | .base _ | .bottom | .top | .emptyRecord => 1
  | .union first last | .inter first last | .pair first last | .record _ first last =>
      1 + tyNodes first + tyNodes last
  | .variant _ payload => 1 + tyNodes payload
  | .arrow input inputRow output outputRow =>
      1 + tyNodes input + rowNodes inputRow + tyNodes output + rowNodes outputRow

def compNodes (term : CompTerm α) : Nat := tyNodes term.ty + rowNodes term.row

theorem rowNodes_rename (term : RowTerm α) (rename : α → β) :
    rowNodes (term.rename rename) = rowNodes term := by
  induction term <;> simp_all [RowTerm.rename, rowNodes]

theorem tyNodes_rename (term : TyTerm α) (rename : α → β) :
    tyNodes (term.rename rename) = tyNodes term := by
  induction term <;> simp_all [TyTerm.rename, tyNodes, rowNodes_rename]

theorem compNodes_rename (term : CompTerm α) (rename : α → β) :
    compNodes (term.rename rename) = compNodes term := by
  simp [compNodes, CompTerm.rename, tyNodes_rename, rowNodes_rename]

def rowSubst (replacement : α → CompTerm β × Nat) : RowTerm α → RowTerm β × Nat
  | .var index => let value := replacement index; (value.1.row, 1 + value.2)
  | .empty => (.empty, 1)
  | .join first last =>
      let a := rowSubst replacement first
      let b := rowSubst replacement last
      (.join a.1 b.1, 1 + a.2 + b.2)

def tySubst (replacement : α → CompTerm β × Nat) : TyTerm α → TyTerm β × Nat
  | .var index => let value := replacement index; (value.1.ty, 1 + value.2)
  | .base base => (.base base, 1)
  | .bottom => (.bottom, 1)
  | .top => (.top, 1)
  | .emptyRecord => (.emptyRecord, 1)
  | .union first last =>
      let a := tySubst replacement first
      let b := tySubst replacement last
      (.union a.1 b.1, 1 + a.2 + b.2)
  | .inter first last =>
      let a := tySubst replacement first
      let b := tySubst replacement last
      (.inter a.1 b.1, 1 + a.2 + b.2)
  | .pair first last =>
      let a := tySubst replacement first
      let b := tySubst replacement last
      (.pair a.1 b.1, 1 + a.2 + b.2)
  | .record label first last =>
      let a := tySubst replacement first
      let b := tySubst replacement last
      (.record label a.1 b.1, 1 + a.2 + b.2)
  | .variant label payload =>
      let value := tySubst replacement payload
      (.variant label value.1, 1 + value.2)
  | .arrow input inputRow output outputRow =>
      let a := tySubst replacement input
      let ar := rowSubst replacement inputRow
      let b := tySubst replacement output
      let br := rowSubst replacement outputRow
      (.arrow a.1 ar.1 b.1 br.1, 1 + a.2 + ar.2 + b.2 + br.2)

theorem rowSubst_value (replacement : α → CompTerm β × Nat) (term : RowTerm α) :
    (rowSubst replacement term).1 = term.subst (fun index => (replacement index).1) := by
  induction term <;> simp_all [rowSubst, RowTerm.subst]

theorem tySubst_value (replacement : α → CompTerm β × Nat) (term : TyTerm α) :
    (tySubst replacement term).1 = term.subst (fun index => (replacement index).1) := by
  induction term <;> simp_all [tySubst, TyTerm.subst, rowSubst_value]

theorem rowSubst_bound (replacement : α → CompTerm β × Nat) (cost : Nat)
    (bounded : ∀ index, (replacement index).2 ≤ cost) (term : RowTerm α) :
    (rowSubst replacement term).2 ≤ rowNodes term * (cost + 1) := by
  induction term with
  | var index => simpa [rowSubst, rowNodes, Nat.add_comm] using Nat.add_le_add_left (bounded index) 1
  | empty => simp [rowSubst, rowNodes]
  | join first last ihf ihl =>
      simp only [rowSubst, rowNodes, Nat.add_mul, Nat.one_mul]
      omega

theorem tySubst_bound (replacement : α → CompTerm β × Nat) (cost : Nat)
    (bounded : ∀ index, (replacement index).2 ≤ cost) (term : TyTerm α) :
    (tySubst replacement term).2 ≤ tyNodes term * (cost + 1) := by
  induction term with
  | var index => simpa [tySubst, tyNodes, Nat.add_comm] using Nat.add_le_add_left (bounded index) 1
  | base | bottom | top | emptyRecord => simp [tySubst, tyNodes]
  | union | inter | pair | record | variant =>
      simp only [tySubst, tyNodes, Nat.add_mul, Nat.one_mul]
      omega
  | arrow input inputRow output outputRow ihi iho =>
      have first := rowSubst_bound replacement cost bounded inputRow
      have last := rowSubst_bound replacement cost bounded outputRow
      simp only [tySubst, tyNodes, Nat.add_mul, Nat.one_mul]
      omega

/-- A binder preserves the substitution's size bound but increases the cost
of each captured lookup by the full size of the renamed computation term. -/
def lift (replacement : α → CompTerm β × Nat) : Option α → CompTerm (Option β) × Nat
  | none => (CompTerm.var none, 0)
  | some index =>
      let value := replacement index
      (value.1.rename some, value.2 + compNodes value.1)

theorem lift_value (replacement : α → CompTerm β × Nat) :
    (fun index => (lift replacement index).1) = liftSubst (fun index => (replacement index).1) := by
  funext index
  cases index <;> rfl

theorem lift_bounds (replacement : α → CompTerm β × Nat) (size cost : Nat) (fresh : 2 ≤ size)
    (sizes : ∀ index, compNodes (replacement index).1 ≤ size)
    (costs : ∀ index, (replacement index).2 ≤ cost) :
    (∀ index, compNodes (lift replacement index).1 ≤ size) ∧
      (∀ index, (lift replacement index).2 ≤ cost + size) := by
  constructor
  · intro index
    cases index with
    | none => exact fresh
    | some index => simpa only [lift, compNodes_rename] using sizes index
  · intro index
    cases index with
    | none => simp [lift]
    | some index => exact Nat.add_le_add (costs index) (sizes index)

def formulaNodes : Formula α → Nat
  | .top | .bot => 1
  | .and first last | .or first last => 1 + formulaNodes first + formulaNodes last
  | .tyLe first last => 1 + tyNodes first + tyNodes last
  | .rowLe first last => 1 + rowNodes first + rowNodes last
  | .existsSlot body => 1 + formulaNodes body

def binderDepth : Formula α → Nat
  | .top | .bot | .tyLe _ _ | .rowLe _ _ => 0
  | .and first last | .or first last => max (binderDepth first) (binderDepth last)
  | .existsSlot body => 1 + binderDepth body

def formulaSubst (replacement : α → CompTerm β × Nat) : Formula α → Formula β × Nat
  | .top => (.top, 1)
  | .bot => (.bot, 1)
  | .and first last =>
      let a := formulaSubst replacement first
      let b := formulaSubst replacement last
      (.and a.1 b.1, 1 + a.2 + b.2)
  | .or first last =>
      let a := formulaSubst replacement first
      let b := formulaSubst replacement last
      (.or a.1 b.1, 1 + a.2 + b.2)
  | .tyLe first last =>
      let a := tySubst replacement first
      let b := tySubst replacement last
      (.tyLe a.1 b.1, 1 + a.2 + b.2)
  | .rowLe first last =>
      let a := rowSubst replacement first
      let b := rowSubst replacement last
      (.rowLe a.1 b.1, 1 + a.2 + b.2)
  | .existsSlot body =>
      let nested := formulaSubst (lift replacement) body
      (.existsSlot nested.1, 1 + nested.2)

theorem formulaSubst_value (replacement : α → CompTerm β × Nat) (formula : Formula α) :
    (formulaSubst replacement formula).1 = formula.subst (fun index => (replacement index).1) := by
  induction formula generalizing β with
  | top | bot => rfl
  | and | or => simp_all [formulaSubst, Formula.subst]
  | tyLe => simp [formulaSubst, Formula.subst, tySubst_value]
  | rowLe => simp [formulaSubst, Formula.subst, rowSubst_value]
  | existsSlot body ih => simp [formulaSubst, Formula.subst, ih, lift_value]

private theorem combined_bound (a b na nb budget : Nat) (ha : a ≤ na * budget)
    (hb : b ≤ nb * budget) (positive : 1 ≤ budget) :
    1 + a + b ≤ (1 + na + nb) * budget := by
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem formulaSubst_bound (replacement : α → CompTerm β × Nat) (size cost : Nat) (fresh : 2 ≤ size)
    (sizes : ∀ index, compNodes (replacement index).1 ≤ size)
    (costs : ∀ index, (replacement index).2 ≤ cost) (formula : Formula α) :
    (formulaSubst replacement formula).2 ≤
      formulaNodes formula * (cost + size * binderDepth formula + 1) := by
  induction formula generalizing β cost with
  | top | bot => simp [formulaSubst, formulaNodes, binderDepth]
  | and first last ihf ihl | or first last ihf ihl =>
      have firstBound := ihf replacement cost sizes costs
      have lastBound := ihl replacement cost sizes costs
      have firstBudget : cost + size * binderDepth first + 1 ≤
          cost + size * max (binderDepth first) (binderDepth last) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left size (Nat.le_max_left _ _)) cost) 1
      have lastBudget : cost + size * binderDepth last + 1 ≤
          cost + size * max (binderDepth first) (binderDepth last) + 1 :=
        Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left size (Nat.le_max_right _ _)) cost) 1
      exact combined_bound _ _ _ _ _
        (Nat.le_trans firstBound (Nat.mul_le_mul_left _ firstBudget))
        (Nat.le_trans lastBound (Nat.mul_le_mul_left _ lastBudget)) (by omega)
  | tyLe first last =>
      simpa only [formulaSubst, formulaNodes, binderDepth, Nat.mul_zero, Nat.add_zero] using
        combined_bound _ _ _ _ (cost + 1) (tySubst_bound replacement cost costs first)
          (tySubst_bound replacement cost costs last) (by omega)
  | rowLe first last =>
      simpa only [formulaSubst, formulaNodes, binderDepth, Nat.mul_zero, Nat.add_zero] using
        combined_bound _ _ _ _ (cost + 1) (rowSubst_bound replacement cost costs first)
          (rowSubst_bound replacement cost costs last) (by omega)
  | existsSlot body ih =>
      obtain ⟨liftSizes, liftCosts⟩ := lift_bounds replacement size cost fresh sizes costs
      have nested := ih (lift replacement) (cost + size) liftSizes liftCosts
      simp only [formulaSubst, formulaNodes, binderDepth, Nat.add_mul, Nat.one_mul]
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using
        Nat.add_le_add (show 1 ≤ cost + size + size * binderDepth body + 1 by omega) nested

def instantiate (scheme : Scheme α) (target : CompTerm α) : Formula α × Nat :=
  formulaSubst (fun | none => (target, 0) | some index => (CompTerm.var index, 0)) scheme

theorem instantiate_value (scheme : Scheme α) (target : CompTerm α) :
    (instantiate scheme target).1 = scheme.instantiate target := by
  simp only [instantiate, formulaSubst_value, Scheme.instantiate]
  congr 1
  funext index
  cases index <;> rfl

theorem instantiate_bound (scheme : Scheme α) (target : CompTerm α) :
    (instantiate scheme target).2 ≤
      formulaNodes scheme * (max 2 (compNodes target) * binderDepth scheme + 1) := by
  have result := formulaSubst_bound
    (fun | none => (target, 0) | some index => (CompTerm.var index, 0))
    (max 2 (compNodes target)) 0 (Nat.le_max_left _ _)
    (by
      intro index
      cases index with
      | none => exact Nat.le_max_right _ _
      | some index => exact Nat.le_max_left _ _)
    (by intro index; cases index <;> exact Nat.le_refl _) scheme
  simpa only [instantiate, Nat.zero_add] using result

theorem binderDepth_le_nodes (formula : Formula α) : binderDepth formula ≤ formulaNodes formula := by
  induction formula <;> simp_all [binderDepth, formulaNodes] <;> omega

theorem instantiate_size_bound (scheme : Scheme α) (target : CompTerm α) :
    (instantiate scheme target).2 ≤
      formulaNodes scheme * (max 2 (compNodes target) * formulaNodes scheme + 1) := by
  exact Nat.le_trans (instantiate_bound scheme target)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right
      (Nat.mul_le_mul_left _ (binderDepth_le_nodes scheme)) 1))

end Yulang.InferenceSubstitutionCost
