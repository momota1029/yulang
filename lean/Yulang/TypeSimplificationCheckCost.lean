import Yulang.TypeSimplificationSize

/-!
# Counted evaluation of the existing symbolic simplification certificate

The interpreter is deliberately eager: it checks both sides of each Boolean
combination. It computes the same Boolean as `TypeSimplification.symbolicCheck`
but gives a conservative reference cost even when the original short-circuits.
Type equality, row equality and record-spine checks are traversed explicitly;
they are not hidden unit-cost queries. A constructor dispatch together with
its bounded local atom/Boolean tests counts as one abstract unit. The explicit
`conj` and `disj` combinators charge a separate unit. This is not an exact count
of every primitive Boolean instruction. Identifier bit cost and allocation
costs are outside this model.

The public evaluator chooses its depth from the two finite input syntax trees.
Its exactness and bounds require no supplied fuel or successful certificate.
-/

namespace Yulang.TypeSimplificationCheckCost

open Inference TypeSimplification
open InferenceSubstitutionCost (tyNodes rowNodes)

def atom (value : Bool) : Bool × Nat := (value, 1)

def conj (left right : Bool × Nat) : Bool × Nat :=
  (left.1 && right.1, 1 + left.2 + right.2)

def disj (left right : Bool × Nat) : Bool × Nat :=
  (left.1 || right.1, 1 + left.2 + right.2)

def rowEqCount : RowTerm (Fin n) → RowTerm (Fin n) → Bool × Nat
  | .var first, .var last => (decide (first = last), 1)
  | .empty, .empty => (true, 1)
  | .join a b, .join c d =>
      let first := rowEqCount a c
      let last := rowEqCount b d
      (first.1 && last.1, 1 + first.2 + last.2)
  | _, _ => (false, 1)

theorem rowEqCount_value (first last : RowTerm (Fin n)) :
    (rowEqCount first last).1 = decide (first = last) := by
  induction first generalizing last <;> cases last <;> simp_all [rowEqCount]

theorem rowEqCount_bound (first last : RowTerm (Fin n)) :
    (rowEqCount first last).2 ≤ rowNodes first := by
  induction first generalizing last with
  | var | empty => cases last <;> exact Nat.le_refl _
  | join a b iha ihb =>
      cases last <;> simp only [rowEqCount, rowNodes]
      all_goals first | omega | exact Nat.add_le_add (Nat.add_le_add_left (iha _) 1) (ihb _)

def tyEqCount : TyTerm (Fin n) → TyTerm (Fin n) → Bool × Nat
  | .var first, .var last => (decide (first = last), 1)
  | .base first, .base last => (decide (first = last), 1)
  | .bottom, .bottom | .top, .top | .emptyRecord, .emptyRecord => (true, 1)
  | .union a b, .union c d | .inter a b, .inter c d | .pair a b, .pair c d =>
      let first := tyEqCount a c
      let last := tyEqCount b d
      (first.1 && last.1, 1 + first.2 + last.2)
  | .record label a b, .record other c d =>
      let first := tyEqCount a c
      let last := tyEqCount b d
      (decide (label = other) && first.1 && last.1, 1 + first.2 + last.2)
  | .variant label a, .variant other b =>
      let payload := tyEqCount a b
      (decide (label = other) && payload.1, 1 + payload.2)
  | .arrow a ar b br, .arrow c cr d dr =>
      let input := tyEqCount a c
      let inputRow := rowEqCount ar cr
      let output := tyEqCount b d
      let outputRow := rowEqCount br dr
      (input.1 && inputRow.1 && output.1 && outputRow.1,
        1 + input.2 + inputRow.2 + output.2 + outputRow.2)
  | _, _ => (false, 1)

theorem tyEqCount_value (first last : TyTerm (Fin n)) :
    (tyEqCount first last).1 = decide (first = last) := by
  induction first generalizing last <;> cases last <;>
    simp_all [tyEqCount, rowEqCount_value, Bool.and_assoc]

theorem tyEqCount_bound (first last : TyTerm (Fin n)) :
    (tyEqCount first last).2 ≤ tyNodes first := by
  induction first generalizing last with
  | var | base | bottom | top | emptyRecord => cases last <;> exact Nat.le_refl _
  | union a b iha ihb | inter a b iha ihb | pair a b iha ihb | record label a b iha ihb =>
      cases last <;> simp only [tyEqCount, tyNodes]
      all_goals first | omega | exact Nat.add_le_add (Nat.add_le_add_left (iha _) 1) (ihb _)
  | variant label payload ih =>
      cases last <;> simp only [tyEqCount, tyNodes]
      all_goals first | omega | exact Nat.add_le_add_left (ih _) 1
  | arrow input inputRow output outputRow ihi iho =>
      cases last <;> simp only [tyEqCount, tyNodes]
      all_goals try omega
      rename_i otherInput otherInputRow otherOutput otherOutputRow
      have a := ihi otherInput
      have ar := rowEqCount_bound inputRow otherInputRow
      have b := iho otherOutput
      have br := rowEqCount_bound outputRow otherOutputRow
      omega

def spineCount : TyTerm (Fin n) → Bool × Nat
  | .emptyRecord => (true, 1)
  | .record _ _ rest =>
      let tail := spineCount rest
      (tail.1, 1 + tail.2)
  | _ => (false, 1)

theorem spineCount_value (term : TyTerm (Fin n)) :
    (spineCount term).1 = ValueBoundElimination.recordSpine term := by
  induction term <;> simp_all [spineCount, ValueBoundElimination.recordSpine]

theorem spineCount_bound (term : TyTerm (Fin n)) :
    (spineCount term).2 ≤ tyNodes term := by
  induction term <;> simp_all only [spineCount, tyNodes] <;> omega

/-- One unfolding of the actual checker, with recursive calls supplied by
the caller. Every recursive Boolean operation is also charged explicitly. -/
def step (next : TyTerm (Fin n) → TyTerm (Fin n) → Bool × Nat)
    (source target : TyTerm (Fin n)) : Bool × Nat :=
  disj (disj (disj (disj (disj (disj (disj (disj (disj (disj
    (tyEqCount source target)
    (atom (match source with | .bottom => true | _ => false)))
    (atom (match target with | .top => true | _ => false)))
    (match source with
      | .union a b => conj (next a target) (next b target)
      | _ => atom false))
    (match target with
      | .inter a b => conj (next source a) (next source b)
      | _ => atom false))
    (match target with
      | .union a b => disj (next source a) (next source b)
      | _ => atom false))
    (match source with
      | .inter a b => disj (next a target) (next b target)
      | _ => atom false))
    (match source, target with
      | .pair a b, .pair c d => conj (next a c) (next b d)
      | _, _ => atom false))
    (match source, target with
      | .variant label a, .variant other b => conj (atom (decide (label = other))) (next a b)
      | _, _ => atom false))
    (match source, target with
      | .arrow a ar b br, .arrow c cr d dr =>
          conj (conj (conj (rowEqCount ar cr) (rowEqCount br dr)) (next c a)) (next b d)
      | _, _ => atom false))
    (match source, target with
      | .record label a rest, .record other b tail =>
          conj (conj (conj (conj (atom (decide (label = other)))
            (spineCount rest)) (spineCount tail)) (next a b)) (next rest tail)
      | _, _ => atom false)

def fuelCount : Nat → TyTerm (Fin n) → TyTerm (Fin n) → Bool × Nat
  | 0, _, _ => (false, 0)
  | fuel + 1, source, target => step (fuelCount fuel) source target

theorem fuelCount_value (fuel : Nat) (source target : TyTerm (Fin n))
    (enough : nodes source + nodes target ≤ fuel) :
    (fuelCount fuel source target).1 = symbolicCheck source target := by
  induction fuel generalizing source target with
  | zero => cases source <;> simp [nodes] at enough
  | succ fuel ih =>
      rw [fuelCount, symbolicCheck.eq_def]
      cases source <;> cases target <;>
        simp only [nodes] at enough <;>
        simp (disch := simp only [nodes] <;> omega) only
          [step, disj, conj, atom, tyEqCount_value, rowEqCount_value, spineCount_value, ih]
      all_goals simp (disch := omega) only [ih]

theorem step_bound (next : TyTerm (Fin n) → TyTerm (Fin n) → Bool × Nat)
    (source target : TyTerm (Fin n)) (size budget : Nat)
    (fits : tyNodes source + tyNodes target ≤ size) (large : size + 1 ≤ budget)
    (recursive : ∀ first last, tyNodes first + tyNodes last ≤ size →
      (next first last).2 ≤ budget) :
    (step next source target).2 ≤ 128 * budget := by
  have sameBound : (tyEqCount source target).2 ≤ 10 * budget := by
    have smaller := tyEqCount_bound source target
    omega
  have fromUnion : (match source with
      | .union a b => conj (next a target) (next b target)
      | _ => atom false).2 ≤ 10 * budget := by
    cases source with
    | union a b =>
        simp only [tyNodes] at fits
        have first := recursive a target (by omega)
        have last := recursive b target (by omega)
        simp only [conj]
        omega
    | _ => change 1 ≤ 10 * budget; omega
  have toInter : (match target with
      | .inter a b => conj (next source a) (next source b)
      | _ => atom false).2 ≤ 10 * budget := by
    cases target with
    | inter a b =>
        simp only [tyNodes] at fits
        have first := recursive source a (by omega)
        have last := recursive source b (by omega)
        simp only [conj]
        omega
    | _ => change 1 ≤ 10 * budget; omega
  have toUnion : (match target with
      | .union a b => disj (next source a) (next source b)
      | _ => atom false).2 ≤ 10 * budget := by
    cases target with
    | union a b =>
        simp only [tyNodes] at fits
        have first := recursive source a (by omega)
        have last := recursive source b (by omega)
        simp only [disj]
        omega
    | _ => change 1 ≤ 10 * budget; omega
  have fromInter : (match source with
      | .inter a b => disj (next a target) (next b target)
      | _ => atom false).2 ≤ 10 * budget := by
    cases source with
    | inter a b =>
        simp only [tyNodes] at fits
        have first := recursive a target (by omega)
        have last := recursive b target (by omega)
        simp only [disj]
        omega
    | _ => change 1 ≤ 10 * budget; omega
  have pairBound : (match source, target with
      | .pair a b, .pair c d => conj (next a c) (next b d)
      | _, _ => atom false).2 ≤ 10 * budget := by
    cases source with
    | pair a b =>
        cases target with
        | pair c d =>
            simp only [tyNodes] at fits
            have first := recursive a c (by omega)
            have last := recursive b d (by omega)
            simp only [conj]
            omega
        | _ => change 1 ≤ 10 * budget; omega
    | _ => change 1 ≤ 10 * budget; omega
  have variantBound : (match source, target with
      | .variant label a, .variant other b => conj (atom (decide (label = other))) (next a b)
      | _, _ => atom false).2 ≤ 10 * budget := by
    cases source with
    | variant label a =>
        cases target with
        | variant other b =>
            simp only [tyNodes] at fits
            have payload := recursive a b (by omega)
            simp only [conj, atom]
            omega
        | _ => change 1 ≤ 10 * budget; omega
    | _ => change 1 ≤ 10 * budget; omega
  have arrowBound : (match source, target with
      | .arrow a ar b br, .arrow c cr d dr =>
          conj (conj (conj (rowEqCount ar cr) (rowEqCount br dr)) (next c a)) (next b d)
      | _, _ => atom false).2 ≤ 10 * budget := by
    cases source with
    | arrow a ar b br =>
        cases target with
        | arrow c cr d dr =>
            simp only [tyNodes] at fits
            have input := recursive c a (by omega)
            have output := recursive b d (by omega)
            have inputRow := rowEqCount_bound ar cr
            have outputRow := rowEqCount_bound br dr
            simp only [conj]
            omega
        | _ => change 1 ≤ 10 * budget; omega
    | _ => change 1 ≤ 10 * budget; omega
  have recordBound : (match source, target with
      | .record label a rest, .record other b tail =>
          conj (conj (conj (conj (atom (decide (label = other)))
            (spineCount rest)) (spineCount tail)) (next a b)) (next rest tail)
      | _, _ => atom false).2 ≤ 10 * budget := by
    cases source with
    | record label a rest =>
        cases target with
        | record other b tail =>
            simp only [tyNodes] at fits
            have first := recursive a b (by omega)
            have last := recursive rest tail (by omega)
            have firstSpine := spineCount_bound rest
            have lastSpine := spineCount_bound tail
            simp only [conj, atom]
            omega
        | _ => change 1 ≤ 10 * budget; omega
    | _ => change 1 ≤ 10 * budget; omega
  simp only [step, disj, atom] at *
  omega

theorem fuelCount_bound (fuel : Nat) (source target : TyTerm (Fin n))
    (size : Nat) (fits : tyNodes source + tyNodes target ≤ size) :
    (fuelCount fuel source target).2 ≤ (size + 1) * 128 ^ fuel := by
  induction fuel generalizing source target with
  | zero => simp [fuelCount]
  | succ fuel ih =>
      have power : 1 ≤ 128 ^ fuel := Nat.one_le_pow _ _ (by decide)
      have large : size + 1 ≤ (size + 1) * 128 ^ fuel := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (size + 1) power
      have bounded := step_bound (fuelCount fuel) source target size ((size + 1) * 128 ^ fuel)
        fits large (fun first last small => ih first last small)
      simpa only [fuelCount, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using bounded

def symbolicCount (source target : TyTerm (Fin n)) : Bool × Nat :=
  fuelCount (nodes source + nodes target) source target

theorem symbolicCount_value (source target : TyTerm (Fin n)) :
    (symbolicCount source target).1 = symbolicCheck source target :=
  fuelCount_value _ _ _ (Nat.le_refl _)

/-- A deliberately conservative exponential reference bound. Full input
size includes arrow rows; recursion depth uses the checker's own measure. -/
theorem symbolicCount_bound (source target : TyTerm (Fin n)) :
    (symbolicCount source target).2 ≤
      (tyNodes source + tyNodes target + 1) * 128 ^ (nodes source + nodes target) :=
  fuelCount_bound _ _ _ _ (Nat.le_refl _)

theorem nodes_le_total (term : TyTerm (Fin n)) : nodes term ≤ tyNodes term := by
  induction term <;> simp_all only [nodes, tyNodes] <;> omega

def checkBudget (size : Nat) : Nat := (size + 1) * 128 ^ size

theorem checkBudget_mono (first last : Nat) (ordered : first ≤ last) :
    checkBudget first ≤ checkBudget last := by
  apply Nat.mul_le_mul (Nat.add_le_add_right ordered 1)
  exact Nat.pow_le_pow_right (by decide) ordered

theorem symbolicCount_size_bound (source target : TyTerm (Fin n)) (size : Nat)
    (fits : tyNodes source + tyNodes target ≤ size) :
    (symbolicCount source target).2 ≤ checkBudget size := by
  have sourceSize := nodes_le_total source
  have targetSize := nodes_le_total target
  exact Nat.le_trans (symbolicCount_bound source target)
    (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right (by decide) (by omega)))

end Yulang.TypeSimplificationCheckCost
