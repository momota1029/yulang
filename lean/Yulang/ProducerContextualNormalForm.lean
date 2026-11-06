import Yulang.ProducerNormalForm
import Yulang.ProducerContextual

/-!
# Constructor grouping under contextual demands

The executable pass is exactly the existing `ProducerNormalForm.normalize`.
This module proves it preserves the Q5-aware contextual order, including
arbitrary type-parameter demands, role heads, masks, and negative arrow
contexts. It does not change the old pass or weaken its earlier theorem.

The final counterexample records why this pass alone cannot be an interface
cache key: equivalent differently ordered unions still have distinct syntax.
-/

namespace Yulang.ProducerContextualNormalForm

open StructuralBase (Ty)
open ProducerContextual
open ProducerNormalForm (merge normalize)

universe u
variable {Row : Type u} {leRow : Row → Row → Prop}

theorem union_idempotent (type : Ty Row) : ProducerEq leRow (.union type type) type := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank env obs
  simp

/-- The executable grouping itself preserves all finite-rank demands,
including every demand variable assignment and every nested demand mask. -/
theorem merge_equivalent (left right : Ty Row) :
    ProducerEq leRow (merge left right) (.union left right) := by
  induction left generalizing right with
  | base first =>
      cases right with
      | base last =>
          by_cases same : first = last
          · subst last
            simpa only [merge, ↓reduceIte] using producerEq_symm (union_idempotent (Ty.base first))
          · simp only [merge, same, ↓reduceIte]
            exact producerEq_refl _
      | _ => exact producerEq_refl _
  | emptyRecord =>
      cases right with
      | emptyRecord => exact producerEq_symm (union_idempotent .emptyRecord)
      | _ => exact producerEq_refl _
  | pair a b iha ihb =>
      cases right with
      | pair c d =>
          exact producerEq_trans (producerEq_pair (iha c) (ihb d))
            (producerEq_symm (pair_union_group a b c d))
      | _ => exact producerEq_refl _
  | record first a rest iha ihr =>
      cases right with
      | record last b tail =>
          by_cases same : first = last
          · subst last
            simp only [merge, ↓reduceIte]
            exact producerEq_trans (producerEq_record first (iha b) (ihr tail))
              (producerEq_symm (record_union_group first a rest b tail))
          · simp only [merge, same, ↓reduceIte]
            exact producerEq_refl _
      | _ => exact producerEq_refl _
  | variant first a ih =>
      cases right with
      | variant last b =>
          by_cases same : first = last
          · subst last
            simp only [merge, ↓reduceIte]
            exact producerEq_trans (producerEq_variant first (ih b)) (variant_union first a b)
          · simp only [merge, same, ↓reduceIte]
            exact producerEq_refl _
      | _ => exact producerEq_refl _
  | bottom | top | union | inter | arrow => exact producerEq_refl _

/-- All finite producers are covered, including intersections, open record
tails and negative arrow positions. The only assumptions are row reflexivity
and transitivity. The original type need not already be a normal form. -/
theorem normalize_equivalent (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c) (type : Ty Row) :
    ProducerEq leRow (normalize type) type := by
  induction type with
  | base | bottom | top | emptyRecord => exact producerEq_refl _
  | union a b iha ihb => exact producerEq_trans (merge_equivalent _ _) (producerEq_union iha ihb)
  | inter a b iha ihb => exact producerEq_inter iha ihb
  | pair a b iha ihb => exact producerEq_pair iha ihb
  | record label value rest ihv ihr => exact producerEq_record label ihv ihr
  | variant label value ih => exact producerEq_variant label ih
  | arrow input inputRow output outputRow ihi iho =>
      exact producerEq_arrow rowRefl rowTrans inputRow outputRow ihi iho

theorem normalize_accept_iff (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (type : Ty Row) (rank : Nat) (environment : ProducerContextual.Environment Row)
    (demand : ProducerContextual.Demand Row) :
    AcceptAt leRow rank environment (normalize type) demand ↔
      AcceptAt leRow rank environment type demand := by
  have same := normalize_equivalent rowRefl rowTrans type
  exact ⟨same.2 rank environment demand, same.1 rank environment demand⟩

/-- Constructor grouping is sound but not a complete canonical interface. -/
theorem normalize_not_complete (leRow : Row → Row → Prop) :
    ∃ first last : Ty Row, ProducerEq leRow first last ∧ normalize first ≠ normalize last := by
  refine ⟨.union (.base .int) (.base .str), .union (.base .str) (.base .int), ?_, ?_⟩
  · apply (producerEq_iff_probe _ _).mpr
    intro rank env obs
    simp only [probeAt_union]
    exact and_comm
  · simp [normalize, merge]

end Yulang.ProducerContextualNormalForm
