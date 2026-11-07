import Yulang.ProducerRanked

/-!
# Constructor grouping for the ranked producer equivalence

The pass below chooses the grouped presentation of unions of two pairs,
same-label records and same-tag variants. It recursively groups their
components and preserves real arrow arguments and rows. Equal base names and
the two width-record bounds are merged as well.

This is a verified constructor-factoring pass, not yet a complete canonical
display algorithm: it does not sort arbitrary union/intersection members,
rename variables, flatten all mixed-shape alternatives or decide equivalence.
-/

namespace Yulang.ProducerNormalForm

open StructuralBase (Ty)
open ProducerRanked

universe u
variable {Row : Type u} {leRow : Row → Row → Prop}

/-- Keep same-constructor alternatives grouped, recursively in each component.
Only the first structural argument drives recursion; there is no fuel. -/
def merge : Ty Row → Ty Row → Ty Row
  | .base first, .base last => if first = last then .base first else .union (.base first) (.base last)
  | .emptyRecord, .emptyRecord => .emptyRecord
  | .pair a b, .pair c d => .pair (merge a c) (merge b d)
  | .record first a rest, .record last b tail =>
      if first = last then .record first (merge a b) (merge rest tail)
      else .union (.record first a rest) (.record last b tail)
  | .variant first a, .variant last b =>
      if first = last then .variant first (merge a b)
      else .union (.variant first a) (.variant last b)
  | left, right => .union left right

theorem union_idempotent (type : Ty Row) : ProducerEq leRow (.union type type) type := by
  apply (producerEq_iff_probe _ _).mpr
  intro rank obs
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

def normalize : Ty Row → Ty Row
  | .base name => .base name
  | .bottom => .bottom
  | .top => .top
  | .union a b => merge (normalize a) (normalize b)
  | .inter a b => .inter (normalize a) (normalize b)
  | .pair a b => .pair (normalize a) (normalize b)
  | .emptyRecord => .emptyRecord
  | .record label value rest => .record label (normalize value) (normalize rest)
  | .variant label value => .variant label (normalize value)
  | .arrow input inputRow output outputRow =>
      .arrow (normalize input) inputRow (normalize output) outputRow

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
    (type : Ty Row) (rank : Nat) (environment : ProducerDemand.Environment Row)
    (demand : ProducerDemand.Demand Row) :
    AcceptAt leRow rank environment (normalize type) demand ↔
      AcceptAt leRow rank environment type demand := by
  have same := normalize_equivalent rowRefl rowTrans type
  exact ⟨same.2 rank environment demand, same.1 rank environment demand⟩

namespace Examples

theorem grouped_pair :
    normalize (Row := Row)
      (.union (.pair (.base .int) (.base .int)) (.pair (.base .int) (.base .str))) =
      .pair (.base .int) (.union (.base .int) (.base .str)) := rfl

theorem grouped_record (label : Nat) :
    normalize (Row := Row)
      (.union (.record label (.base .int) .emptyRecord) (.record label (.base .str) .emptyRecord)) =
      .record label (.union (.base .int) (.base .str)) .emptyRecord := by
  simp [normalize, merge]

theorem grouped_variant (tag : Nat) :
    normalize (Row := Row)
      (.union (.variant tag (.base .int)) (.variant tag (.base .str))) =
      .variant tag (.union (.base .int) (.base .str)) := by
  simp [normalize, merge]

end Examples
end Yulang.ProducerNormalForm
