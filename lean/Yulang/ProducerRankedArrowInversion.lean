import Yulang.ProducerRanked

/-!
# Arrow inversion at a closed union-free target argument

The current observer grammar tests arrow arguments only with
`ProducerDemand.Negative`. That grammar contains no union, variable or mask.
For a target arrow whose argument is the embedding of such a requirement,
the requirement itself is an available separating test. Consequently all
four arrow components can be recovered from the ranked producer comparison.

Result and row inversion hold for arbitrary arguments. Argument inversion
below is restricted to a closed `Negative` target argument. No density of
these requirements among all producers, arbitrary-domain arrow inversion,
regular-graph inversion or source-inference completeness is asserted.
-/

namespace Yulang.ProducerRankedArrowInversion

open StructuralBase ProducerRanked
open ProducerDemand (Negative)

universe u
variable {Row : Type u} {leRow : Row → Row → Prop}

/-- Every result demand is observed directly, for all ranks and arbitrary
source/target argument types. No property of the row relation is needed. -/
theorem arrow_result_inversion
    {input input' output output' : Ty Row} {inputRow inputRow' outputRow outputRow' : Row}
    (below : ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow')) :
    ProducerLe leRow output output' := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank obs accepted
  have test := (producerLe_iff_probe _ _).mp below rank (.arrowResult obs)
  cases rank <;> exact test accepted

/-- Input computation rows are reflected contravariantly. Reflexivity is
required only to use the target row itself as a test. -/
theorem arrow_input_row_inversion (rowRefl : ∀ row, leRow row row)
    {input input' output output' : Ty Row} {inputRow inputRow' outputRow outputRow' : Row}
    (below : ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow')) :
    leRow inputRow' inputRow :=
  (producerLe_iff_probe _ _).mp below 0 (.arrowInputRow inputRow') (rowRefl inputRow')

/-- Output computation rows are reflected covariantly, under row reflexivity. -/
theorem arrow_output_row_inversion (rowRefl : ∀ row, leRow row row)
    {input input' output output' : Ty Row} {inputRow inputRow' outputRow outputRow' : Row}
    (below : ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow input' inputRow' output' outputRow')) :
    leRow outputRow outputRow' :=
  (producerLe_iff_probe _ _).mp below 0 (.arrowOutputRow outputRow') (rowRefl outputRow')

/-- For every source argument and every closed union-free target argument,
arrow subtyping reflects the full new producer order on arguments. All ranks
are recovered by testing the enclosing arrow at the successor rank. -/
theorem arrow_negative_argument_inversion
    {input output output' : Ty Row} {expected : Negative Row}
    {inputRow inputRow' outputRow outputRow' : Row}
    (below : ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow expected.embed inputRow' output' outputRow')) :
    ProducerLe leRow expected.embed input := by
  apply (producerLe_iff_probe _ _).mpr
  intro rank obs accepted
  have targetAccepted : ProbeAt leRow (rank + 1)
      (.arrow expected.embed inputRow' output' outputRow') (.arrowArgument expected) :=
    fun _ valid => valid
  have sourceAccepted := (producerLe_iff_probe _ _).mp below (rank + 1)
    (.arrowArgument expected) targetAccepted
  exact sourceAccepted obs accepted

/-- Complete arrow decomposition for this stated target-domain fragment.
Both arguments are compared in the new ranked order; row reflexivity and
transitivity are the only row assumptions. -/
theorem arrow_negative_argument_iff (rowRefl : ∀ row, leRow row row)
    (rowTrans : ∀ {a b c}, leRow a b → leRow b c → leRow a c)
    (input output output' : Ty Row) (expected : Negative Row)
    (inputRow inputRow' outputRow outputRow' : Row) :
    ProducerLe leRow (.arrow input inputRow output outputRow)
      (.arrow expected.embed inputRow' output' outputRow') ↔
      ProducerLe leRow expected.embed input ∧ leRow inputRow' inputRow ∧
        ProducerLe leRow output output' ∧ leRow outputRow outputRow' := by
  constructor
  · intro below
    exact ⟨arrow_negative_argument_inversion below, arrow_input_row_inversion rowRefl below,
      arrow_result_inversion below, arrow_output_row_inversion rowRefl below⟩
  · rintro ⟨argument, incoming, result, outgoing⟩
    exact ProducerRanked.producerLe_arrow (leRow := leRow) rowTrans argument incoming result outgoing

end Yulang.ProducerRankedArrowInversion
