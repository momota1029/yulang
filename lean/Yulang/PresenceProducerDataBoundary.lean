import Yulang.PresenceLegacyBridge
import Yulang.ProducerRanked

/-!
# Producer grouping does not identify strict data meanings

The demand order groups a union of pairs component by component. In
particular `(bottom, B) | (A, bottom)` and `(A, B)` have the same demands,
although the former always has an empty strict data interpretation. For
`A = B = int`, the latter has a concrete data inhabitant.

Consequently the existing strict data interpretation cannot factor exactly
through a carrier that identifies all ranked producer equivalents. This
does not rule out a common presence/function model: an independent runtime
interpretation may retain information that the demand equivalence forgets.
No set-theoretic subtype relation or constructor strictness equation is
added to the producer order by this module.
-/

namespace Yulang.PresenceProducerDataBoundary

open StructuralBase (Ty)
open SourceDataRuntime (Value)

universe u v
variable {Row : Type u}

/-- All finite negative-context ranks agree, for every row relation and
arbitrary two components. No nonemptiness premise is imposed. -/
theorem crossed_bottom_pair_equivalent (leRow : Row → Row → Prop)
    (first last : Ty Row) :
    ProducerRanked.ProducerEq leRow
      (.union (.pair .bottom last) (.pair first .bottom)) (.pair first last) := by
  apply (ProducerRanked.producerEq_iff_probe _ _).mpr
  intro rank observation
  cases rank <;> cases observation <;>
    simp [ProducerRanked.ProbeAt, ProducerRanked.ProbeStep]

def diagonal : Ty Row :=
  .union (.pair .bottom (.base .int)) (.pair (.base .int) .bottom)

def grouped : Ty Row := .pair (.base .int) (.base .int)

theorem diagonal_equivalent (leRow : Row → Row → Prop) :
    ProducerRanked.ProducerEq leRow (diagonal : Ty Row) grouped :=
  crossed_bottom_pair_equivalent leRow (.base .int) (.base .int)

/-- The existing finite data interpretation is empty at every outer mask. -/
theorem diagonal_data_empty (mask : DataTypeSemantics.Mask) (value : Value) :
    ¬ DataTypeSemantics.Holds (diagonal : Ty Row) mask value := by
  cases value <;> simp [diagonal, DataTypeSemantics.Holds]

theorem grouped_data_inhabited (mask : DataTypeSemantics.Mask) :
    DataTypeSemantics.Holds (grouped : Ty Row) mask (.pair (.base .int) (.base .int)) :=
  ⟨rfl, rfl⟩

theorem data_meanings_differ (mask : DataTypeSemantics.Mask) :
    DataTypeSemantics.Holds (diagonal : Ty Row) mask ≠
      DataTypeSemantics.Holds (grouped : Ty Row) mask := by
  intro same
  exact diagonal_data_empty mask (.pair (.base .int) (.base .int))
    (same.symm ▸ grouped_data_inhabited mask)

/-- The same distinction holds for the already established presence-data
translation, without changing its meaning or its treatment of masks. -/
theorem translated_meanings_differ (hidden : List Nat) :
    PresenceLegacyBridge.translate (diagonal : Ty Row) hidden ≠
      PresenceLegacyBridge.translate (grouped : Ty Row) hidden := by
  intro same
  let witness : Value := .pair (.base .int) (.base .int)
  have groupedValid : PresenceLegacyBridge.translate (grouped : Ty Row) hidden witness :=
    (PresenceLegacyBridge.translate_exact _ hidden witness).mpr
      (grouped_data_inhabited _)
  exact diagonal_data_empty (fun label => label ∈ hidden) witness
    ((PresenceLegacyBridge.translate_exact _ hidden witness).mp (same.symm ▸ groupedValid))

/-- No target carrier can both identify all ranked producer equivalents
and recover the existing strict data membership exactly. The claim concerns
this exact factorization, not existence of a common presence/function model. -/
theorem no_exact_data_factorization (leRow : Row → Row → Prop)
    {Carrier : Type v} (embed : Ty Row → Carrier) (meaning : Carrier → Value → Prop)
    (equates : ∀ source target, ProducerRanked.ProducerEq leRow source target →
      embed source = embed target)
    (exact : ∀ type value, meaning (embed type) value ↔
      DataTypeSemantics.Holds type DataTypeSemantics.visible value) : False := by
  have same := equates diagonal grouped (diagonal_equivalent leRow)
  have valid := (exact grouped (.pair (.base .int) (.base .int))).mpr
    (grouped_data_inhabited DataTypeSemantics.visible)
  rw [← same] at valid
  exact diagonal_data_empty DataTypeSemantics.visible (.pair (.base .int) (.base .int))
    ((exact diagonal _).mp valid)

end Yulang.PresenceProducerDataBoundary
