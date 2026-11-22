import Yulang.GeneralDeclarativeWitnessCovariantFixture352
import Yulang.CommonNominalFullConstructors

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantCarrier352
open CommonNominalFullCarrier (Ty Subtype Equivalent nominal subtype_refl subtype_trans
  nominal_regular_invariant_exact common_union_is_join)

def integer : Ty := .base .int
def boolean : Ty := .base .bool
def whole : Ty := .union integer boolean

private theorem base_not_below {a b : Inference.Base} (different : a ≠ b) :
    ¬ Subtype (.base a) (.base b) := by
  intro below
  have h := below 0
  change CommonNominalFullDemand.ProducerLe Common.rowLe (.base a) (.base b) at h
  have tested := (CommonNominalFullDemand.producerLe_iff_probe _ _).mp h 0
    ⟨fun _ => .bottom,fun _ => []⟩ (.base b) rfl
  cases tested
  exact different rfl

theorem not_left_payload : ¬ Equivalent integer whole := by
  intro split
  have included : Subtype boolean whole :=
    ((common_union_is_join integer boolean whole).mp (subtype_refl _)).2
  exact base_not_below (by decide : Inference.Base.bool ≠ .int) (subtype_trans included split.2)

theorem not_right_payload : ¬ Equivalent boolean whole := by
  intro split
  have included : Subtype integer whole :=
    ((common_union_is_join integer boolean whole).mp (subtype_refl _)).1
  exact base_not_below (by decide : Inference.Base.int ≠ .bool) (subtype_trans included split.2)

/-- Turning on the old source interpreter's invariant route for a declaration
marked covariant would get actual valid nominal comparisons wrong, even for
closed integer and Boolean arms. This is not a negative language rule. -/
theorem invariant_flag_is_not_a_covariant_encoding (name : Nat) :
    ¬ Subtype (nominal name [.inl integer]) (nominal name [.inl whole]) ∧
    ¬ Subtype (nominal name [.inl boolean]) (nominal name [.inl whole]) := by
  constructor
  · intro encodes
    exact not_left_payload (((nominal_regular_invariant_exact ..).mp encodes).2.2 0 _ _ rfl rfl)
  · intro encodes
    exact not_right_payload (((nominal_regular_invariant_exact ..).mp encodes).2.2 0 _ _ rfl rfl)

end Yulang.GeneralDeclarativeWitnessCovariantCarrier352
