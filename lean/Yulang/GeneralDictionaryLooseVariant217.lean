import Yulang.GeneralDictionaryInspectionHeads215

/-! The known outer variant envelope admits inequivalent actual payloads.
This is a semantic interval regression, not an I40 reachable-state counterexample. -/
namespace Yulang.GeneralDictionaryLooseVariant217
open CommonNominalFullCarrier GeneralDictionaryInspectionHeads215

theorem bottom_below (value : Ty) : Subtype .bottom value := by
  intro depth
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro rank env obs _
  exact CommonNominalFullDemand.probeAt_bottom rank obs

theorem below_top (value : Ty) : Subtype value .top := by
  intro depth
  apply (CommonNominalFullDemand.producerLe_iff_probe _ _).mpr
  intro rank env obs held
  cases obs <;> cases rank <;>
    simp_all [observeTy,CommonNominalSyntax.Layer.evalAt,CommonNominalFullDemand.ProbeAt,
      CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep]

def low : Ty := variant 0 .bottom
def high : Ty := variant 0 .top
def first : Ty := variant 0 (.base .int)
def second : Ty := variant 0 (.base .bool)

theorem fits_first : Subtype low first ∧ Subtype first high :=
  ⟨(common_variant_iff ..).mpr (bottom_below _),(common_variant_iff ..).mpr (below_top _)⟩
theorem fits_second : Subtype low second ∧ Subtype second high :=
  ⟨(common_variant_iff ..).mpr (bottom_below _),(common_variant_iff ..).mpr (below_top _)⟩
theorem unequal : ¬ Equivalent first second := by
  intro equal
  have below := (common_variant_iff ..).mp equal.1
  have impossible := tag_subtype (tagged_scalar .int) (tagged_scalar .bool) below
  cases impossible

theorem same_outer_tag : Tagged low (.variant 0) ∧ Tagged high (.variant 0) ∧
    Tagged first (.variant 0) ∧ Tagged second (.variant 0) := by
  exact ⟨by intro env; rfl,by intro env; rfl,by intro env; rfl,by intro env; rfl⟩
end Yulang.GeneralDictionaryLooseVariant217
