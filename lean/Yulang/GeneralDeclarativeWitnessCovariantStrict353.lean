import Yulang.GeneralDeclarativeWitnessCovariantIntervalModel353
import Yulang.CommonNominalFullModelMap

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeWitnessCovariantStrict353
open GeneralDeclarativeWitnessCovariantIntervalModel353 (model int bool whole)
open GeneralDeclarativeWitnessCovariantOrigin353 (assigned)
open CommonNominalFullCarrier (Ty Equivalent Subtype subtype_refl subtype_trans common_union_is_join)
open CommonNominalFullDemand (ProducerLe Environment ProbeAt producerLe_iff_probe)

def unitTy : Ty := .base .unit

/-- The independent role probe admits both written arms, but no Unit.
This shows the concrete widened upper is genuinely different. -/
theorem unit_outside_merge : ¬ Subtype unitTy whole := by
  intro below
  have ground := below 0
  change ProducerLe Common.rowLe (.base .unit) (.union (.base .int) (.base .bool)) at ground
  let env : Environment Common.Row := ⟨fun _ => .bottom,fun _ => [.base .int,.base .bool]⟩
  have admits : ProbeAt Common.rowLe 0 env (.union (.base .int) (.base .bool)) (.role 0) := by
    simp [ProbeAt,CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep,env]
  have bad := (producerLe_iff_probe _ _).mp ground 0 env (.role 0) admits
  simp [ProbeAt,CommonNominalFullDemand.ProbeStep,CommonNominalFullDemand.MaskedProbeStep,env] at bad

theorem upper_is_genuinely_larger : ¬ Subtype (model 10).1 (model 9).1 := by
  intro same
  have unitIncluded : Subtype unitTy (.union whole unitTy) :=
    ((common_union_is_join whole unitTy _).mp (subtype_refl _)).2
  exact unit_outside_merge (subtype_trans unitIncluded same)

theorem common_upper_is_genuinely_larger :
    ¬ Common.Subtype (assigned model 10).1 (assigned model 9).1 := by
  intro same
  apply upper_is_genuinely_larger
  have old := (CommonNominalFullModelMap.subtype_exact (assigned model 10).1 (assigned model 9).1).mpr same
  exact old

theorem common_lower_is_genuinely_smaller :
    ¬ Common.Subtype (assigned model 9).1 (assigned model 7).1 := by
  intro same
  have back := (CommonNominalFullModelMap.subtype_exact (assigned model 9).1 (assigned model 7).1).mpr same
  apply GeneralDeclarativeWitnessCovariantIntervalModel353.lower_strict
  exact ⟨((common_union_is_join int bool whole).mp (subtype_refl _)).1,back⟩

end Yulang.GeneralDeclarativeWitnessCovariantStrict353
