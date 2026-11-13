import Yulang.GeneralNominalCaptureMerges
import Yulang.CommonNominalFullModelMap
import Yulang.CommonRoleMergedCaptureBoundary

/-! A shared actual value does not determine nonpoint interval endpoints.
This isolates the point-leaf side condition; no reobserve counterexample is asserted. -/
namespace Yulang.GeneralDictionarySemanticCollapsePointBoundary
open CommonNominalFullCarrier
abbrev assignment : GeneralNominalCommonBridge.Assignment :=
 fun identity => (if identity = 0 then .bottom else .base .int,Common.rowEmpty)
abbrev first : GeneralSourceState.Interval := (0,1)
abbrev last : GeneralSourceState.Interval := (1,1)

theorem shared_actual_fits :
 GeneralNominalCaptureMerges.Fits assignment first (.base .int) ∧
 GeneralNominalCaptureMerges.Fits assignment last (.base .int) := by
 refine ⟨⟨?_,subtype_refl _⟩,subtype_refl _,subtype_refl _⟩
 exact (CommonNominalFullModelMap.subtype_exact .bottom (.base .int)).mpr
   (CommonBoundCoalescing.bottom_le _)

theorem lower_endpoints_differ :
 ¬ Equivalent (assignment first.1).1 (assignment last.1).1 := by
 intro same
 apply CommonRoleMergedCaptureBoundary.bottom_not_int
 exact ⟨(CommonNominalFullModelMap.subtype_exact .bottom (.base .int)).mp same.1,
   (CommonNominalFullModelMap.subtype_exact (.base .int) .bottom).mp same.2⟩

theorem upper_endpoints_equal :
 Equivalent (assignment first.2).1 (assignment last.2).1 := ⟨subtype_refl _,subtype_refl _⟩

theorem first_nonpoint : first.1 ≠ first.2 := by decide +kernel

theorem shared_actual_not_endpoint_equivalence :
 ¬ (∀ (model : GeneralNominalCommonBridge.Assignment)
     (a b : GeneralSourceState.Interval) (actual : Ty),
   GeneralNominalCaptureMerges.Fits model a actual →
   GeneralNominalCaptureMerges.Fits model b actual →
   Equivalent (model a.1).1 (model b.1).1 ∧ Equivalent (model a.2).1 (model b.2).1) := by
 intro claim
 exact lower_endpoints_differ (claim assignment first last (.base .int)
   shared_actual_fits.1 shared_actual_fits.2).1
end Yulang.GeneralDictionarySemanticCollapsePointBoundary
