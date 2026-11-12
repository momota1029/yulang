import Yulang.GeneralDictionarySelectedLocality
import Yulang.GeneralDictionaryInspectionLocalityExamples

/-! Actual journal refresh with selected-key occupancy, not an assumed report
invariance. The child really changes and is rejected, so only the local parent
Instance is concluded. -/
namespace Yulang.GeneralDictionarySelectedLocalityExamples
open GeneralDictionaryInspectionTransport
open GeneralDictionaryInspectionTransportExamples (observation reobserve_eq)
open GeneralDictionaryInspectionLocalityExamples (parent_footprint)
open GeneralDictionarySelectedLocality
open GeneralNominalFeedbackObstruction GeneralNominalFeedbackRefresh
open GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)

theorem parent_occupied : OccupiedFor registry installed.context root 2 := by
  intro decl visible _ _ bounds located slot member
  have same := List.mem_singleton.mp visible
  subst decl
  have actual : bounds = [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] :=
    Option.some.inj (located.symm.trans (by decide +kernel))
  subst bounds
  rw [parent_footprint] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
  subst slot
  exact ⟨GeneralNominalIntervalExamples.descriptor,rfl⟩

theorem recorded_parent_current (m : Assignment) (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext m root 2 [child] := by
  have result := recorded_instance registry root installed GeneralNominalFeedbackRegressions.formed
    packet (by simp [installed,GeneralNominalFeedbackSites.install])
    (GeneralDictionaryOrdinaryTrace.packet_extension packet) observation rfl refresh_certificate
    parent_occupied m valid
  simpa only [GeneralNominalFeedbackObstruction.children_exact,reobserve_eq,GeneralNominalDemandMerging.pointSite] using result

theorem actual_nonvacuous_parent :
    Models refreshed model ∧
    GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext model root 2 [child] ∧
    GeneralNominalFeedbackK2.Local registry refreshed child .rejected :=
  ⟨(refresh_models model).mpr installed_models,
    recorded_parent_current model ((refresh_models model).mpr installed_models),child_rejected⟩

end Yulang.GeneralDictionarySelectedLocalityExamples
