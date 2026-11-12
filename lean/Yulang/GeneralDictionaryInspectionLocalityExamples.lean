import Yulang.GeneralDictionaryInspectionLocality
import Yulang.GeneralDictionaryInspectionTransportExamples

/-! Finite-footprint regression on the actual generated-child descriptor refresh.
The changed child slot is absent from the parent's variable-query footprint.
No equality of computed reports is assumed in the resulting source instance. -/
namespace Yulang.GeneralDictionaryInspectionLocalityExamples
open GeneralDictionaryInspectionTransport
open GeneralDictionaryInspectionTransportExamples (observation reobserve_eq)
open GeneralDictionaryInspectionLocality
open GeneralNominalFeedbackObstruction
open GeneralNominalFeedbackRefresh
open GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)

/-- The variable subquery captures slots 2 and 3 without reading descriptors there. -/
theorem parent_footprint :
    footprints installed.context.state
      (GeneralNominalInspection.queries installed.context.state installed.context.interpretation declaration)
      [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] = [⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩] := by
  have query : GeneralNominalInspection.queries installed.context.state installed.context.interpretation declaration =
      [.nominal 0 [.variables [0]]] := by
    simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
      GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
      GeneralNominalInspection.translate]
    rfl
  rw [query]
  decide +kernel

theorem parent_footprint_agrees : FootprintAt registry installed.context observation root := by
  intro decl visible _ bounds located slot member
  have same := List.mem_singleton.mp visible
  subst decl
  have actual : bounds = [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] :=
    Option.some.inj (located.symm.trans (by decide +kernel))
  subst bounds
  rw [parent_footprint] at member
  simp only [List.mem_cons,List.not_mem_nil,or_false,or_self] at member
  subst slot
  rfl

/-- The unchanged-view, finite-descriptor guard is discharged without report equality. -/
theorem current_parent_from_footprint (m : Assignment) (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext m root 2 [child] := by
  rw [← reobserve_eq]
  exact instance_of_footprint registry installed.context observation rfl m root 2 [child]
    parent_footprint_agrees valid.1
    (GeneralDictionaryOrdinaryTransportExamples.Feedback.current_parent_instance m
      ((refresh_models m).mp valid))

theorem nonvacuous_parent_from_footprint :
    Models refreshed model ∧
      GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext model root 2 [child] := by
  have valid := (refresh_models model).mpr installed_models
  exact ⟨valid,current_parent_from_footprint model valid⟩

/-- A genuinely nested query adds the child endpoints to the conservative
footprint. It does not silently treat nested nominal patterns as variables. -/
theorem nested_nonpoint_footprint :
    footprint installed.context.state (.nominal 0 [.nominal 0 [.variables [0]]]) (⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩) =
      [⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩,⟨2,by decide +kernel⟩,⟨3,by decide +kernel⟩,
        ⟨2,by decide +kernel⟩,⟨3,by decide +kernel⟩] := by
  decide +kernel

set_option backward.isDefEq.respectTransparency false in
/-- Inspecting the changed child itself does observe the new descriptor.
This contrasts with the parent's variable subquery, which never reads it. -/
theorem inspected_child_report_changes :
    (GeneralNominalRecursiveInspection.inspect installed.context.state
      (.nominal 0 []) (⟨2,by decide +kernel⟩,⟨2,by decide +kernel⟩) none).blocked ≠
    (GeneralNominalRecursiveInspection.inspect refreshedContext.state
      (.nominal 0 []) (⟨2,by decide +kernel⟩,⟨2,by decide +kernel⟩) none).blocked := by
  simp only [GeneralNominalRecursiveInspection.inspect,
    GeneralDictionaryInspectionTransportExamples.child_descriptor_changed.1,
    GeneralDictionaryInspectionTransportExamples.child_descriptor_changed.2]
  have head : installed.context.state.view.heads ⟨2,by decide +kernel⟩ = .deferred .unresolved := rfl
  simp only [head]
  have args : GeneralNominalRecursiveInspection.typeArguments
      GeneralNominalFeedbackRefresh.descriptor.arguments = some [(2,2)] := rfl
  simp only [args]
  simp [GeneralNominalRecursiveInspection.inspectMany,
    GeneralNominalRecursiveInspection.Report.visit, GeneralNominalRecursiveInspection.block]

end Yulang.GeneralDictionaryInspectionLocalityExamples
