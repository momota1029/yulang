import Yulang.GeneralDictionaryInspectionTransport
import Yulang.GeneralDictionaryOrdinaryTransportExamples
import Yulang.GeneralNominalFeedbackRefresh

/-! A genuine descriptor-changing refresh, discharged through the generic
inspection-preserving transport. The generated child gains a descriptor; the
parent keeps its queried descriptor and exact ordered child list. This proves
its local instance, not a complete dictionary for the rejected child. -/
namespace Yulang.GeneralDictionaryInspectionTransportExamples
open GeneralDictionaryInspectionTransport
open GeneralNominalFeedbackObstruction
open GeneralNominalFeedbackRefresh
open GeneralNominalSaturationState
open GeneralNominalCommonBridge (Assignment)

noncomputable def observation : Observation installed.context.state where
  view := refreshedState.view
  nominals := refreshedState.nominals
  catalogue := refreshedState.catalogue
  bodiesOpaque := refreshedState.bodies_opaque

theorem reobserve_eq : reobserve installed.context observation = refreshedContext := rfl

theorem parent_preserves : PreservesAt registry installed.context observation root := by
  intro decl visible _ bounds located
  have same := List.mem_singleton.mp visible
  subst decl
  have actual : bounds = [(⟨0,by decide +kernel⟩,⟨0,by decide +kernel⟩)] :=
    Option.some.inj (located.symm.trans (by decide +kernel))
  subst bounds
  apply nominal_unary_report installed.context observation declaration ⟨0,by decide +kernel⟩
    GeneralNominalIntervalExamples.descriptor rfl rfl 0
    (⟨2,by decide +kernel⟩,⟨3,by decide +kernel⟩) rfl
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate]
  rfl

/-- Current-context Instance obtained by the generic transport, rather than
reproving the source branch semantics for this example. -/
theorem current_parent_instance (m : Assignment) (valid : Models refreshed m) :
    GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext m root 2 [child] := by
  rw [← reobserve_eq]
  apply instance_of_reports registry installed.context observation m root 2 [child] parent_preserves
  · exact valid.1
  · exact GeneralDictionaryOrdinaryTransportExamples.Feedback.current_parent_instance m
      ((refresh_models m).mp valid)

/-- The refresh and transported source instance share an explicit actual model. -/
theorem nonvacuous_refreshed_parent :
    Models refreshed model ∧
      GeneralDictionaryRecursiveEvidence.Instance registry refreshedContext model root 2 [child] := by
  have valid := (refresh_models model).mpr installed_models
  exact ⟨valid,current_parent_instance model valid⟩

/-- This is not an identity refresh: the generated child's descriptor changes. -/
theorem child_descriptor_changed :
    installed.context.state.nominals ⟨2,by decide +kernel⟩ = none ∧
    refreshedContext.state.nominals ⟨2,by decide +kernel⟩ =
      some GeneralNominalFeedbackRefresh.descriptor := ⟨rfl,rfl⟩

end Yulang.GeneralDictionaryInspectionTransportExamples
