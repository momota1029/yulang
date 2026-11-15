import Yulang.GeneralDictionaryDefaultRevisionEvidence210
import Yulang.GeneralDictionaryDefaultTransportExamples209
import Yulang.GeneralNominalReobservationExamples
import Yulang.GeneralDictionaryReobservationRefinementGap

set_option backward.isDefEq.respectTransparency false

/-! Distinguish existential center choice from universal center independence,
and genuine descriptor revisions from descriptor-preserving refinements. -/
namespace Yulang.GeneralDictionaryDefaultReplayRegression210
open GeneralNominalRecursiveInspection
open GeneralDictionaryDefaultTransportExamples209
open GeneralNominalReobservationExamples

 theorem retained_interval_body :
    GeneralNominalCenteredHeadMatEffects.BodyHolds
      (GeneralDictionaryDefaultSemanticReplay209.recenter (intervalPlan 1) (intervalSite 0) rfl)
      0 intervalModel (.default 0 0 (.var 0)) := interval_default_bottom

 theorem arbitrary_interval_body_fails :
    ¬ GeneralNominalCenteredHeadMatEffects.BodyHolds (intervalPlan 1)
      0 intervalModel (.default 0 0 (.var 0)) := interval_default_int_false

 theorem centers_not_equal : (intervalSite 0).center (0 : Fin 1) ≠ (intervalSite 1).center (0 : Fin 1) := by decide

 theorem real_revision_changes_descriptor :
    (GeneralNominalRefreshFork.state (some true)).nominals 0 ≠ revision.snapshot.nominals (0 : Fin 5) := by
  intro equal
  have args := congrArg (fun value => value.map GeneralNominalState.Descriptor.arguments) equal
  exact (by decide +kernel : ([GeneralNominalState.Parameter.type (2,4)] : List (GeneralNominalState.Parameter 5)) ≠
    [.type (2,2)]) (Option.some.inj args)

 theorem real_revision_certified : GeneralNominalReobservationSteps.Certified revision := revision_certified
 theorem real_revision_improves : GeneralNominalReobservationSteps.Improves revision := revision_improves

 theorem scalar_finished : Finished
    (inspect (GeneralNominalRefreshFork.state (some true)) (.scalar .int) (3,3) none) := by
  simp [Finished,inspect,Report.visit,GeneralNominalRefreshFork.state,GeneralNominalRefreshFork.view]

 theorem scalar_traced : GeneralNominalInspectionTrace197.Trace
    (GeneralNominalRefreshFork.state (some true))
    (GeneralDictionaryDefaultStructuralReobserve210.view revision) (.scalar .int) (3,3) :=
  GeneralDictionaryDefaultStructuralReobserve210.traced revision .scalar scalar_finished

 theorem scalar_queries : GeneralNominalInspection.queries
    (GeneralNominalRefreshFork.state (some true))
    GeneralNominalExamples.interpretation
    ⟨91,0,[.app 2 []],[],[],[]⟩ = [.scalar .int] := by
  simp [GeneralNominalInspection.queries,GeneralDeclarations.Declaration.normalHead,
    GeneralDeclarationPatterns.normalizeArgs,GeneralDeclarationPatterns.normalize,
    GeneralNominalInspection.translate,GeneralNominalExamples.interpretation]

 theorem scalar_candidate_report :
    GeneralNominalReportErasure.erase revision.snapshot
      (GeneralNominalRecursiveCandidates.report
        ⟨revision.snapshot,(GeneralNominalRefreshFork.context (some true)).interpretation⟩
        ⟨91,0,[.app 2 []],[],[],[]⟩ [((3 : Fin 5),(3 : Fin 5))]) =
    GeneralNominalReportErasure.erase (GeneralNominalRefreshFork.state (some true))
      (GeneralNominalRecursiveCandidates.report (GeneralNominalRefreshFork.context (some true))
        ⟨91,0,[.app 2 []],[],[],[]⟩ [(3,3)]) := by
  apply GeneralDictionaryDefaultStructuralReobserve210.candidate_report revision
  · intro query member
    change query ∈ GeneralNominalInspection.queries (GeneralNominalRefreshFork.state (some true))
      GeneralNominalExamples.interpretation ⟨91,0,[.app 2 []],[],[],[]⟩ at member
    rw [scalar_queries] at member
    cases List.mem_singleton.mp member
    exact .scalar
  · change Finished (GeneralNominalRecursiveCandidates.report (GeneralNominalRefreshFork.context (some true))
        ⟨91,0,[.app 2 []],[],[],[]⟩ [(3,3)])
    change Finished (inspectMany (GeneralNominalRefreshFork.state (some true))
      (GeneralNominalInspection.queries (GeneralNominalRefreshFork.state (some true))
        GeneralNominalExamples.interpretation ⟨91,0,[.app 2 []],[],[],[]⟩) [(3,3)] (fun _ => none) 0)
    rw [scalar_queries,inspectMany,GeneralNominalFinishedObservation197.finished_append]
    exact ⟨scalar_finished,by simp [inspectMany,Finished]⟩

end Yulang.GeneralDictionaryDefaultReplayRegression210
