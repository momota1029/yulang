import Yulang.GeneralDepthTwoTerminalFrame300
import Yulang.GeneralDepthTwoFinalParents300

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 33000
set_option maxHeartbeats 13000000
namespace Yulang.GeneralDepthTwoEvidence300
open GeneralGeneratedNestedSource299 (initial root)
open GeneralGeneratedNestedPredictions299 (compiled middle terminal)
open GeneralNominalExamples (registry)
open GeneralDeclarationExamples (roles)
open GeneralDepthTwoFirstInstall300 (after)
open GeneralDepthTwoSecondInstall300 (final final_requests actual_terminal)
open GeneralNominalVersionedJournal232 (Models)
open GeneralNominalVersionedEvidence231 (Instance)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseDisplayFrame276 (classes_empty)

theorem terminal_instance (m : Assignment) (valid : Models final m) :
    Instance compiled final.core m terminal 3 [] := by
  let p := GeneralDepthTwoTerminalPlan300.plan
  refine ⟨p,GeneralNominalVersionedEvidence231.certificate_of_semantics
    GeneralDepthTwoTerminalFrame300.frame GeneralDepthTwoTerminalPlan300.children_empty.symm
    (GeneralDepthTwoTerminalPlan300.holds m valid) ?_ ?_⟩
  · intro output member
    rw [final_requests] at member
    cases member
  · exact classes_empty (final_requests terminal) p m

theorem terminal_evidence (m : Assignment) (valid : Models final m) :
    (boundary roles).Evidence registry final m terminal (.node 3 []) :=
  GeneralNominalVersionedEvidence231.evidence_leaf (terminal_instance m valid)

theorem middle_evidence (m : Assignment) (valid : Models final m) :
    (boundary roles).Evidence registry final m middle (.node 1 [.node 3 []]) :=
  GeneralNominalVersionedEvidence231.evidence_node
    (GeneralDepthTwoFinalParents300.middle_instance m valid) (.cons (terminal_evidence m valid) .nil)

theorem root_evidence (m : Assignment) (valid : Models final m) :
    (boundary roles).Evidence registry final m root (.node 1 [.node 1 [.node 3 []]]) :=
  GeneralNominalVersionedEvidence231.evidence_node
    (GeneralDepthTwoFinalParents300.root_instance m valid) (.cons (middle_evidence m valid) .nil)

theorem final_models (m : Assignment) : Models final m ↔ Models initial m :=
  (GeneralDepthTwoSecondInstall300.models m).trans (GeneralDepthTwoFirstInstall300.models m)

theorem final_edges : final.core.erased.current.edges = [(root,middle),(middle,terminal)] := by
  change after.core.erased.current.edges ++ GeneralNominalVersionedChildren232.edges GeneralDepthTwoMiddleContext300.plan = _
  rw [GeneralGeneratedNestedInstallInterface299.only_first_edge (e := GeneralDepthTwoRootFrame300.effect) rfl]
  unfold GeneralNominalVersionedChildren232.edges
  rw [GeneralDepthTwoMiddleContext300.same_children]
  rfl

theorem actual_dictionary :
    (boundary roles).Step registry root initial after ∧
    (boundary roles).Step registry root after final ∧
    B4TargetV8.Reachable (boundary roles) registry root final ∧
    GeneralNominalSaturationState.Generated final.core.erased.current root terminal ∧
    (∃ m, Models final m) ∧
    (∀ m, Models final m ↔ Models initial m) ∧
    ∀ m, Models final m → (boundary roles).Evidence registry final m root (.node 1 [.node 1 [.node 3 []]]) :=
  ⟨GeneralDepthTwoFirstInstall300.actual,GeneralDepthTwoSecondInstall300.actual,
    actual_terminal.2.1,actual_terminal.2.2,
    ⟨_,GeneralDepthTwoTerminalFrame300.final_model⟩,final_models,root_evidence⟩

end Yulang.GeneralDepthTwoEvidence300
