import Yulang.GeneralRebasePackedNonleaf298
import Yulang.GeneralRebaseCompiledEvidenceAt277

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 27000
set_option maxHeartbeats 9800000
namespace Yulang.GeneralRebasePackedNodeCompose298
open GeneralNominalExamples (registry model displayRoot displayChild)
open GeneralDeclarationExamples (roles)
open GeneralNominalVersionedMixedSourceBoundary234 (boundary)
open GeneralNominalVersionedJournal232 (Models State)
open GeneralNominalCommonBridge (Assignment)
open GeneralRebaseCompiledDisplay277 (after)
open GeneralRebasePackedAnswers298 (Vector fill pack)
open GeneralRebasePackedNonleaf298 (footprint)

def complete (v : Vector footprint) (fallback : Assignment) : Assignment :=
  fill footprint v fallback

theorem no_second_raw_step (next : State roles) : ¬ (boundary roles).Step registry displayRoot after next := by
  intro step
  exact GeneralRebaseCompiledStable277.halted next step

theorem child_of_answer (v : Vector footprint) (fallback : Assignment)
    (valid : Models after (complete v fallback)) :
    (boundary roles).Evidence registry after (complete v fallback) displayChild (.node 3 []) :=
  GeneralRebaseCompiledEvidence277.child_evidence _ valid

theorem parent_of_answer (v : Vector footprint) (fallback : Assignment)
    (valid : Models after (complete v fallback)) :
    (boundary roles).Evidence registry after (complete v fallback) displayRoot (.node 1 [.node 3 []]) := by
  apply GeneralRebaseCompiledEvidenceAt277.evidenceAt (complete v fallback) valid displayRoot 1 [displayChild]
    [.node 3 []] (.inl rfl) GeneralRebaseCompiledStable277.stable_parent ?_
    GeneralRebaseCompiledSelection277.picked_parent
  · exact .cons (child_of_answer v fallback valid) .nil
  · intro d found
    cases List.mem_singleton.mp found
    exact GeneralRebaseCompiledStable277.stable_child

theorem supplied_model_composes (fallback : Assignment) :
    let v := pack footprint model
    Models after (complete v fallback) ∧
      (boundary roles).Evidence registry after (complete v fallback) displayChild (.node 3 []) ∧
      (boundary roles).Evidence registry after (complete v fallback) displayRoot (.node 1 [.node 3 []]) := by
  let v := pack footprint model
  have original := (GeneralRebasePackedNonleaf298.joint_exact model (.node 1 [.node 3 []]) (.node 3 [])).mpr
    ⟨(GeneralRebaseDisplayFrame285.final_check _).mp GeneralRebaseCompiledSelection277.after_model,rfl,rfl⟩
  have modelHere : Models after (complete v fallback) :=
    ((GeneralRebasePackedNonleaf298.model_and_tree_packed model fallback _ _).mpr original).1
  exact ⟨modelHere,child_of_answer v fallback modelHere,parent_of_answer v fallback modelHere⟩

end Yulang.GeneralRebasePackedNodeCompose298
