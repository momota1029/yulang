import Yulang.GeneralDeclarativeI65I74StructuralWhereBodyReplay428
import Yulang.GeneralDeclarativeI65I74StructuralWhereReplayAuditSupport430

set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereBodyReplay428
open GeneralDeclarativeI65 StructuralWhere427 StructuralWhere428 StructuralWhereMixedFixture430

theorem actual_body_reader_uses_both_exact_original_requests428 :
    reconstructed.first.child.occurrence = [71,0] ∧
      reconstructed.first.name = 4 ∧
      reconstructed.structural.source.decl.id = 219 ∧
      reconstructed.second.actual.child.occurrence = [71,1] ∧
      (frame.names.input reconstructed.second.actual.binder).center = 3 ∧
      reconstructed.namedDecl.id = 88 := by decide +kernel

theorem actual_body_reader_gets_one_fitting_model_dictionary_forest428 :
    DictionaryEvidenceForest mixedProblem.state fitModel (frameWhereKids400 frame)
      [.node 219 [], .node 88 []] := by
  have fit := mixed_body_reader_has_one_exact_model_forest428
    (data:=reconstructed) (Option.eq_some_of_isSome body_replay_works_on_the_original_checked_frame428)
    fitModel genuine_mixed_problem_has_one_model428
  rw [actual_body_reader_uses_both_exact_original_requests428.2.2.1,
    actual_body_reader_uses_both_exact_original_requests428.2.2.2.2.2] at fit
  exact fit

theorem actual_body_reader_never_uses_wrong_structural_or_legacy_source428 :
    (readActualMixedBody428 (s:=mixedProblem.state) frame checked_parent_syntax428
      {actualWire with originalRecordRow := 1}).isNone = true ∧
    (readActualMixedBody428 (s:=mixedProblem.state) frame checked_parent_syntax428
      {actualWire with structuralChild := ⟨2,placedEsc⟩}).isNone = true ∧
    (readActualMixedBody428 (s:=mixedProblem.state) frame checked_parent_syntax428
      {actualWire with bareNameChild := ⟨0,oldWire.levels⟩}).isNone = true ∧
    (readOriginalVariable428 frame 0).isNone = true := by decide +kernel

#print axioms mixed_body_reader_uses_the_exact_original_children428
#print axioms mixed_body_reader_gets_official_legacy_classification428
#print axioms mixed_body_reader_has_one_exact_model_forest428
#print axioms actual_body_reader_uses_both_exact_original_requests428
#print axioms actual_body_reader_never_uses_wrong_structural_or_legacy_source428
#print axioms actual_body_reader_gets_one_fitting_model_dictionary_forest428

end Yulang.GeneralDeclarativeI65.I72.StructuralWhereBodyReplay428
