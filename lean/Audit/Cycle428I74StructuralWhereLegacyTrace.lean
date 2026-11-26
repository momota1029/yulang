import Yulang.GeneralDeclarativeI65I74StructuralWhereEmbed428
import Yulang.GeneralDeclarativeI65I74StructuralWhereMixedAuditSupport430

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72.StructuralWhereLegacyTrace428
open GeneralDeclarativeI65 StructuralWhere427 StructuralWhere428 StructuralWhereMixedFixture430
open CommonRoleOutermostResolver (Summarizes Tree)

private theorem legacyMap : NamedRuleMap428 RepeatedCenters421.R13 mixedRules :=
  ⟨fun h => Or.inl h,fun h => Or.inl h⟩

private theorem sameParentLocal : mixedRules.elected mixedProblem.state mixedProblem.root parentNode [] :=
  selected_trace_local_witness_has_empty_needs428 actualBoth exact_mixed_trace_has_no_support_or_requested_outputs428

private theorem newLeafStillNoWrites : namedTraceWrites428 newLeafTrace = [] := by
  apply support_free_original_named_trace_encodes_no_writes428
  unfold newLeafTrace
  apply selected_leaf_with_zero_outputs_and_no_where_has_no_support428
  · exact closed_child_no_where427 selectedStruct.source
  · exact selectedStruct.source.noOutputs

private def printedTree :=
  Tree.selected parentNode.frame.decl.id [.selected selectedStruct.source.decl.id [],
    (Check408.nullaryReport legacyDecl).tree]

/-- Take the exact checked old proof returned by the real installed
R13 entry on the actual variable sibling. The old Event is not
reconstructed and survives at ordinal 1 of the very same original
parent. This builds an isolated mixed trace, not the public checker. -/
theorem official_old_trace_is_attached_to_the_exact_literal_sibling428 (m : I72.Model)
    (fit : I72.Fits mixedProblem.state m) :
    ∃ old : Event mixedProblem.state actualLegacy.root,
    ∃ prior : SourceTrace RepeatedCenters421.R13 mixedProblem.state actualLegacy.root
        (Check408.nullaryReport legacyDecl).tree (some old),
    ∃ replay : SourceTrace mixedRules mixedProblem.state actualLegacy.root
        (Check408.nullaryReport legacyDecl).tree (some old),
    ∃ all : SourceTrace mixedRules mixedProblem.state mixedProblem.root printedTree (some parentNode),
      (Check408.nullaryReport legacyDecl).writes = RepeatedCenters421.writes prior ∧
      namedTraceNeeds428 replay = namedTraceNeeds428 prior ∧
      namedTraceWrites428 replay = namedTraceWrites428 prior ∧
      TraceChild428 all 1 actualVariable.child old ∧
      namedTraceWrites428 all = [] ∧
      Summarizes printedTree (.selected (.node 218 [.node 219 [],.node 88 []])) ∧
      DictionaryEvidence mixedProblem.state m mixedProblem.root (.node 218 [.node 219 [],.node 88 []]) := by
  have ok := existing_current_dispatch_uses_the_actual_legacy_named_sibling428
  obtain ⟨returned,prior,summary,writes⟩ :=
    (RepeatedCenters421.check_sound actualLegacy (Check408.nullaryReport legacyDecl) throughCurrentPreR14 ok).1
  obtain ⟨actualOld,same⟩ := named_trace_with_selected_tree_returns_actual_event428 prior
  subst returned
  let replay := mapNamedTrace428 legacyMap prior
  have exactOldWrites : namedTraceWrites428 replay.val = [] :=
    replay.property.1.trans ((named_writes_are_the_current_R13_writes428 prior).trans writes.symm)
  have lengthTwo : parentNode.frame.decl.requirements.length = 2 := by decide +kernel
  let all := assembleActualMixedSiblings428 parentNode actualRecord actualVariable lengthTwo
    (rootPick.safe mixedProblem.state.b6) sameParentLocal newLeafTrace replay.val
  have entered : TraceChild428 all 1 actualVariable.child actualOld :=
    actual_parent_second_selected_is_the_supplied_existing_event428
      parentNode actualRecord actualVariable lengthTwo (rootPick.safe mixedProblem.state.b6)
      sameParentLocal newLeafTrace replay.val
  have exactWrite : namedTraceWrites428 all = [] := by
    change namedTraceWrites428 (assembleActualMixedSiblings428 parentNode actualRecord actualVariable lengthTwo
      (rootPick.safe mixedProblem.state.b6) sameParentLocal newLeafTrace replay.val) = _
    rw [assembled_mixed_named_trace_exact_writes428,
      event_with_no_original_outputs_encodes_no_writes428 parentNode rfl,
      newLeafStillNoWrites,exactOldWrites]
    rfl
  have wanted : Summarizes printedTree (.selected (.node 218 [.node 219 [],.node 88 []])) := by
    have actualKey : parentNode.frame.decl.id = 218 := by decide +kernel
    have childKey : selectedStruct.source.decl.id = 219 := by decide +kernel
    unfold printedTree
    rw [actualKey,childKey]
    exact .selected (.cons (.selected .nil (.selected rfl)) (.cons summary .nil)) (.selected rfl)
  have oldMeaning : DictionaryEvidence mixedProblem.state m actualVariable.child (.node 88 []) :=
    actual_named_trace_same_model_dictionary428 current_R13_local_law_for_mixed_named_traces428 prior m fit _ summary
  have structuralMeaning : DictionaryEvidence mixedProblem.state m actualRecord.child (.node 219 []) := by
    have d := original_compound_child_has_positive_same_model_dictionary427 (atlas:=mixedProblem.state.b6) selectedStruct.source m fit
    have actualKey : selectedStruct.source.decl.id = 219 := by decide +kernel
    rw [actualKey] at d
    exact d
  have meaning : DictionaryEvidence mixedProblem.state m mixedProblem.root (.node 218 [.node 219 [],.node 88 []]) := by
    have atParent := no_output_ordinary_event_same_model_semantics428 frame rootPick.head rfl m fit
    have key : parentNode.frame.decl.id = 218 := by decide +kernel
    rw [← key]
    refine .node parentNode atParent.1 atParent.2 ?_
    change DictionaryEvidenceForest mixedProblem.state m (frameWhereKids400 frame) [.node 219 [],.node 88 []]
    rw [literal_mixed_where_order_has_original_distinct_children428 actualRecord actualVariable lengthTwo]
    exact .cons structuralMeaning (.cons oldMeaning .nil)
  exact ⟨actualOld,prior,replay.val,all,writes,replay.property.2,replay.property.1,entered,exactWrite,
    wanted,meaning⟩

#print axioms mapNamedTrace428
#print axioms actual_parent_second_selected_is_the_supplied_existing_event428
#print axioms support_free_original_named_trace_encodes_no_writes428
#print axioms assembled_mixed_named_trace_exact_writes428
#print axioms official_old_trace_is_attached_to_the_exact_literal_sibling428

end Yulang.GeneralDeclarativeI65.I72.StructuralWhereLegacyTrace428
