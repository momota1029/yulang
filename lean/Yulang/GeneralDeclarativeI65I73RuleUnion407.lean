import Yulang.GeneralDeclarativeI65I72UnifiedGroundedReplay405
import Yulang.GeneralDeclarativeI65I72SupportedSound404

set_option backward.isDefEq.respectTransparency false
namespace Yulang.GeneralDeclarativeI65.I72
open GeneralDeclarativeI65
open GeneralDeclarativeWitnessDeclaredState357 (authoredRegistry)
open CommonRoleOutermostResolver (Summarizes)

/-- The concrete fixed-event families. The index is the complete original
rule (including its local requirements and diagnostics), not an arbitrary
checker or a predicate chosen to make a result provable. -/
inductive FixedEvidenceFamily407 : SourcePrimitives → Prop where
  | variableOnly : FixedEvidenceFamily407 variableSource403
  | repeated : FixedEvidenceFamily407 repeatedSource403
  | whereTree : FixedEvidenceFamily407 variableWhereSource403
  | nativeK2 : FixedEvidenceFamily407 variableWithNativeK2403
  | supported : FixedEvidenceFamily407 supportedVariableSource404
  | supportedK2 : FixedEvidenceFamily407 completedNativePrioritySource404
  | supportedAmbiguity : FixedEvidenceFamily407 completedChoiceSource404
  | authoredNative : FixedEvidenceFamily407 authoredNativeSelectedSource405

/-- Disjunction at each local judgment, not a disjunction of already
classified whole programs. The unchanged C402 trace constructors allow
a different family for every actual ordered child and support producer;
raw root K2 remains independent of all eight families. -/
def R0 : SourcePrimitives where
  elected := fun s q event needs =>
    ∃ R, FixedEvidenceFamily407 R ∧ R.elected s q event needs
  other := fun s q verdict needs =>
    ∃ R, FixedEvidenceFamily407 R ∧ R.other s q verdict needs

/-- Stronger than the original homogeneous S10 letters: the node has
meaning independent of which already verified families prove the
original smaller output dependencies or ordered children. Their real
proof/receipt requirements remain in C402 SourceTrace. -/
def LocalEvidence407 (R : SourcePrimitives) : Prop :=
  ∀ s q (event : Event s q) needs, R.elected s q event needs →
    GeneralNode event ∧ (RetainedVariableOutputs403 event ∨ RetainedTypedValueRows403 event)

private theorem variable_local407 : LocalEvidence407 variableSource403 := by
  intro s q event needs via
  obtain ⟨_,⟨read⟩,fixed⟩ := via
  have checked := read.scope.checked.2 event.frame.decl (List.mem_of_getElem? event.frame.authored)
  refine ⟨node_from_exact_preoutput_head405 event checked (fun _ => emptyCapture403) ?_,.inl fixed⟩
  rw [read.sameHead]
  exact congrArg AuthoredBodyFrame393.input read.sameFrame

private theorem repeated_local407 : LocalEvidence407 repeatedSource403 := by
  intro s q event needs via
  obtain ⟨_,⟨read⟩,fixed⟩ := via
  have checked := read.elected.scope.checked.2 event.frame.decl (List.mem_of_getElem? event.frame.authored)
  refine ⟨node_from_exact_preoutput_head405 event checked (fun _ => emptyCapture403) ?_,.inl fixed⟩
  rw [read.sameHead]
  exact congrArg AuthoredBodyFrame393.input read.sameFrame

private theorem native_priority_local407 : LocalEvidence407 variableWithNativeK2403 := by
  intro s q event needs via
  obtain ⟨_,⟨read⟩,fixed⟩ := via
  have checked := read.elected.scope.checked.2 event.frame.decl (List.mem_of_getElem? event.frame.authored)
  refine ⟨node_from_exact_preoutput_head405 event checked (fun _ => emptyCapture403) ?_,fixed⟩
  rw [read.sameHead]
  exact congrArg AuthoredBodyFrame393.input read.sameFrame

private theorem where_local407 : LocalEvidence407 variableWhereSource403 := by
  intro s q event needs via
  exact native_priority_local407 s q event needs ⟨via.1,via.2.1,.inl via.2.2⟩

private theorem supported_local407 : LocalEvidence407 supportedVariableSource404 := by
  intro s q event needs via
  rcases via with old|fresh
  · exact native_priority_local407 s q event needs old
  · obtain ⟨read⟩ := fresh.1
    exact ⟨supporting_readback_makes_actual_node404 read,fresh.2⟩

private theorem authored_native_local407 : LocalEvidence407 authoredNativeSelectedSource405 := by
  intro s q event needs via
  rcases via with old|native
  · exact supported_local407 s q event needs old
  · obtain ⟨read⟩ := native.2.1
    have checked := read.test.checked.2 event.frame.decl (List.mem_of_getElem? event.frame.authored)
    refine ⟨node_from_exact_preoutput_head405 event checked (fun _ => emptyCapture403) ?_,native.2.2⟩
    rw [read.head]
    exact congrArg AuthoredBodyFrame393.input read.frame

theorem each_fixed_rule_produces_local_evidence407 {R : SourcePrimitives}
    (family : FixedEvidenceFamily407 R) : LocalEvidence407 R := by
  cases family with
  | variableOnly => exact variable_local407
  | repeated => exact repeated_local407
  | whereTree => exact where_local407
  | nativeK2 => exact native_priority_local407
  | supported | supportedK2 | supportedAmbiguity => exact supported_local407
  | authoredNative => exact authored_native_local407

theorem R0_elected_has_local_evidence407 : LocalEvidence407 R0 := by
  intro s q event needs via
  obtain ⟨family,member,actual⟩ := via
  exact each_fixed_rule_produces_local_evidence407 member s q event needs actual

theorem R0_provides_nodes407 : S10 R0 :=
  fun s q event needs _ via _ => (R0_elected_has_local_evidence407 s q event needs via).1

theorem R0_keeps_fixed_rows407 : KeepsFixedOutputs404 R0 :=
  fun s q event needs via => (R0_elected_has_local_evidence407 s q event needs via).2

/-- One canonical original-event ledger for the actual mixed trace,
constructed before choosing a model. The finite source-to-tree lowerer
recurses on the actual mixed children; support proofs stay attached to
the source constructor and retain their original OutputNeed indices. -/
theorem R0_trace_has_one_canonical_ledger407 {s q t e d}
    (trace : SourceTrace R0 s q t e) (summarizes : Summarizes t (.selected d)) :
    ∃ tree : I72.GeneralTree trace d,
      CanonicalReplay tree tree.ledger ∧ LedgerMeaning Addresses tree.ledger ∧
      ∀ m, Fits s m → DictionaryEvidence s m q d := by
  obtain ⟨⟨tree⟩,shape⟩ := (lower_selected_at_exact_trace R0 s (R0_provides_nodes407 s)).tree trace summarizes
  have align : CanonicalReplay tree tree.ledger := ⟨rfl,shape,rfl⟩
  refine ⟨tree,align,typed_replay_keeps_original_addresses _ s q t e d trace tree tree.ledger align,?_⟩
  intro m fit
  have meaning := typed_replay_keeps_same_event_meaning _ s q t e d trace tree tree.ledger m align
    (general_tree_meaning_from_local R0 semantic_node_in_signature s q t e d trace tree m fit)
  exact exact_ledger_evidence405 tree.ledger m meaning
    (fixed_targets_from_own_elected_events405 R0_keeps_fixed_rows407 tree m fit)

/-- The literal C402/I-65 fixed conclusion, for all States, actual
selected classifications of R0, and every fitting Model. -/
theorem dictionary_sound_R0 : DictionarySound R0 := by
  intro s q d chosen m fit
  obtain ⟨t,e,⟨trace⟩,summarizes⟩ := chosen
  obtain ⟨_,_,_,meaning⟩ := R0_trace_has_one_canonical_ledger407 trace summarizes
  exact meaning m fit

end Yulang.GeneralDeclarativeI65.I72
