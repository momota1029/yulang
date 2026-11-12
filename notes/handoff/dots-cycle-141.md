# Cycle141: actual reobservation Evidence and guarded nonempty journals

Started 2026-11-12T12:27:19Z; deadline 13:22:19Z. Fresh integration
`e2daf8ed21c76eaef6dd30a18636b3cc7b0d26d3`; standing orders and I-25 reread.
Previous140 completed and writer released. Latest inbox recheck unchanged.
Start heartbeat was about 5.7 minutes late; no overlapping writer was started.

## Results and exact scope

Eight declarations extend cycle140's packet-free Evidence result to Astra's
new actual point-descriptor replacement Step. The proof inducts directly over
that extended relation rather than assuming old SourceFormed. At an actual
reachable state with packets=[], root/generated focus and actual selected,
Joint follows; actual Stable forces terminal children and gives Evidence in
every final journal model. No fixed-view, Joint or ContextComplete premise is
added. The concrete repaired fork uses an actual point replacement and its
explicit satisfiable final model; it remains an empty-journal example.

Twenty-two additional declarations prove Current for initial traces that may
install nonempty journals, then refresh or perform Certified point revisions.
The explicit guard is computed-report equality at recorded occurrences only.
It is not an assumed Instance, Evidence or Joint. Ordinary steps retain their
existing Extension restriction; actual refresh steps may change views. Actual
Certified revisions provide exact journal-model transport. Recorded packets
then yield parent Evidence from children in the SAME final model, preserving
the exact key and ordered child payloads. A selected recorded occurrence is
proved to match the stored key and ordered children.

A nonempty actual install -> descriptor-addition refresh has an explicit final
model and Current/Instance proof. It does not build Evidence for its rejected
child. The separate actual point-replacement example has EMPTY journal, so its
report guard is vacuous. No nonempty replacement example is claimed.

## Remaining obligations

This is soundness/invariant work toward item5, not general V5 completion.
Selected-to-recorded coverage, child Evidence construction, arbitrary feedback
report preservation, and a nonempty point-replacement positive example remain.
The general evidenceNode field is NOT discharged. Astra's Progress-dependent
executor is not an unconditional progress/termination theorem. The concrete
boundary still has only six unconditional V5 laws; execution/halted/treeExecution
are conditional on Progress, and Remaining fields (whereAccessible,
canonicalLocalOrder, evidenceNode, generatedChildren) remain unsupplied.
The prior unrestricted confluence obstruction is not resolved by a repaired
finite fork. No language semantics, target or Astra-owned definitions changed.

## Verification and publication

Focused build: 714 jobs PASS. Audit/Cycle141.lean (8) and
Audit/Cycle141Recorded.lean (22), --trust=0: PASS; only standard propext,
Classical.choice, Quot.sound. Independent read-only review of both groups PASS.
Diff gate --no-build PASS after committing; the first precommit gate correctly
failed on uncommitted/untracked source, then passed. Full repository build and
frozen Audit.lean were not rerun. Audit.lean and README.md remain untouched.
First source checkpoint `48afb92f3bff793c554b04da022a20ed594ca1d6` published and
six changed-content files read back byte-for-byte. Final source/report/heartbeat
are published together after this report, only to work/dots-main.

## Audited declarations (30)

- `Yulang.GeneralDictionaryReobservationEvidence.trace_packetFree_shape`
- `Yulang.GeneralDictionaryReobservationEvidence.reachable_packetFree_shape`
- `Yulang.GeneralDictionaryReobservationEvidence.reachable_packetFree_joint`
- `Yulang.GeneralDictionaryReobservationEvidence.reachable_packetFree_terminal`
- `Yulang.GeneralDictionaryReobservationEvidence.reachable_packetFree_evidence`
- `Yulang.GeneralDictionaryReobservationEvidence.nonterminal_has_packet`
- `Yulang.GeneralDictionaryReobservationEvidenceExamples.repaired_evidence`
- `Yulang.GeneralDictionaryReobservationEvidenceExamples.actual_repair_with_evidence`
- `Yulang.GeneralDictionaryRecordedObservationTrace.step_feedback`
- `Yulang.GeneralDictionaryRecordedObservationTrace.trace_feedback`
- `Yulang.GeneralDictionaryRecordedObservationTrace.refresh_current`
- `Yulang.GeneralDictionaryRecordedObservationTrace.step_current`
- `Yulang.GeneralDictionaryRecordedObservationTrace.trace_current`
- `Yulang.GeneralDictionaryRecordedObservationTrace.initial_trace_current`
- `Yulang.GeneralDictionaryRecordedObservationTrace.recorded_selected`
- `Yulang.GeneralDictionaryRecordedObservationTrace.recorded_node`
- `Yulang.GeneralDictionaryRecordedRevisionTrace.result_eq`
- `Yulang.GeneralDictionaryRecordedRevisionTrace.revision_current`
- `Yulang.GeneralDictionaryRecordedRevisionTrace.step_reobservation`
- `Yulang.GeneralDictionaryRecordedRevisionTrace.trace_reobservation`
- `Yulang.GeneralDictionaryRecordedRevisionTrace.step_current`
- `Yulang.GeneralDictionaryRecordedRevisionTrace.trace_current`
- `Yulang.GeneralDictionaryRecordedRevisionTrace.initial_trace_current`
- `Yulang.GeneralDictionaryRecordedRevisionTrace.recorded_node`
- `Yulang.GeneralDictionaryRecordedObservationExamples.Nonempty.recorded_reports`
- `Yulang.GeneralDictionaryRecordedObservationExamples.Nonempty.actual_path`
- `Yulang.GeneralDictionaryRecordedObservationExamples.Nonempty.nonempty_current`
- `Yulang.GeneralDictionaryRecordedObservationExamples.Nonempty.modeled_current_parent`
- `Yulang.GeneralDictionaryRecordedObservationExamples.PointReplacement.recorded_reports`
- `Yulang.GeneralDictionaryRecordedObservationExamples.PointReplacement.actual_guarded_repair`
