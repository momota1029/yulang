# Cycle176 module guide
I-30 exact target is G=`GeneralNominalCenteredGroundBoundary.groundBoundary roles`.
General EvidenceNode and B4 completion remain open. Exact elaborated signatures
are in `notes/verification/cycle176/types-expanded.log.txt`; entries below name
all explicit public declarations in the currently complete modules.

All quantified roles/registries/states/models are arbitrary unless their
signatures specialize the regression fixture. Soundness results never imply
that an actual unrestricted executor trace belongs to a restricted history.

## GeneralDictionaryCenteredCandidate176
Source: `lean/Yulang/GeneralDictionaryCenteredCandidate176.lean`.

`Candidate`, `selected_candidate`, `reachable_candidate`

## GeneralDictionaryCenteredFlexible176
Source: `lean/Yulang/GeneralDictionaryCenteredFlexible176.lean`.

`At`, `Step`, `at_actual`, `step_actual`, `steps_actual`, `step_models`, `at_instance`, `RecordedCurrent`, `step_recorded`, `initial_recorded`, `trace_recorded`, `initial_trace_recorded`, `initial_trace_instance`, `initial_trace_evidence`

## GeneralDictionaryCenteredFootprint176
Source: `lean/Yulang/GeneralDictionaryCenteredFootprint176.lean`.

`RecordedFootprints`, `At`, `Step`, `at_actual`, `step_actual`, `steps_actual`, `flexible_step`, `flexible_steps`, `refresh_instance`, `step_recorded`, `trace_recorded`, `initial_trace_recorded`, `initial_trace_evidence`

## GeneralDictionaryCenteredInhabited176
Source: `lean/Yulang/GeneralDictionaryCenteredInhabited176.lean`.

`OutputsAligned`, `MergeAligned`, `aligned_output_atoms`, `aligned_merge_models`, `at_inhabited`, `AlignedStep`, `step_actual`, `step_inhabited`, `trace_actual`, `trace_inhabited`

## GeneralDictionaryCenteredLedger176
Source: `lean/Yulang/GeneralDictionaryCenteredLedger176.lean`.

`ExactLedger`, `exact_at`, `exact_trace`, `initial_exact`, `reachable_exact`, `packet_member`, `packet_has_plan`, `plan_instance`, `plan_evidence`

## GeneralDictionaryCenteredReady176
Source: `lean/Yulang/GeneralDictionaryCenteredReady176.lean`.

`stable_committed`, `stable_instance`, `selected_instance`, `selected_evidence`, `ModeledSelectedInstallable`, `evidenceNode_of_modeledSelectedInstallable`

## GeneralDictionaryCenteredRecorded176
Source: `lean/Yulang/GeneralDictionaryCenteredRecorded176.lean`.

`Recorded`, `recorded_at`, `recorded_trace`, `initial_recorded`, `reachable_recorded`, `recorded_committed`, `stored_instance`, `reachable_stored_instance`, `stored_evidence`, `current_instance`

## GeneralDictionaryCenteredRegression176
Source: `lean/Yulang/GeneralDictionaryCenteredRegression176.lean`.

`first_flexible`, `parent_current_instance`, `exact_ledger`, `selected_candidate_not_installable`, `premerge_not_stable`

## GeneralDictionaryCenteredSharedMerge176
Source: `lean/Yulang/GeneralDictionaryCenteredSharedMerge176.lean`.

`same_named_inputs`, `recovered_observed`, `named_merge_guard`, `stable_named_alias`

## GeneralDictionaryCenteredTree176
Source: `lean/Yulang/GeneralDictionaryCenteredTree176.lean`.

`current_evidence`, `initial_trace_evidence`, `initial_trace_certificate`

## GeneralDictionaryHeadFootprintRegression176
Source: `lean/Yulang/GeneralDictionaryHeadFootprintRegression176.lean`.

`agrees`, `finished`, `view_changes`, `model_nonempty`, `refinement`, `report_preserved`, `scalar_not_nominal_only`

## GeneralDictionaryViewFootprint176
Source: `lean/Yulang/GeneralDictionaryViewFootprint176.lean`.

`HeadObservation`, `HeadObservation`, `HeadObservation`, `report_finished`, `instance_refinement`

## Verification interpretation

The named nominal-only/fixed-view, finite head-footprint and output-aligned
restrictions are implementation proof fragments, not new language rejection
rules. No completeness or principality theorem is added. Source soundness
uses the SAME final model for every node, and finite trees use existing
RecordedTree syntax rather than an Evidence predicate as a guard.

## Final explicit declaration inventory

This expanded list includes qualified HeadObservation methods omitted from the
compact first inventory. Compiler-generated/private declarations are covered
by the module-based final axiom gate, not by this human-facing list.

### GeneralDictionaryCenteredCandidate176
`Candidate`, `selected_candidate`, `reachable_candidate`

### GeneralDictionaryCenteredFlexible176
`At`, `Step`, `at_actual`, `step_actual`, `steps_actual`, `step_models`, `at_instance`, `RecordedCurrent`, `step_recorded`, `initial_recorded`, `trace_recorded`, `initial_trace_recorded`, `initial_trace_instance`, `initial_trace_evidence`

### GeneralDictionaryCenteredFootprint176
`RecordedFootprints`, `At`, `Step`, `at_actual`, `step_actual`, `steps_actual`, `flexible_step`, `flexible_steps`, `refresh_instance`, `step_recorded`, `trace_recorded`, `initial_trace_recorded`, `initial_trace_evidence`

### GeneralDictionaryCenteredInhabited176
`OutputsAligned`, `MergeAligned`, `aligned_output_atoms`, `aligned_merge_models`, `at_inhabited`, `AlignedStep`, `step_actual`, `step_inhabited`, `trace_actual`, `trace_inhabited`

### GeneralDictionaryCenteredLedger176
`ExactLedger`, `exact_at`, `exact_trace`, `initial_exact`, `reachable_exact`, `packet_member`, `packet_has_plan`, `plan_instance`, `plan_evidence`

### GeneralDictionaryCenteredNonvacuous176
`Step`, `revision_trace`, `aligned_trace`, `actual_trace`, `initial_dictionary_nonvacuous`

### GeneralDictionaryCenteredReady176
`stable_committed`, `stable_instance`, `selected_instance`, `selected_evidence`, `ModeledSelectedInstallable`, `evidenceNode_of_modeledSelectedInstallable`

### GeneralDictionaryCenteredRecorded176
`Recorded`, `recorded_at`, `recorded_trace`, `initial_recorded`, `reachable_recorded`, `recorded_committed`, `stored_instance`, `reachable_stored_instance`, `stored_evidence`, `current_instance`

### GeneralDictionaryCenteredRegression176
`first_flexible`, `parent_current_instance`, `exact_ledger`, `selected_candidate_not_installable`, `premerge_not_stable`

### GeneralDictionaryCenteredRevision176
`RecordedFootprints`, `At`, `Step`, `at_actual`, `step_actual`, `steps_actual`, `footprint_step`, `footprint_steps`, `revision_instance`, `step_recorded`, `trace_recorded`, `initial_trace_recorded`, `initial_trace_evidence`

### GeneralDictionaryCenteredSharedMerge176
`same_named_inputs`, `recovered_observed`, `named_merge_guard`, `stable_named_alias`

### GeneralDictionaryCenteredTree176
`current_evidence`, `initial_trace_evidence`, `initial_trace_certificate`

### GeneralDictionaryHeadFootprintRegression176
`state`, `context`, `next`, `query`, `bounds`, `agrees`, `finished`, `view_changes`, `model_nonempty`, `refinement`, `report_preserved`, `scalar_not_nominal_only`

### GeneralDictionaryViewFootprint176
`HeadObservation`, `HeadObservation.view`, `HeadObservation.observation`, `report_finished`, `instance_refinement`
