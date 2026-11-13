# Cycle165 公開定理の索引

各定理の全量化・前提・結論は `lean/Audit/Cycle165PublicTypes.lean` と最終再実行ログの同名出力に保持している。日本語の意味・証明の側・未完の境界は `notes/handoff/dots-cycle-165.md` を参照。ここで名前だけを見て前提を省略しない。

## Yulang.GeneralDictionaryIdentityCurrentEvidence

- `Yulang.GeneralDictionaryIdentityCurrentEvidence.rebase_outputs`
- `Yulang.GeneralDictionaryIdentityCurrentEvidence.rebase_holds`
- `Yulang.GeneralDictionaryIdentityCurrentEvidence.recorded_current_instance`
- `Yulang.GeneralDictionaryIdentityCurrentEvidence.recorded_current_evidence`

## Yulang.GeneralDictionaryIdentityEvidenceExample

- `Yulang.GeneralDictionaryIdentityEvidenceExample.formed`
- `Yulang.GeneralDictionaryIdentityEvidenceExample.current_model`
- `Yulang.GeneralDictionaryIdentityEvidenceExample.current_evidence`
- `Yulang.GeneralDictionaryIdentityEvidenceExample.nonvacuous_current_evidence`

## Yulang.GeneralDictionaryIdentityRefreshExample

- `Yulang.GeneralDictionaryIdentityRefreshExample.refreshed_raw`
- `Yulang.GeneralDictionaryIdentityRefreshExample.old_unknown`
- `Yulang.GeneralDictionaryIdentityRefreshExample.new_known`
- `Yulang.GeneralDictionaryIdentityRefreshExample.refresh_step`
- `Yulang.GeneralDictionaryIdentityRefreshExample.refreshed_formed`
- `Yulang.GeneralDictionaryIdentityRefreshExample.refreshed_models`
- `Yulang.GeneralDictionaryIdentityRefreshExample.refreshed_evidence`
- `Yulang.GeneralDictionaryIdentityRefreshExample.nonvacuous_refreshed_evidence`
- `Yulang.GeneralDictionaryIdentityRefreshExample.not_ordinary_extension`

## Yulang.GeneralDictionarySharedCapturedGuards

- `Yulang.GeneralDictionarySharedCapturedGuards.located`
- `Yulang.GeneralDictionarySharedCapturedGuards.prepared`
- `Yulang.GeneralDictionarySharedCapturedGuards.root_ready`
- `Yulang.GeneralDictionarySharedCapturedGuards.survivor`
- `Yulang.GeneralDictionarySharedCapturedGuards.inherited`
- `Yulang.GeneralDictionarySharedCapturedGuards.usable`
- `Yulang.GeneralDictionarySharedCapturedGuards.generation`
- `Yulang.GeneralDictionarySharedCapturedGuards.input_schema`
- `Yulang.GeneralDictionarySharedCapturedGuards.coherent`

## Yulang.GeneralDictionarySharedCapturedInputReady

- `Yulang.GeneralDictionarySharedCapturedInputReady.old_guard`
- `Yulang.GeneralDictionarySharedCapturedInputReady.facts`
- `Yulang.GeneralDictionarySharedCapturedInputReady.input_trusted`
- `Yulang.GeneralDictionarySharedCapturedInputReady.refreshed_trusted`
- `Yulang.GeneralDictionarySharedCapturedInputReady.input_endpoint_equation`
- `Yulang.GeneralDictionarySharedCapturedInputReady.lo_ready`
- `Yulang.GeneralDictionarySharedCapturedInputReady.hi_ready`

## Yulang.GeneralDictionarySharedCapturedInstallable

- `Yulang.GeneralDictionarySharedCapturedInstallable.p_only`
- `Yulang.GeneralDictionarySharedCapturedInstallable.selected_old`
- `Yulang.GeneralDictionarySharedCapturedInstallable.enabled`
- `Yulang.GeneralDictionarySharedCapturedInstallable.reads_exact`
- `Yulang.GeneralDictionarySharedCapturedInstallable.decisions`

## Yulang.GeneralDictionarySharedCapturedInstallation

- `Yulang.GeneralDictionarySharedCapturedInstallation.children`
- `Yulang.GeneralDictionarySharedCapturedInstallation.guard`
- `Yulang.GeneralDictionarySharedCapturedInstallation.step`
- `Yulang.GeneralDictionarySharedCapturedInstallation.formed`
- `Yulang.GeneralDictionarySharedCapturedInstallation.inhabited`
- `Yulang.GeneralDictionarySharedCapturedInstallation.children_generated`
- `Yulang.GeneralDictionarySharedCapturedInstallation.captured_still_unknown`
- `Yulang.GeneralDictionarySharedCapturedInstallation.consumer_pending`
- `Yulang.GeneralDictionarySharedCapturedInstallation.producer_inputs`
- `Yulang.GeneralDictionarySharedCapturedInstallation.producer_still_unknown`
- `Yulang.GeneralDictionarySharedCapturedInstallation.producer_pending`
- `Yulang.GeneralDictionarySharedCapturedInstallation.revision_producer_pending`
- `Yulang.GeneralDictionarySharedCapturedInstallation.producer_shape`
- `Yulang.GeneralDictionarySharedCapturedInstallation.output_capture_equivalent`
- `Yulang.GeneralDictionarySharedCapturedInstallation.reached_parent`

## Yulang.GeneralDictionarySharedCapturedModel

- `Yulang.GeneralDictionarySharedCapturedModel.lo_fresh`
- `Yulang.GeneralDictionarySharedCapturedModel.hi_fresh`
- `Yulang.GeneralDictionarySharedCapturedModel.target_ne_lo`
- `Yulang.GeneralDictionarySharedCapturedModel.target_ne_hi`
- `Yulang.GeneralDictionarySharedCapturedModel.model_old`
- `Yulang.GeneralDictionarySharedCapturedModel.model_lo`
- `Yulang.GeneralDictionarySharedCapturedModel.model_hi`
- `Yulang.GeneralDictionarySharedCapturedModel.model_target`
- `Yulang.GeneralDictionarySharedCapturedModel.source_models`
- `Yulang.GeneralDictionarySharedCapturedModel.report_exact`
- `Yulang.GeneralDictionarySharedCapturedModel.canonical`
- `Yulang.GeneralDictionarySharedCapturedModel.schema_exact`
- `Yulang.GeneralDictionarySharedCapturedModel.mid_seen`
- `Yulang.GeneralDictionarySharedCapturedModel.captured_seen`
- `Yulang.GeneralDictionarySharedCapturedModel.mid_same`
- `Yulang.GeneralDictionarySharedCapturedModel.captured_same`
- `Yulang.GeneralDictionarySharedCapturedModel.private_models`
- `Yulang.GeneralDictionarySharedCapturedModel.projections`
- `Yulang.GeneralDictionarySharedCapturedModel.lo_seen`
- `Yulang.GeneralDictionarySharedCapturedModel.hi_seen`
- `Yulang.GeneralDictionarySharedCapturedModel.use_values`
- `Yulang.GeneralDictionarySharedCapturedModel.outputs`
- `Yulang.GeneralDictionarySharedCapturedModel.branch_models`

## Yulang.GeneralDictionarySharedCapturedProducer

- `Yulang.GeneralDictionarySharedCapturedProducer.queries`
- `Yulang.GeneralDictionarySharedCapturedProducer.bounds`
- `Yulang.GeneralDictionarySharedCapturedProducer.report_exact`
- `Yulang.GeneralDictionarySharedCapturedProducer.schema_exact`
- `Yulang.GeneralDictionarySharedCapturedProducer.candidate_bindings`
- `Yulang.GeneralDictionarySharedCapturedProducer.allocated_value`
- `Yulang.GeneralDictionarySharedCapturedProducer.private_models`
- `Yulang.GeneralDictionarySharedCapturedProducer.projections`
- `Yulang.GeneralDictionarySharedCapturedProducer.materialized`
- `Yulang.GeneralDictionarySharedCapturedProducer.branch_models`
- `Yulang.GeneralDictionarySharedCapturedProducer.output_int`
- `Yulang.GeneralDictionarySharedCapturedProducer.captured_int`

## Yulang.GeneralDictionarySharedCapturedRefresh

- `Yulang.GeneralDictionarySharedCapturedRefresh.endpoint_equation`
- `Yulang.GeneralDictionarySharedCapturedRefresh.lo_ne_hi`
- `Yulang.GeneralDictionarySharedCapturedRefresh.identifiers_injective`
- `Yulang.GeneralDictionarySharedCapturedRefresh.source_embed`
- `Yulang.GeneralDictionarySharedCapturedRefresh.lo_supported`
- `Yulang.GeneralDictionarySharedCapturedRefresh.hi_supported`
- `Yulang.GeneralDictionarySharedCapturedRefresh.lo_known`
- `Yulang.GeneralDictionarySharedCapturedRefresh.hi_known`
- `Yulang.GeneralDictionarySharedCapturedRefresh.step`
- `Yulang.GeneralDictionarySharedCapturedRefresh.formed`
- `Yulang.GeneralDictionarySharedCapturedRefresh.models_exact`
- `Yulang.GeneralDictionarySharedCapturedRefresh.inhabited`
- `Yulang.GeneralDictionarySharedCapturedRefresh.producer_ready`
- `Yulang.GeneralDictionarySharedCapturedRefresh.captured_unknown`
- `Yulang.GeneralDictionarySharedCapturedRefresh.consumer_pending`
- `Yulang.GeneralDictionarySharedCapturedRefresh.shared_prefix`

## Yulang.GeneralDictionarySharedMetadata

- `Yulang.GeneralDictionarySharedMetadata.formed_metadata`
- `Yulang.GeneralDictionarySharedMetadata.locate_point`
- `Yulang.GeneralDictionarySharedMetadata.identity_current_evidence`

## Yulang.GeneralDictionarySharedOrdinaryHistory

- `Yulang.GeneralDictionarySharedOrdinaryHistory.source_formed`
- `Yulang.GeneralDictionarySharedOrdinaryHistory.recorded_growth`
- `Yulang.GeneralDictionarySharedOrdinaryHistory.install_extension`
- `Yulang.GeneralDictionarySharedOrdinaryHistory.installed`
- `Yulang.GeneralDictionarySharedOrdinaryHistory.current_evidence`

## Yulang.GeneralDictionarySharedSourceRetention

- `Yulang.GeneralDictionarySharedSourceRetention.retains_refl`
- `Yulang.GeneralDictionarySharedSourceRetention.retains_trans`
- `Yulang.GeneralDictionarySharedSourceRetention.step_retains`
- `Yulang.GeneralDictionarySharedSourceRetention.recorded_sources`
- `Yulang.GeneralDictionarySharedSourceRetention.identity_current_evidence`

