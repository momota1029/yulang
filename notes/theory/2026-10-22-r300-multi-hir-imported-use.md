# R300 — Multi-HIR imported use: construction target

Status: candidate implementation/proof correspondence in progress; no theorem or production closure claimed.

The governing design and proof companion were reread at sprint entry. The hard constraint is to keep one semantic graph and one coherent family of mappings through source identity, capture, FreshUse and publication. A multi-module implementation cannot concatenate HIR ordinals: each occurrence and definition root carries a private artifact brand. The valid construction is a batch-owned ordered set of original HIR artifacts with one batch collection token and dense solver positions.

For a consumer import, `SourceImportEnvironment` retains a `SourceExportResolution`; its `SourceExportId` identifies module, name, parse-owned source key, range and syntax kind. Resolve this against the exact provider HIR using `resolve_source_export_owner`. For a binding, map that export identity to the provider's actual `DefId`/`DefinitionRootId`. The consumer's Name use then becomes the normal pending definition use and receives the normal same-batch root, SCC, and FreshUse path. Unknown or duplicate owner results fail closed. Role declarations remain obligations; this slice does not select implementations.

The current collector has one `Arc<HirModule>`, one borrowed `DefId` endpoint index, and one HIR-specific source validation path. The current candidate preflight rejects all `Imported` names; `emit_candidate_source` likewise rejects them. R300 will change only these seams and the owner-sensitive query routing required by multiple artifacts.

Parent R149 and the general source/native theorem remain open. Focused executable evidence will establish construction behavior only. The exact residual proof obligations after the code slice must be recorded before checkpointing.


## 2026-10-22 implementation checkpoint

The solver now retains the original ordered HIR artifacts in `ConstraintBatch`, `ConstraintStore`, frozen candidate state, and `SolvedModule`. Occurrence and definition-root ownership route through artifact-position indexes, with exact-owner fallback for preserved identities. `CandidateInference::solve_modules` resolves imported binding exports against the supplied HIR set, then sends each imported Name through the ordinary definition-use and FreshUse path in one collection/session. Imported role resolutions still fail preflight when no binding target exists.

The focused test `imported_binding_uses_keep_distinct_hir_artifacts_in_one_freshuse_world` passes. It verifies that the distinct provider and consumer artifacts are observed, a foreign artifact is rejected, the import reaches two retained FreshUse routes, and the instantiated local rows are semantically distinct. The provider fixture has only generalized local rows; it does not prove multi-HIR nonlocal-anchor sharing. The existing one-HIR `structural_bound_scoped_payload_authentic_capture_uses_shared_reconstruction` checks shared borrowed rows separately. A direct imported fixture with both local and nonlocal rows remains open.

`cargo test -p yu-solver --features shadow-apply-candidate` did not complete cleanly: four tests failed (`transferred_member_outputs_have_a_simultaneous_index_peak`, `replay_constructor_lineage_observes_rejected_cross_route_authentication`, `retained_demand_transport_authenticates_distinct_uses_and_rejects_wrong_use_or_root`, and `r235_higher_order_effect_mismatch_source_route`), then an unlabelled test thread overflowed its stack and aborted the process. The three named solver failures were reproducible when individually rerun; attribution to the R300 edits is unresolved. No theorem, R149, source/native, or production gate is closed by this checkpoint.
