# Cycle 1 Rust unit記録

既存Y2 Rust testsのみ。Leanのビルドではない。下記の成功コマンド11回、29 test completions（castの1件再実行を含み、unique 28件）。広いordinary_cast_characterizationは別途SIGKILLで中断し、全PASSとはしない。

- `cargo test -p infer pure_function_argument_effect_passes --lib`:3 PASS、exit0、86秒（初回debug build）。
- `cargo test -p infer infer_adapter_preserves_raw_cardinality_for_ocast_a_ambiguous_edge_fixtures --lib`:1 PASS、exit0。
- `cargo test -p infer analysis::tests::ordinary_cast_characterization --lib`:10 PASS、exit0。
- `cargo test -p infer role_input_variance_ --lib`:2 PASS、exit0。
- `cargo test -p infer covariant_where_role_input_drops_supertype_scaffold_from_residual --lib`:1 PASS、exit0。
- `cargo test -p infer if_without_else_discards_then_value_and_returns_unit --lib`:1 PASS、exit0。
- `cargo test -p infer constraints::directed_weight::tests --lib`:6 PASS、exit0。
- `cargo test -p infer computed_fetch_def_does_not_quantify_binding_level_root --lib`:1 PASS、exit0。
- `cargo test -p infer var_to_effect_row_upper_reuses_weighted_residual_for_same_source_across_tails --lib`:1 PASS、exit0。
- `cargo test -p infer parameterized_effect_items_keep_row_tail_residuals_and_payload_invariance --lib`:1 PASS、exit0。
- `cargo test -p infer effect_row_filter_ --lib`:2 PASS、exit0。
- `cargo test -p infer ordinary_cast_characterization --lib`:複数PASS後、repository_std 2件が60秒超の表示を出した後、test processがsignal 9で停止。原因は出力にない。ラッパーはtailの終了0だったためcargo自身の数値終了コードは保存し損ねた。成功と扱わない。

F1以外の小さい成功filtersは各1秒未満（秒単位計測0を含む）。正確なtest内部時間は各出力末尾。

## 環境

`PATH=/workspace/scratch/1d0b4aaa3394/audit-cargo/bin:$PATH`、`CARGO_HOME=/workspace/scratch/1d0b4aaa3394/audit-cargo`、`RUSTUP_HOME=/workspace/scratch/1d0b4aaa3394/audit-rustup`。cwdは別worktree yulang-audit-y2（main d4c8bc8fc）。

## yulang-audit-f1-unit.log

```text
   Compiling proc-macro2 v1.0.103
   Compiling quote v1.0.42
   Compiling unicode-ident v1.0.22
   Compiling autocfg v1.5.0
   Compiling serde_core v1.0.228
   Compiling serde v1.0.228
   Compiling strsim v0.11.1
   Compiling ident_case v1.0.1
   Compiling fnv v1.0.7
   Compiling typenum v1.19.0
   Compiling version_check v0.9.5
   Compiling smallvec v1.15.1
   Compiling void v1.0.2
   Compiling rand_core v0.6.4
   Compiling seq-macro v0.3.6
   Compiling zmij v1.0.21
   Compiling equivalent v1.0.2
   Compiling im v15.1.0
   Compiling num-traits v0.2.19
   Compiling memoffset v0.9.1
   Compiling hashbrown v0.17.0
   Compiling rand_xoshiro v0.6.0
   Compiling unreachable v1.0.0
   Compiling rustc-hash v2.1.2
   Compiling unicode-segmentation v1.13.3
   Compiling copy-range v0.1.1
   Compiling text-size v1.1.1
   Compiling rustc-hash v1.1.0
   Compiling new_debug_unreachable v1.0.6
   Compiling serde_json v1.0.149
   Compiling winnow v0.7.15
   Compiling toml_write v0.1.2
   Compiling hashbrown v0.14.5
   Compiling countme v3.0.1
   Compiling syn v2.0.111
   Compiling bitmaps v2.1.0
   Compiling indexmap v2.14.0
   Compiling text-tree v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/text-tree)
   Compiling qp-trie v0.8.2
   Compiling num-integer v0.1.46
   Compiling sized-chunks v0.6.5
   Compiling list-tree v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/list-tree)
   Compiling itoa v1.0.18
   Compiling either v1.15.0
   Compiling memchr v2.8.0
   Compiling rowan v0.15.17
   Compiling darling_core v0.21.3
   Compiling serde_derive v1.0.228
   Compiling darling_macro v0.21.3
   Compiling darling v0.21.3
   Compiling reborrow-generic-derive v0.1.1
   Compiling reborrow-generic v0.1.2
   Compiling chasa v0.5.0
   Compiling num-bigint v0.4.6
   Compiling toml_datetime v0.6.11
   Compiling serde_spanned v0.6.9
   Compiling bincode v1.3.3
   Compiling toml_edit v0.22.27
   Compiling mono v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/mono)
   Compiling poly v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/poly)
   Compiling toml v0.8.23
   Compiling control-ir v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/control-ir)
   Compiling specialize v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/specialize)
   Compiling parser v0.1.3 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/parser)
   Compiling evidence-vm v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/evidence-vm)
   Compiling sources v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/sources)
   Compiling infer v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/infer)
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 1m 26s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 3 tests
test constraints::tests::case_02::pure_function_argument_effect_passes_to_return_effect ... ok
test constraints::tests::case_02::pure_function_argument_effect_passes_outside_return_stack_marker ... ok
test constraints::tests::case_02::pure_function_argument_effect_passes_through_with_right_side_weights ... ok

test result: ok. 3 passed; 0 failed; 0 ignored; 0 measured; 1390 filtered out; finished in 0.00s

```

## yulang-audit-cast-unit.log

```text
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.11s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 1 test
test analysis::tests::ordinary_cast_characterization::infer_adapter_preserves_raw_cardinality_for_ocast_a_ambiguous_edge_fixtures ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1392 filtered out; finished in 0.01s

```

## audit-test-analysis::tests::ordinary_cast_characterization.log

```text
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.19s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 10 tests
test analysis::tests::ordinary_cast_characterization::duplicated_imported_registry_entry_is_currently_counted_twice ... ok
test analysis::tests::ordinary_cast_characterization::cached_prefix_seed_preserves_cast_table_and_poly_rule_cardinality ... ok
test analysis::tests::ordinary_cast_characterization::cached_prefix_seed_retains_defs_without_changing_schemes ... ok
test analysis::tests::ordinary_cast_characterization::compact_cast_discovery_treats_one_and_two_candidates_as_the_same_present_pair ... ok
test analysis::tests::ordinary_cast_characterization::prefix_seeded_infer_and_poly_classification_match_the_ocast_a_oracle ... ok
test analysis::tests::ordinary_cast_characterization::direct_and_compact_shadow_observations_match_the_ocast_a_oracle ... ok
test analysis::tests::ordinary_cast_characterization::repeated_identical_nominal_subtype_constraint_emits_only_one_current_cast_event ... ok
test analysis::tests::ordinary_cast_characterization::direct_nominal_cast_event_applies_zero_one_or_every_visible_candidate ... ok
test analysis::tests::ordinary_cast_characterization::infer_adapter_preserves_raw_cardinality_for_ocast_a_ambiguous_edge_fixtures ... ok
test analysis::tests::ordinary_cast_characterization::disjoint_looking_same_pair_schemes_are_both_applied_today ... ok

test result: ok. 10 passed; 0 failed; 0 ignored; 0 measured; 1383 filtered out; finished in 0.01s

```

## audit-test-computed_fetch_def_does_not_quantify_binding_level_root.log

```text
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.21s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 1 test
test analysis::tests::case_03::computed_fetch_def_does_not_quantify_binding_level_root ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1392 filtered out; finished in 0.01s

```

## audit-test-covariant_where_role_input_drops_supertype_scaffold_from_residual.log

```text
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.03s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 1 test
test lowering::tests::case_04::covariant_where_role_input_drops_supertype_scaffold_from_residual ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1392 filtered out; finished in 0.28s

```

## audit-test-directed-weights.log

```text
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.25s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 6 tests
test constraints::directed_weight::tests::mixed_projection_does_not_move_single_sided_pop ... ok
test constraints::directed_weight::tests::mixed_projection_moves_existing_left_pure_pop_to_right ... ok
test constraints::directed_weight::tests::same_id_pop_then_take_survives ... ok
test constraints::directed_weight::tests::same_id_take_then_pop_cancels ... ok
test constraints::directed_weight::tests::mixed_projection_moves_pure_pop_to_right ... ok
test constraints::directed_weight::tests::mixed_projection_keeps_remaining_active_push_on_left ... ok

test result: ok. 6 passed; 0 failed; 0 ignored; 0 measured; 1387 filtered out; finished in 0.01s

```

## audit-test-effect_row_filter_.log

```text
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.03s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 2 tests
test constraints::tests::case_02::effect_row_filter_rejects_disallowed_concrete_family ... ok
test constraints::tests::case_02::effect_row_filter_constrains_matching_payloads ... ok

test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 1391 filtered out; finished in 0.00s

```

## audit-test-if-without-else.log

```text
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.18s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 1 test
test lowering::tests::case_03::if_without_else_discards_then_value_and_returns_unit ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1392 filtered out; finished in 0.02s

```

## audit-test-parameterized_effect_items_keep_row_tail_residuals_and_payload_invariance.log

```text
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.03s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 1 test
test constraints::tests::case_01::parameterized_effect_items_keep_row_tail_residuals_and_payload_invariance ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1392 filtered out; finished in 0.00s

```

## audit-test-role_input_variance_.log

```text
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.04s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 2 tests
test lowering::tests::case_04::role_input_variance_records_method_signature_polarities ... ok
test lowering::tests::case_04::role_input_variance_keeps_data_constructor_arguments_invariant ... ok

test result: ok. 2 passed; 0 failed; 0 ignored; 0 measured; 1391 filtered out; finished in 0.01s

```

## audit-test-var_to_effect_row_upper_reuses_weighted_residual_for_same_source_across_tails.log

```text
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.03s
     Running unittests src/lib.rs (target/debug/deps/infer-dfea53230aacf9c4)

running 1 test
test constraints::tests::case_02::var_to_effect_row_upper_reuses_weighted_residual_for_same_source_across_tails ... ok

test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; 1392 filtered out; finished in 0.00s

```

## yulang-audit-cast-characterization.log

```text
warning: ambiguous import visibility: pub(in crate::compact::analysis) or pub(crate)
  --> crates/infer/src/compact/analysis/mod.rs:20:28
   |
20 | pub(crate) use occurrence::normalize_var_substitutions;
   |                            ^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: ambiguous because of multiple glob imports of a name in the same module
note: `normalize_var_substitutions` could refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:5:16
   |
 5 | pub(super) use substitution::*;
   |                ^^^^^^^^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
note: `normalize_var_substitutions` could also refer to the function imported here
  --> crates/infer/src/compact/analysis/occurrence/mod.rs:1:5
   |
 1 | use super::*;
   |     ^^^^^^^^
   = help: consider adding an explicit import of `normalize_var_substitutions` to disambiguate
   = warning: this was previously accepted by the compiler but is being phased out; it will become a hard error in a future release!
   = note: for more information, see issue #149145 <https://github.com/rust-lang/rust/issues/149145>
   = note: `#[warn(ambiguous_import_visibilities)]` (part of `#[warn(future_incompatible)]`) on by default

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
17 |     ProofAttemptKernel, ProofAttemptNonce, ScopedLegacyPublicationQuery,
   |                         ^^^^^^^^^^^^^^^^^
18 |     ScopedPublicationProjectionQuery, StructuralPreparationScope,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `#[warn(unused_imports)]` (part of `#[warn(unused)]`) on by default

warning: unused imports: `CommittedStructuralMutation` and `StructuralMutationIntent`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:24:43
   |
24 | pub(in crate::constraints) use commands::{CommittedStructuralMutation, StructuralMutationIntent};
   |                                           ^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^

warning: unused imports: `ImmutableTypeShapeView` and `ScopedQueryView`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:25:44
   |
25 | pub(in crate::constraints) use read_view::{ImmutableTypeShapeView, ScopedQueryView};
   |                                            ^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^

warning: unused import: `ProofSoakTelemetrySnapshot`
   --> crates/infer/src/constraints/mod.rs:216:27
    |
216 |     ProofSoakEventOrigin, ProofSoakTelemetrySnapshot, capture_proof_soak_test_events,
    |                           ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: use of deprecated method `std::sync::atomic::Atomic::<u64>::fetch_update`: renamed to `try_update` for consistency
   --> crates/infer/src/constraints/proof/mod.rs:217:10
    |
217 |         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |          ^^^^^^^^^^^^
    |
    = note: `#[warn(deprecated)]` on by default
help: replace the use of the deprecated method
    |
217 -         .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
217 +         .try_update(Ordering::Relaxed, Ordering::Relaxed, |next| {
    |

warning: variant `Original` is never constructed
   --> crates/infer/src/constraints/mod.rs:646:5
    |
645 | enum UpperReplayClaimLineage {
    |      ----------------------- variant in this enum
646 |     Original,
    |     ^^^^^^^^
    |
    = note: `UpperReplayClaimLineage` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis
    = note: `#[warn(dead_code)]` (part of `#[warn(unused)]`) on by default

warning: methods `register_claim_parent_clause_links`, `evaluate_projection_inclusion_snapshot_after_commit_for_test`, `recompute_lower_projection_bulk_oracle_record`, `reset_cdm_lower_delta_census`, and `cdm_lower_delta_census` are never used
    --> crates/infer/src/constraints/machine/bounds.rs:1132:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1132 |     fn register_claim_parent_clause_links(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2011 |     pub(in crate::constraints) fn evaluate_projection_inclusion_snapshot_after_commit_for_test(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2752 |     fn recompute_lower_projection_bulk_oracle_record(&mut self, lower_record: BoundRecordId) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2907 |     pub(crate) fn reset_cdm_lower_delta_census(&mut self) {
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2912 |     pub(crate) fn cdm_lower_delta_census(&self) -> CdmLowerDeltaCensus {
     |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: variant `ForeignAttemptRoundState` is never constructed
  --> crates/infer/src/constraints/structural_kernel/access.rs:37:5
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ---------------- variant in this enum
...
37 |     ForeignAttemptRoundState {
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProofAccessError` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: variants `SourceBoundary`, `GeneralizedScheme`, and `GeneralizedWitness` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:31:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:41:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
 46 |     ReplayFiniteMapIndex,
    |     ^^^^^^^^^^^^^^^^^^^^
 47 |     ReplayResultMap,
    |     ^^^^^^^^^^^^^^^
 48 |     ReplayOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 49 |     ReplayParentChunkNodes,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 50 |     ReplayParentChunkEntries(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 51 |     ReplayQualifiedArmResultMap,
 52 |     ReplayQualifiedArmNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 53 |     CanonicalQualifiedRootNodes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 54 |     NonReplayQualifiedParentArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 55 |     NonReplayQualifiedParentResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 56 |     NonReplayQualifiedParentsForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 57 |     ReplayAdmissions,
    |     ^^^^^^^^^^^^^^^^
 58 |     FirstReplayWitnesses,
    |     ^^^^^^^^^^^^^^^^^^^^
 59 |     UpperClaimArena,
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
 77 |     ProjectionFormulaEntryIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 78 |     ProjectionSupportGroups(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 79 |     ProjectionSupportGroupIndex(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 80 |     ProjectionExactLinks(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^
 81 |     ProjectionCanonicalRuns(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 82 |     ProjectionCanonicalRunNodes(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 83 |     ProjectionCanonicalRunEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 84 |     ProjectionValidationActions(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 85 |     ProjectionValidationMembership(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 86 |     ProjectionNormalizedSupportKeys(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 87 |     ProjectionAttributedRoots(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 88 |     ProjectionLowerByConstraint,
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
 91 |     DependentsForPremise(ProofPremise),
    |     ^^^^^^^^^^^^^^^^^^^^
 92 |     BoundVarSlots,
    |     ^^^^^^^^^^^^^
 93 |     BoundLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 94 |     BoundUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^
 95 |     BoundEvidenceLowerEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 96 |     BoundEvidenceUpperEntries(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 97 |     BoundCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 98 |     BoundRecords,
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
102 |     ConstraintRootOrigins(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^
103 |     ConstraintStructuralDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
104 |     ConstraintRowDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
105 |     ConstraintReplayDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
106 |     ConstraintSchemeDerivations(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
107 |     ConstraintSchemeRoutes(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^
108 |     ReplayDropRecords,
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: `infer` (lib test) generated 11 warnings (run `cargo fix --lib -p infer --tests` to apply 5 suggestions)
    Finished `test` profile [unoptimized + debuginfo] target(s) in 0.11s
     Running unittests src/lib.rs (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/debug/deps/infer-dfea53230aacf9c4)

running 25 tests
test analysis::tests::ordinary_cast_characterization::cached_prefix_seed_retains_defs_without_changing_schemes ... ok
test analysis::tests::ordinary_cast_characterization::duplicated_imported_registry_entry_is_currently_counted_twice ... ok
test analysis::tests::ordinary_cast_characterization::compact_cast_discovery_treats_one_and_two_candidates_as_the_same_present_pair ... ok
test analysis::tests::ordinary_cast_characterization::prefix_seeded_infer_and_poly_classification_match_the_ocast_a_oracle ... ok
test analysis::tests::ordinary_cast_characterization::infer_adapter_preserves_raw_cardinality_for_ocast_a_ambiguous_edge_fixtures ... ok
test analysis::tests::ordinary_cast_characterization::cached_prefix_seed_preserves_cast_table_and_poly_rule_cardinality ... ok
test analysis::tests::ordinary_cast_characterization::disjoint_looking_same_pair_schemes_are_both_applied_today ... ok
test analysis::tests::ordinary_cast_characterization::direct_and_compact_shadow_observations_match_the_ocast_a_oracle ... ok
test analysis::tests::ordinary_cast_characterization::direct_nominal_cast_event_applies_zero_one_or_every_visible_candidate ... ok
test analysis::tests::ordinary_cast_characterization::repeated_identical_nominal_subtype_constraint_emits_only_one_current_cast_event ... ok
test lowering::tests::ordinary_cast_characterization::sound_b1e_companion_method_result_keeps_structural_shape_check ... ok
test lowering::tests::ordinary_cast_characterization::missing_boundary_shadow_observation_matches_the_ocast_a_oracle ... ok
test lowering::tests::ordinary_cast_characterization::cprov_i_source_paths_require_complete_origins_and_coherent_ownership ... ok
test lowering::tests::ordinary_cast_characterization::missing_ordinary_cast_function_result_and_struct_field_reject ... ok
test lowering::tests::ordinary_cast_characterization::live_application_cast_diagnostics_follow_zero_one_two_cardinality ... ok
test lowering::tests::ordinary_cast_characterization::sound_field_named_and_nested_activation_leaves_scheme_unknown_function_path_open ... ok
test lowering::tests::ordinary_cast_characterization::missing_cast_explanation_reaches_unannotated_parameter_boolean_condition ... ok
test lowering::tests::ordinary_cast_characterization::source_local_cast_registration_retains_def_without_changing_scheme ... ok
test lowering::tests::ordinary_cast_characterization::sound_a_role_impl_associated_type_result_pins_zero_one_two_and_both_nominal_dispositions ... ok
test lowering::tests::ordinary_cast_characterization::source_local_cast_registries_have_cardinality_parity ... ok
test lowering::tests::ordinary_cast_characterization::source_local_infer_and_poly_classification_match_the_ocast_a_oracle ... ok
test lowering::tests::ordinary_cast_characterization::sound_b1e_companion_method_results_follow_zero_one_two_cast_semantics ... ok
test lowering::tests::ordinary_cast_characterization::sound_field_named_and_nested_follow_zero_one_two_cast_semantics ... ok
test lowering::tests::ordinary_cast_characterization::repository_std_infer_and_poly_classification_are_unique has been running for over 60 seconds
test lowering::tests::ordinary_cast_characterization::repository_std_value_cast_pairs_are_each_unique_in_both_registries has been running for over 60 seconds
error: test failed, to rerun pass `-p infer --lib`

Caused by:
  process didn't exit successfully: `/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/target/debug/deps/infer-dfea53230aacf9c4 ordinary_cast_characterization` (signal: 9, SIGKILL: kill)
```
