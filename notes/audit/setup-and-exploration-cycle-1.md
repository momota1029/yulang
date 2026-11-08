# Cycle 1 setup・探索時の出力

再現batch以外の初期手動確認・toolchain導入・buildログ。stdout/stderrはそのまま保存。ファイル名は保存時の識別名であり、各出力について終了コード・実行時刻・完全なcommandを再構成していない。この節だけから厳密な総CLI呼出数は数えない。再現可能な主要結果はruntime-cycle-1.mdのcommand付きbatchで再実行済み。

初期`cargo build --release -p yulang --offline`はcargo不在exit127、導入後offlineはchasa不在exit101、onlineはexit0。`f1-direct-standard-run`は標準prelude付きrun、exit0・308秒。

## yulang-audit-build-offline.log

```text
error: no matching package named `chasa` found
location searched: crates.io index
required by package `parser v0.1.3 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/parser)`
note: offline mode (via `--offline`) can sometimes cause surprising resolution failures
help: if this error is too confusing you may wish to retry without `--offline`
```

## yulang-audit-build-online.log

```text
    Updating crates.io index
 Downloading crates ...
  Downloaded icu_locale_core v2.1.1
  Downloaded futures-io v0.3.32
  Downloaded futures-channel v0.3.32
  Downloaded icu_normalizer v2.1.1
  Downloaded futures v0.3.32
  Downloaded futures-macro v0.3.32
  Downloaded httparse v1.10.1
  Downloaded async-trait v0.1.89
  Downloaded icu_normalizer_data v2.1.1
  Downloaded icu_properties_data v2.1.2
  Downloaded icu_collections v2.1.1
  Downloaded futures-core v0.3.32
  Downloaded futures-task v0.3.32
  Downloaded futures-util v0.3.32
  Downloaded hashbrown v0.17.0
  Downloaded ident_case v1.0.1
  Downloaded futures-sink v0.3.32
  Downloaded icu_properties v2.1.2
  Downloaded once_cell v1.21.4
  Downloaded icu_provider v2.1.1
  Downloaded hashbrown v0.14.5
  Downloaded scopeguard v1.2.0
  Downloaded smallvec v1.15.1
  Downloaded idna_adapter v1.2.1
  Downloaded itoa v1.0.18
  Downloaded percent-encoding v2.3.2
  Downloaded copy-range v0.1.1
  Downloaded reborrow-generic v0.1.2
  Downloaded new_debug_unreachable v1.0.6
  Downloaded toml_edit v0.22.27
  Downloaded bitflags v1.3.2
  Downloaded tinystr v0.8.2
  Downloaded countme v3.0.1
  Downloaded darling_macro v0.21.3
  Downloaded parking_lot_core v0.9.12
  Downloaded reborrow-generic-derive v0.1.1
  Downloaded seq-macro v0.3.6
  Downloaded serde_repr v0.1.20
  Downloaded serde_spanned v0.6.9
  Downloaded stable_deref_trait v1.2.1
  Downloaded text-size v1.1.1
  Downloaded bitmaps v2.1.0
  Downloaded lock_api v0.4.14
  Downloaded parking_lot v0.12.5
  Downloaded rand_core v0.6.4
  Downloaded cfg-if v1.0.4
  Downloaded strsim v0.11.1
  Downloaded tokio-macros v2.7.0
  Downloaded memoffset v0.9.1
  Downloaded toml_write v0.1.2
  Downloaded equivalent v1.0.2
  Downloaded rustc-hash v2.1.2
  Downloaded rustc-hash v1.1.0
  Downloaded potential_utf v0.1.4
  Downloaded errno v0.3.14
  Downloaded fnv v1.0.7
  Downloaded pin-project-lite v0.2.17
  Downloaded either v1.15.0
  Downloaded qp-trie v0.8.2
  Downloaded idna v1.1.0
  Downloaded litemap v0.8.2
  Downloaded num-traits v0.2.19
  Downloaded serde_core v1.0.228
  Downloaded signal-hook-registry v1.4.8
  Downloaded form_urlencoded v1.2.2
  Downloaded slab v0.4.12
  Downloaded synstructure v0.13.2
  Downloaded toml_datetime v0.6.11
  Downloaded dashmap v5.5.3
  Downloaded displaydoc v0.2.5
  Downloaded pin-project-internal v1.1.12
  Downloaded quote v1.0.42
  Downloaded num-integer v0.1.46
  Downloaded toml v0.8.23
  Downloaded auto_impl v1.3.0
  Downloaded autocfg v1.5.0
  Downloaded bincode v1.3.3
  Downloaded rand_xoshiro v0.6.0
  Downloaded rowan v0.15.17
  Downloaded chasa v0.5.0
  Downloaded socket2 v0.6.3
  Downloaded sized-chunks v0.6.5
  Downloaded darling v0.21.3
  Downloaded proc-macro2 v1.0.103
  Downloaded serde_derive v1.0.228
  Downloaded pin-project v1.1.12
  Downloaded lsp-types v0.94.1
  Downloaded serde v1.0.228
  Downloaded bytes v1.11.1
  Downloaded darling_core v0.21.3
  Downloaded mio v1.2.0
  Downloaded num-bigint v0.4.6
  Downloaded im v15.1.0
  Downloaded indexmap v2.14.0
  Downloaded memchr v2.8.0
  Downloaded tokio-util v0.7.18
  Downloaded serde_json v1.0.149
  Downloaded syn v2.0.111
  Downloaded libc v0.2.183
  Downloaded yoke v0.8.1
  Downloaded tokio v1.52.3
  Downloaded writeable v0.6.3
  Downloaded tower-lsp v0.20.0
  Downloaded unicode-segmentation v1.13.3
  Downloaded tracing-attributes v0.1.31
  Downloaded unicode-ident v1.0.22
  Downloaded void v1.0.2
  Downloaded zerofrom-derive v0.1.6
  Downloaded zmij v1.0.21
  Downloaded tower-layer v0.3.3
  Downloaded tower-lsp-macros v0.9.0
  Downloaded tower-service v0.3.3
  Downloaded unreachable v1.0.0
  Downloaded tracing-core v0.1.36
  Downloaded tracing v0.1.44
  Downloaded zerofrom v0.1.7
  Downloaded zerovec-derive v0.11.2
  Downloaded typenum v1.19.0
  Downloaded version_check v0.9.5
  Downloaded yoke-derive v0.8.1
  Downloaded utf8_iter v1.0.4
  Downloaded zerotrie v0.2.3
  Downloaded zerovec v0.11.5
  Downloaded url v2.5.8
  Downloaded winnow v0.7.15
  Downloaded unicode-width v0.2.2
  Downloaded tower v0.4.13
   Compiling proc-macro2 v1.0.103
   Compiling unicode-ident v1.0.22
   Compiling quote v1.0.42
   Compiling serde_core v1.0.228
   Compiling autocfg v1.5.0
   Compiling serde v1.0.228
   Compiling smallvec v1.15.1
   Compiling stable_deref_trait v1.2.1
   Compiling libc v0.2.183
   Compiling fnv v1.0.7
   Compiling ident_case v1.0.1
   Compiling strsim v0.11.1
   Compiling litemap v0.8.2
   Compiling typenum v1.19.0
   Compiling writeable v0.6.3
   Compiling memchr v2.8.0
   Compiling icu_properties_data v2.1.2
   Compiling num-traits v0.2.19
   Compiling icu_normalizer_data v2.1.1
   Compiling memoffset v0.9.1
   Compiling version_check v0.9.5
   Compiling hashbrown v0.14.5
   Compiling pin-project-lite v0.2.17
   Compiling parking_lot_core v0.9.12
   Compiling zmij v1.0.21
   Compiling im v15.1.0
   Compiling bitmaps v2.1.0
   Compiling syn v2.0.111
   Compiling futures-sink v0.3.32
   Compiling serde_json v1.0.149
   Compiling futures-core v0.3.32
   Compiling rand_core v0.6.4
   Compiling void v1.0.2
   Compiling seq-macro v0.3.6
   Compiling scopeguard v1.2.0
   Compiling cfg-if v1.0.4
   Compiling lock_api v0.4.14
   Compiling rand_xoshiro v0.6.0
   Compiling unreachable v1.0.0
   Compiling num-integer v0.1.46
   Compiling sized-chunks v0.6.5
   Compiling equivalent v1.0.2
   Compiling itoa v1.0.18
   Compiling copy-range v0.1.1
   Compiling new_debug_unreachable v1.0.6
   Compiling countme v3.0.1
   Compiling text-size v1.1.1
   Compiling rustc-hash v1.1.0
   Compiling hashbrown v0.17.0
   Compiling qp-trie v0.8.2
   Compiling errno v0.3.14
   Compiling rowan v0.15.17
   Compiling futures-channel v0.3.32
   Compiling unicode-segmentation v1.13.3
   Compiling slab v0.4.12
   Compiling percent-encoding v2.3.2
   Compiling rustc-hash v2.1.2
   Compiling futures-io v0.3.32
   Compiling winnow v0.7.15
   Compiling toml_write v0.1.2
   Compiling futures-task v0.3.32
   Compiling once_cell v1.21.4
   Compiling either v1.15.0
   Compiling utf8_iter v1.0.4
   Compiling text-tree v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/text-tree)
   Compiling form_urlencoded v1.2.2
   Compiling indexmap v2.14.0
   Compiling signal-hook-registry v1.4.8
   Compiling parking_lot v0.12.5
   Compiling socket2 v0.6.3
   Compiling mio v1.2.0
   Compiling httparse v1.10.1
   Compiling bytes v1.11.1
   Compiling list-tree v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/list-tree)
   Compiling tracing-core v0.1.36
   Compiling bitflags v1.3.2
   Compiling tower-service v0.3.3
   Compiling tower-layer v0.3.3
   Compiling dashmap v5.5.3
   Compiling unicode-width v0.2.2
   Compiling synstructure v0.13.2
   Compiling darling_core v0.21.3
   Compiling serde_derive v1.0.228
   Compiling zerovec-derive v0.11.2
   Compiling displaydoc v0.2.5
   Compiling futures-macro v0.3.32
   Compiling tokio-macros v2.7.0
   Compiling pin-project-internal v1.1.12
   Compiling tracing-attributes v0.1.31
   Compiling zerofrom-derive v0.1.6
   Compiling yoke-derive v0.8.1
   Compiling tokio v1.52.3
   Compiling futures-util v0.3.32
   Compiling serde_repr v0.1.20
   Compiling pin-project v1.1.12
   Compiling auto_impl v1.3.0
   Compiling zerofrom v0.1.7
   Compiling tracing v0.1.44
   Compiling tower-lsp-macros v0.9.0
   Compiling async-trait v0.1.89
   Compiling yoke v0.8.1
   Compiling zerovec v0.11.5
   Compiling zerotrie v0.2.3
   Compiling tinystr v0.8.2
   Compiling darling_macro v0.21.3
   Compiling potential_utf v0.1.4
   Compiling icu_collections v2.1.1
   Compiling icu_locale_core v2.1.1
   Compiling darling v0.21.3
   Compiling reborrow-generic-derive v0.1.1
   Compiling reborrow-generic v0.1.2
   Compiling num-bigint v0.4.6
   Compiling toml_datetime v0.6.11
   Compiling serde_spanned v0.6.9
   Compiling bincode v1.3.3
   Compiling icu_provider v2.1.1
   Compiling toml_edit v0.22.27
   Compiling icu_properties v2.1.2
   Compiling icu_normalizer v2.1.1
   Compiling chasa v0.5.0
   Compiling futures v0.3.32
   Compiling tower v0.4.13
   Compiling mono v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/mono)
   Compiling poly v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/poly)
   Compiling idna_adapter v1.2.1
   Compiling idna v1.1.0
   Compiling toml v0.8.23
   Compiling url v2.5.8
   Compiling lsp-types v0.94.1
   Compiling control-ir v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/control-ir)
   Compiling tokio-util v0.7.18
   Compiling specialize v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/specialize)
   Compiling mono-runtime v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/mono-runtime)
   Compiling parser v0.1.3 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/parser)
   Compiling evidence-vm v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/evidence-vm)
   Compiling sources v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/sources)
   Compiling yulang-editor v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/yulang-editor)
   Compiling tower-lsp v0.20.0
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

warning: unused imports: `CpkPublicationEvaluationRoundState`, `PreparedStructuralMutationHandle`, `ProofAccessError`, `ProofAttemptNonce`, `ScopedPublicationProjectionQuery`, and `StructuralPreparationScope`
  --> crates/infer/src/constraints/structural_kernel/mod.rs:16:5
   |
16 |     CpkPublicationEvaluationRoundState, PreparedStructuralMutationHandle, ProofAccessError,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^  ^^^^^^^^^^^^^^^^
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

warning: methods `scheme_projectable_lowers`, `scheme_projectable_lowers_in_round`, `extend_with_record_dependents`, and `active_projection_record_owner` are never used
    --> crates/infer/src/constraints/mod.rs:1484:19
     |
1478 | impl ConstraintMachine {
     | ---------------------- methods in this implementation
...
1484 |     pub(crate) fn scheme_projectable_lowers(
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^
...
1493 |     pub(crate) fn scheme_projectable_lowers_in_round<'a>(
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2332 |     fn extend_with_record_dependents(&self, records: &mut FxHashSet<BoundRecordId>) {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
2349 |     fn active_projection_record_owner(&self, record: BoundRecordId) -> Option<TypeVar> {
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: method `generalized_projection_lowers` is never used
    --> crates/infer/src/constraints/mod.rs:2674:19
     |
2643 | impl VarBounds {
     | -------------- method in this implementation
...
2674 |     pub(crate) fn generalized_projection_lowers(
     |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: variant `FormulaOnlyRetryable` is never constructed
  --> crates/infer/src/constraints/machine/bounds.rs:81:5
   |
80 | enum ProjectionClauseCommitPolicy {
   |      ---------------------------- variant in this enum
81 |     FormulaOnlyRetryable,
   |     ^^^^^^^^^^^^^^^^^^^^
   |
   = note: `ProjectionClauseCommitPolicy` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: method `register_record_proof_clause_link` is never used
    --> crates/infer/src/constraints/machine/bounds.rs:1328:8
     |
 155 | impl ConstraintMachine {
     | ---------------------- method in this implementation
...
1328 |     fn register_record_proof_clause_link(
     |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: enum `ProofAccessError` is never used
  --> crates/infer/src/constraints/structural_kernel/access.rs:34:33
   |
34 | pub(in crate::constraints) enum ProofAccessError {
   |                                 ^^^^^^^^^^^^^^^^

warning: methods `try_with_structural_preparation_scope` and `with_publication_projection_query` are never used
   --> crates/infer/src/constraints/structural_kernel/access.rs:104:35
    |
 71 | impl ProofAttemptKernel {
    | ----------------------- methods in this implementation
...
104 |     pub(in crate::constraints) fn try_with_structural_preparation_scope<R>(
    |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
259 |     fn with_publication_projection_query<R>(
    |        ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: field `terminal_failure` is never read
   --> crates/infer/src/constraints/structural_kernel/access.rs:475:5
    |
474 | pub(in crate::constraints::structural_kernel) struct ActiveProofAttempt<'attempt> {
    |                                                      ------------------ field in this struct
475 |     terminal_failure: &'attempt RefCell<Option<ProofFailure>>,
    |     ^^^^^^^^^^^^^^^^

warning: associated items `new` and `ensure_active` are never used
   --> crates/infer/src/constraints/structural_kernel/access.rs:481:8
    |
480 | impl<'attempt> ActiveProofAttempt<'attempt> {
    | ------------------------------------------- associated items in this implementation
481 |     fn new(
    |        ^^^
...
495 |     pub(in crate::constraints::structural_kernel) fn ensure_active(
    |                                                      ^^^^^^^^^^^^^

warning: struct `StructuralPreparationScope` is never constructed
   --> crates/infer/src/constraints/structural_kernel/access.rs:519:35
    |
519 | pub(in crate::constraints) struct StructuralPreparationScope<'scope> {
    |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: methods `prepare`, `commit`, `cancel`, and `live_slot_position` are never used
   --> crates/infer/src/constraints/structural_kernel/access.rs:527:35
    |
526 | impl<'scope> StructuralPreparationScope<'scope> {
    | ----------------------------------------------- methods in this implementation
527 |     pub(in crate::constraints) fn prepare(
    |                                   ^^^^^^^
...
545 |     pub(in crate::constraints) fn commit(
    |                                   ^^^^^^
...
557 |     pub(in crate::constraints) fn cancel(
    |                                   ^^^^^^
...
569 |     fn live_slot_position(
    |        ^^^^^^^^^^^^^^^^^^

warning: struct `PreparedStructuralMutationHandle` is never constructed
   --> crates/infer/src/constraints/structural_kernel/access.rs:645:35
    |
645 | pub(in crate::constraints) struct PreparedStructuralMutationHandle<'scope> {
    |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: fields `checked_targets`, `canonical_reads`, and `hits` are never read
   --> crates/infer/src/constraints/structural_kernel/access.rs:666:5
    |
665 | struct ProjectionInvocationState {
    |        ------------------------- fields in this struct
666 |     checked_targets: HashSet<u64>,
    |     ^^^^^^^^^^^^^^^
667 |     canonical_reads: usize,
    |     ^^^^^^^^^^^^^^^
668 |     hits: usize,
    |     ^^^^
    |
    = note: `ProjectionInvocationState` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: fields `memoized_targets`, `canonical_reads`, and `hits` are never read
   --> crates/infer/src/constraints/structural_kernel/access.rs:673:5
    |
672 | struct PublicationInvocationState {
    |        -------------------------- fields in this struct
673 |     memoized_targets: HashSet<u64>,
    |     ^^^^^^^^^^^^^^^^
674 |     canonical_reads: usize,
    |     ^^^^^^^^^^^^^^^
675 |     hits: usize,
    |     ^^^^
    |
    = note: `PublicationInvocationState` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: struct `ScopedPublicationProjectionQuery` is never constructed
   --> crates/infer/src/constraints/structural_kernel/access.rs:693:35
    |
693 | pub(in crate::constraints) struct ScopedPublicationProjectionQuery<'query> {
    |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: field `invocation` is never read
   --> crates/infer/src/constraints/structural_kernel/access.rs:703:5
    |
700 | pub(crate) struct ScopedLegacyProjectionQuery<'query> {
    |                   --------------------------- field in this struct
...
703 |     invocation: ProjectionInvocationState,
    |     ^^^^^^^^^^

warning: field `invocation` is never read
   --> crates/infer/src/constraints/structural_kernel/access.rs:710:5
    |
707 | pub(in crate::constraints) struct ScopedLegacyPublicationQuery<'query> {
    |                                   ---------------------------- field in this struct
...
710 |     invocation: PublicationInvocationState,
    |     ^^^^^^^^^^

warning: methods `view` and `complete` are never used
   --> crates/infer/src/constraints/structural_kernel/access.rs:717:43
    |
716 |           impl $name<'_> {
    |           -------------- methods in this implementation
717 |               pub(in crate::constraints) fn view(&self) -> &ScopedQueryView<'_> {
    |                                             ^^^^
...
721 |               $complete_visibility fn complete<R>(self, value: R) -> QueryCompletion<R> {
    |                                       ^^^^^^^^
...
739 | / query_shell!(
740 | |     ScopedPublicationProjectionQuery,
741 | |     pub(in crate::constraints)
742 | | );
    | |_- in this macro invocation
    |
    = note: this warning originates in the macro `query_shell` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: associated function `try_new` is never used
   --> crates/infer/src/constraints/structural_kernel/access.rs:815:8
    |
814 | impl<'query> ScopedPublicationProjectionQuery<'query> {
    | ----------------------------------------------------- associated function in this implementation
815 |     fn try_new(
    |        ^^^^^^^

warning: method `with_publication_projection_query` is never used
    --> crates/infer/src/constraints/structural_kernel/access.rs:1228:35
     |
1199 | impl ConstraintMachine {
     | ---------------------- method in this implementation
...
1228 |     pub(in crate::constraints) fn with_publication_projection_query<R>(
     |                                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: enum `StructuralMutationIntent` is never used
 --> crates/infer/src/constraints/structural_kernel/commands.rs:6:33
  |
6 | pub(in crate::constraints) enum StructuralMutationIntent {
  |                                 ^^^^^^^^^^^^^^^^^^^^^^^^

warning: enum `CommittedStructuralMutation` is never used
  --> crates/infer/src/constraints/structural_kernel/commands.rs:40:33
   |
40 | pub(in crate::constraints) enum CommittedStructuralMutation {
   |                                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: method `was_changed` is never used
  --> crates/infer/src/constraints/structural_kernel/commands.rs:73:35
   |
72 | impl CommittedStructuralMutation {
   | -------------------------------- method in this implementation
73 |     pub(in crate::constraints) fn was_changed(self) -> bool {
   |                                   ^^^^^^^^^^^

warning: function `publish_shadow` is never used
 --> crates/infer/src/constraints/structural_kernel/families/bounds.rs:3:50
  |
3 | pub(in crate::constraints::structural_kernel) fn publish_shadow(port: BoundsPublishPort<'_>) {
  |                                                  ^^^^^^^^^^^^^^

warning: function `publish_shadow` is never used
 --> crates/infer/src/constraints/structural_kernel/families/constraints.rs:3:50
  |
3 | pub(in crate::constraints::structural_kernel) fn publish_shadow(port: ConstraintsPublishPort<'_>) {
  |                                                  ^^^^^^^^^^^^^^

warning: function `publish_shadow` is never used
 --> crates/infer/src/constraints/structural_kernel/families/identities.rs:3:50
  |
3 | pub(in crate::constraints::structural_kernel) fn publish_shadow(port: IdentitiesPublishPort<'_>) {
  |                                                  ^^^^^^^^^^^^^^

warning: function `publish_shadow` is never used
 --> crates/infer/src/constraints/structural_kernel/families/proof.rs:3:50
  |
3 | pub(in crate::constraints::structural_kernel) fn publish_shadow(port: ProofPublishPort<'_>) {
  |                                                  ^^^^^^^^^^^^^^

warning: function `publish_shadow` is never used
 --> crates/infer/src/constraints/structural_kernel/families/rows.rs:3:50
  |
3 | pub(in crate::constraints::structural_kernel) fn publish_shadow(port: RowsPublishPort<'_>) {
  |                                                  ^^^^^^^^^^^^^^

warning: struct `PreparedMutationSlotId` is never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:32:19
   |
32 | pub(super) struct PreparedMutationSlotId(usize);
   |                   ^^^^^^^^^^^^^^^^^^^^^^

warning: multiple variants are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:39:5
   |
38 | enum PreparedPayload {
   |      --------------- variants in this enum
39 |     AppendProofOccurrence,
   |     ^^^^^^^^^^^^^^^^^^^^^
40 |     AdmitProjectionSupport,
   |     ^^^^^^^^^^^^^^^^^^^^^^
41 |     AdmitProjectionFormulaClause,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
42 |     AdmitProjectionIndex,
   |     ^^^^^^^^^^^^^^^^^^^^
43 |     AdmitOriginalClaim,
   |     ^^^^^^^^^^^^^^^^^^
44 |     DecideDerivedClaim,
   |     ^^^^^^^^^^^^^^^^^^
45 |     MoveUpperClaim,
   |     ^^^^^^^^^^^^^^
46 |     BindReductionClaim,
   |     ^^^^^^^^^^^^^^^^^^
47 |     TransitionLiveCoverage,
   |     ^^^^^^^^^^^^^^^^^^^^^^
48 |     AdmitReplayRelation,
   |     ^^^^^^^^^^^^^^^^^^^
49 |     AdmitReplayQualifiedParents,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
50 |     AdmitQualifiedParents,
   |     ^^^^^^^^^^^^^^^^^^^^^
51 |     AdmitBound,
   |     ^^^^^^^^^^
52 |     PromoteBound,
   |     ^^^^^^^^^^^^
53 |     TombstoneBound,
   |     ^^^^^^^^^^^^^^
54 |     ExtendBoundDerivation,
   |     ^^^^^^^^^^^^^^^^^^^^^
55 |     AdmitConstraint,
   |     ^^^^^^^^^^^^^^^
56 |     ExtendConstraintProof,
   |     ^^^^^^^^^^^^^^^^^^^^^
57 |     UpdateReplayCompleteness,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
58 |     AdmitReplayDrop,
   |     ^^^^^^^^^^^^^^^
59 |     AdmitRowResidual,
   |     ^^^^^^^^^^^^^^^^
60 |     AdmitRowDerivation,
   |     ^^^^^^^^^^^^^^^^^^
61 |     AdmitRowReduction,
   |     ^^^^^^^^^^^^^^^^^
62 |     AdvanceRowReductionMatched,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
63 |     AdvanceRowReductionUnmatched,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
64 |     UpdateRowReductionOwner,
   |     ^^^^^^^^^^^^^^^^^^^^^^^
65 |     AdmitLowerFilter,
   |     ^^^^^^^^^^^^^^^^
66 |     AdmitStructuralIdentity,
   |     ^^^^^^^^^^^^^^^^^^^^^^^
67 |     AdmitSchemeInstantiation,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: `PreparedPayload` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: fields `payload`, `ticket`, and `reserved_operations` are never read
  --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:72:5
   |
71 | pub(in crate::constraints::structural_kernel) struct PreparedStructuralCommand {
   |                                                      ------------------------- fields in this struct
72 |     payload: PreparedPayload,
   |     ^^^^^^^
73 |     ticket: StructuralReservationTicket,
   |     ^^^^^^
74 |     reserved_operations: Vec<ReservedOperation>,
   |     ^^^^^^^^^^^^^^^^^^^
   |
   = note: `PreparedStructuralCommand` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: fields `scope` and `command` are never read
  --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:79:5
   |
78 | struct PreparedStructuralMutation {
   |        -------------------------- fields in this struct
79 |     scope: PreparationScopeNonce,
   |     ^^^^^
80 |     command: PreparedStructuralCommand,
   |     ^^^^^^^
   |
   = note: `PreparedStructuralMutation` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: field `entries` is never read
  --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:85:5
   |
84 | struct PreparedMutationArena {
   |        --------------------- field in this struct
85 |     entries: Vec<Option<PreparedStructuralMutation>>,
   |     ^^^^^^^
   |
   = note: `PreparedMutationArena` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: enum `StructuralMutationDisposition` is never used
  --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:89:6
   |
89 | enum StructuralMutationDisposition {
   |      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: fields `shadow_snapshot`, `reservations`, `prepared`, and `next_scope_nonce` are never read
   --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:97:5
    |
 95 | pub(in crate::constraints::structural_kernel) struct ProofStructuralState {
    |                                                      -------------------- fields in this struct
 96 |     data: StructuralData,
 97 |     shadow_snapshot: u64,
    |     ^^^^^^^^^^^^^^^
 98 |     reservations: StructuralReservationLedger,
    |     ^^^^^^^^^^^^
 99 |     prepared: PreparedMutationArena,
    |     ^^^^^^^^
100 |     next_scope_nonce: u64,
    |     ^^^^^^^^^^^^^^^^
    |
    = note: `ProofStructuralState` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: multiple methods are never used
   --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:113:19
    |
103 | impl ProofStructuralState {
    | ------------------------- methods in this implementation
...
113 |     pub(super) fn next_scope_nonce(&mut self) -> PreparationScopeNonce {
    |                   ^^^^^^^^^^^^^^^^
...
119 |     pub(in crate::constraints::structural_kernel) fn prepare(
    |                                                      ^^^^^^^
...
154 |     fn try_reserve_arena_slot(&mut self) -> Result<(), ProofAccessError> {
    |        ^^^^^^^^^^^^^^^^^^^^^^
...
164 |     pub(in crate::constraints::structural_kernel) fn commit(
    |                                                      ^^^^^^
...
190 |     pub(super) fn cancel_scope_slots_and_release_tickets(
    |                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
...
207 |     pub(super) fn cancel_slot(
    |                   ^^^^^^^^^^^
...
226 |     fn release_prepared(&mut self, prepared: PreparedStructuralMutation) {
    |        ^^^^^^^^^^^^^^^^

warning: struct `InFlightCommitGuard` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:296:8
    |
296 | struct InFlightCommitGuard<'state> {
    |        ^^^^^^^^^^^^^^^^^^^

warning: associated items `take` and `commit` are never used
   --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:302:8
    |
301 | impl<'state> InFlightCommitGuard<'state> {
    | ---------------------------------------- associated items in this implementation
302 |     fn take(
    |        ^^^^
...
323 |     fn commit(
    |        ^^^^^^

warning: function `prepare_payload` is never used
   --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:386:4
    |
386 | fn prepare_payload(intent: StructuralMutationIntent) -> PreparedPayload {
    |    ^^^^^^^^^^^^^^^

warning: function `try_prove_unchanged` is never used
   --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:436:4
    |
436 | fn try_prove_unchanged(payload: &PreparedPayload) -> Option<ExplicitNoOpProof> {
    |    ^^^^^^^^^^^^^^^^^^^

warning: enum `VerifiedPublicationPlan` is never used
   --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:470:6
    |
470 | enum VerifiedPublicationPlan {
    |      ^^^^^^^^^^^^^^^^^^^^^^^

warning: function `verify_changed_publication` is never used
   --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:505:4
    |
505 | fn verify_changed_publication(
    |    ^^^^^^^^^^^^^^^^^^^^^^^^^^

warning: function `publish_verified_plan` is never used
   --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:621:4
    |
621 | fn publish_verified_plan(
    |    ^^^^^^^^^^^^^^^^^^^^^

warning: function `take_verified_operation` is never used
   --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:759:4
    |
759 | fn take_verified_operation<D: ResourceDomainMarker>(
    |    ^^^^^^^^^^^^^^^^^^^^^^^

warning: function `primary_domain` is never used
   --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:775:4
    |
775 | fn primary_domain(payload: &PreparedPayload) -> StructuralResourceDomainKey {
    |    ^^^^^^^^^^^^^^

warning: function `reservation_plan` is never used
   --> crates/infer/src/constraints/structural_kernel/gateway/mod.rs:815:4
    |
815 | fn reservation_plan(payload: &PreparedPayload) -> Result<Vec<ReservationClaim>, ProofAccessError> {
    |    ^^^^^^^^^^^^^^^^

warning: enum `ReservationError` is never used
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:15:17
   |
15 | pub(super) enum ReservationError {
   |                 ^^^^^^^^^^^^^^^^

warning: variants `Origin`, `SourceBoundary`, `GeneralizedScheme`, `GeneralizedWitness`, and `SchemeInstantiation` are never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:30:5
   |
29 | pub(in crate::constraints::structural_kernel) enum IdentityFamily {
   |                                                    -------------- variants in this enum
30 |     Origin,
   |     ^^^^^^
31 |     SourceBoundary,
   |     ^^^^^^^^^^^^^^
32 |     GeneralizedScheme,
   |     ^^^^^^^^^^^^^^^^^
33 |     GeneralizedWitness,
   |     ^^^^^^^^^^^^^^^^^^
34 |     SchemeInstantiation,
   |     ^^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityFamily` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: multiple variants are never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:40:5
    |
 39 | pub(in crate::constraints::structural_kernel) enum StructuralResourceDomainKey {
    |                                                    --------------------------- variants in this enum
 40 |     ProofOccurrences,
    |     ^^^^^^^^^^^^^^^^
 41 |     DependencyOccurrenceResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 42 |     DependencyOccurrencesForResult(ConstraintRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 43 |     ProjectionCarrierOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 44 |     RowDerivationOccurrenceIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 45 |     ReplayFiniteMapArena,
    |     ^^^^^^^^^^^^^^^^^^^^
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
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
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
    |     ^^^^^^^^^^^^^^^
 60 |     UpperClaimIndex,
    |     ^^^^^^^^^^^^^^^
 61 |     OriginalClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^
 62 |     DerivedClaimIndex,
    |     ^^^^^^^^^^^^^^^^^
 63 |     RootClaimProducerIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 64 |     ReductionClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^^
 65 |     ClaimsByUpperRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^
 66 |     ClaimsInUpperRecord(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^
 67 |     LiveCoverageFlat,
    |     ^^^^^^^^^^^^^^^^
 68 |     LiveStatesByCoverageRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 69 |     LiveStatesInCoverageRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
 70 |     ProjectionSupportsByRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
 71 |     ClaimedParentsByLowerRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 72 |     ProjectionRootMemberships,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
 73 |     ProjectionLowerRecordsByRootMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 74 |     ProjectionLowerRecordsInRoot(UpperReplayClaimId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 75 |     ProjectionFormulaByRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
 76 |     ProjectionFormulaEntries(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
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
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
 89 |     ProjectionLowerByReplay,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
 90 |     DependentRecordsByPremiseMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
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
    |     ^^^^^^^^^^^^
 99 |     BoundDerivations(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^
100 |     ConstraintCanonicalIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
101 |     ConstraintRecords,
    |     ^^^^^^^^^^^^^^^^^
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
    |     ^^^^^^^^^^^^^^^^^
109 |     ReplayDropIndex,
    |     ^^^^^^^^^^^^^^^
110 |     RowResidualMap,
    |     ^^^^^^^^^^^^^^
111 |     RowResidualRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
112 |     RowResidualRecords,
    |     ^^^^^^^^^^^^^^^^^^
113 |     RowResidualDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
114 |     RowDerivationArena,
    |     ^^^^^^^^^^^^^^^^^^
115 |     RowDerivationIndex,
    |     ^^^^^^^^^^^^^^^^^^
116 |     RowReductionBySourceMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
117 |     RowReductionsForSource(TypeVar),
    |     ^^^^^^^^^^^^^^^^^^^^^^
118 |     RowReductionOwnerMap,
    |     ^^^^^^^^^^^^^^^^^^^^
119 |     RowReductionOwnersForUpper(BoundRecordId),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
120 |     RowReductionRecords,
    |     ^^^^^^^^^^^^^^^^^^^
121 |     RowProcessedLowers(UnweightedRowReductionRecordId),
    |     ^^^^^^^^^^^^^^^^^^
122 |     LowerFilterMap,
    |     ^^^^^^^^^^^^^^
123 |     LowerFilterRecordIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^
124 |     LowerFilterRecords,
    |     ^^^^^^^^^^^^^^^^^^
125 |     LowerFilterDerivations(u32),
    |     ^^^^^^^^^^^^^^^^^^^^^^
126 |     IdentityRecords(IdentityFamily),
    |     ^^^^^^^^^^^^^^^
    |
    = note: `StructuralResourceDomainKey` has derived impls for the traits `Clone` and `Debug`, but these are intentionally ignored during dead code analysis

warning: associated function `key` is never used
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:141:8
    |
138 | pub(super) trait ResourceDomainMarker: domain_sealed::Sealed {
    |                  -------------------- associated function in this trait
...
141 |     fn key(target: Self::Target) -> StructuralResourceDomainKey;
    |        ^^^

warning: struct `ProofOccurrencesDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:164:5
    |
164 |     ProofOccurrencesDomain => StructuralResourceDomainKey::ProofOccurrences,
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `ProjectionSupportsByRecordDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:165:5
    |
165 |     ProjectionSupportsByRecordDomain => StructuralResourceDomainKey::ProjectionSupportsByRecord,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `ProjectionFormulaByRecordDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:166:5
    |
166 |     ProjectionFormulaByRecordDomain => StructuralResourceDomainKey::ProjectionFormulaByRecordMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `ProjectionLowerByConstraintDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:167:5
    |
167 |     ProjectionLowerByConstraintDomain => StructuralResourceDomainKey::ProjectionLowerByConstraint,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `DependentRecordsByPremiseDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:168:5
    |
168 |     DependentRecordsByPremiseDomain => StructuralResourceDomainKey::DependentRecordsByPremiseMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `UpperClaimArenaDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:169:5
    |
169 |     UpperClaimArenaDomain => StructuralResourceDomainKey::UpperClaimArena,
    |     ^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `ReductionClaimIndexDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:170:5
    |
170 |     ReductionClaimIndexDomain => StructuralResourceDomainKey::ReductionClaimIndex,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `LiveCoverageFlatDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:171:5
    |
171 |     LiveCoverageFlatDomain => StructuralResourceDomainKey::LiveCoverageFlat,
    |     ^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `ReplayFiniteMapArenaDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:172:5
    |
172 |     ReplayFiniteMapArenaDomain => StructuralResourceDomainKey::ReplayFiniteMapArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `ReplayQualifiedArmResultDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:173:5
    |
173 |     ReplayQualifiedArmResultDomain => StructuralResourceDomainKey::ReplayQualifiedArmResultMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `BoundRecordsDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:174:5
    |
174 |     BoundRecordsDomain => StructuralResourceDomainKey::BoundRecords,
    |     ^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `ConstraintRecordsDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:175:5
    |
175 |     ConstraintRecordsDomain => StructuralResourceDomainKey::ConstraintRecords,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `ReplayDropRecordsDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:176:5
    |
176 |     ReplayDropRecordsDomain => StructuralResourceDomainKey::ReplayDropRecords,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `RowResidualRecordsDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:177:5
    |
177 |     RowResidualRecordsDomain => StructuralResourceDomainKey::RowResidualRecords,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `RowDerivationArenaDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:178:5
    |
178 |     RowDerivationArenaDomain => StructuralResourceDomainKey::RowDerivationArena,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `RowReductionRecordsDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:179:5
    |
179 |     RowReductionRecordsDomain => StructuralResourceDomainKey::RowReductionRecords,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `RowReductionOwnerDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:180:5
    |
180 |     RowReductionOwnerDomain => StructuralResourceDomainKey::RowReductionOwnerMap,
    |     ^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `LowerFilterRecordsDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:181:5
    |
181 |     LowerFilterRecordsDomain => StructuralResourceDomainKey::LowerFilterRecords,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `OriginIdentityRecordsDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:182:5
    |
182 |     OriginIdentityRecordsDomain => StructuralResourceDomainKey::IdentityRecords(IdentityFamily::Origin),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `SchemeInstantiationIdentityRecordsDomain` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:183:5
    |
183 |     SchemeInstantiationIdentityRecordsDomain => StructuralResourceDomainKey::IdentityRecords(IdentityFamily::SchemeInstantiation),
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `unit_domain_markers` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: fields `physical_spare`, `outstanding_units`, and `pending_empty_prune` are never read
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:198:16
    |
197 | pub(super) struct ReservationDomainState {
    |                   ---------------------- fields in this struct
198 |     pub(super) physical_spare: usize,
    |                ^^^^^^^^^^^^^^
199 |     pub(super) outstanding_units: usize,
    |                ^^^^^^^^^^^^^^^^^
200 |     pub(super) pending_empty_prune: bool,
    |                ^^^^^^^^^^^^^^^^^^^
    |
    = note: `ReservationDomainState` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: field `claims` is never read
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:205:5
    |
204 | struct ActiveReservationTicket {
    |        ----------------------- field in this struct
205 |     claims: Vec<ReservationClaim>,
    |     ^^^^^^
    |
    = note: `ActiveReservationTicket` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: field `id` is never read
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:210:16
    |
209 | pub(super) struct StructuralReservationTicket {
    |                   --------------------------- field in this struct
210 |     pub(super) id: ReservationTicketId,
    |                ^^
    |
    = note: `StructuralReservationTicket` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: fields `ticket` and `domain` are never read
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:216:5
    |
215 | pub(super) struct ReservedOperation {
    |                   ----------------- fields in this struct
216 |     ticket: ReservationTicketId,
    |     ^^^^^^
217 |     domain: StructuralResourceDomainKey,
    |     ^^^^^^
    |
    = note: `ReservedOperation` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: fields `next_ticket_id`, `domains`, and `active_tickets` are never read
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:229:5
    |
228 | pub(super) struct StructuralReservationLedger {
    |                   --------------------------- fields in this struct
229 |     next_ticket_id: Option<NonZeroU64>,
    |     ^^^^^^^^^^^^^^
230 |     domains: FxHashMap<StructuralResourceDomainKey, ReservationDomainState>,
    |     ^^^^^^^
231 |     active_tickets: FxHashMap<ReservationTicketId, ActiveReservationTicket>,
    |     ^^^^^^^^^^^^^^
    |
    = note: `StructuralReservationLedger` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: methods `reserve`, `take_next_ticket_id`, `release`, and `mark_pending_empty_prune` are never used
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:245:19
    |
244 | impl StructuralReservationLedger {
    | -------------------------------- methods in this implementation
245 |     pub(super) fn reserve(
    |                   ^^^^^^^
...
306 |     fn take_next_ticket_id(&mut self) -> Result<ReservationTicketId, ReservationError> {
    |        ^^^^^^^^^^^^^^^^^^^
...
315 |     pub(super) fn release(&mut self, ticket: StructuralReservationTicket) {
    |                   ^^^^^^^
...
328 |     pub(super) fn mark_pending_empty_prune(&mut self, domain: StructuralResourceDomainKey) {
    |                   ^^^^^^^^^^^^^^^^^^^^^^^^

warning: methods `domain` and `verify` are never used
   --> crates/infer/src/constraints/structural_kernel/gateway/reservation.rs:360:19
    |
359 | impl ReservedOperation {
    | ---------------------- methods in this implementation
360 |     pub(super) fn domain(&self) -> StructuralResourceDomainKey {
    |                   ^^^^^^
...
364 |     pub(super) fn verify<D: ResourceDomainMarker>(
    |                   ^^^^^^

warning: field `shadow_publications` is never read
 --> crates/infer/src/constraints/structural_kernel/gateway/storage.rs:5:5
  |
4 | pub(super) struct ProofRelations {
  |                   -------------- field in this struct
5 |     shadow_publications: u64,
  |     ^^^^^^^^^^^^^^^^^^^
  |
  = note: `ProofRelations` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: field `shadow_publications` is never read
  --> crates/infer/src/constraints/structural_kernel/gateway/storage.rs:10:5
   |
 9 | pub(super) struct BoundRelations {
   |                   -------------- field in this struct
10 |     shadow_publications: u64,
   |     ^^^^^^^^^^^^^^^^^^^
   |
   = note: `BoundRelations` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: field `shadow_publications` is never read
  --> crates/infer/src/constraints/structural_kernel/gateway/storage.rs:15:5
   |
14 | pub(super) struct ConstraintRelations {
   |                   ------------------- field in this struct
15 |     shadow_publications: u64,
   |     ^^^^^^^^^^^^^^^^^^^
   |
   = note: `ConstraintRelations` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: field `shadow_publications` is never read
  --> crates/infer/src/constraints/structural_kernel/gateway/storage.rs:20:5
   |
19 | pub(super) struct RowRelations {
   |                   ------------ field in this struct
20 |     shadow_publications: u64,
   |     ^^^^^^^^^^^^^^^^^^^
   |
   = note: `RowRelations` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: field `shadow_publications` is never read
  --> crates/infer/src/constraints/structural_kernel/gateway/storage.rs:25:5
   |
24 | pub(super) struct IdentityRelations {
   |                   ----------------- field in this struct
25 |     shadow_publications: u64,
   |     ^^^^^^^^^^^^^^^^^^^
   |
   = note: `IdentityRelations` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: fields `proof`, `bounds`, `constraints`, `rows`, and `identities` are never read
  --> crates/infer/src/constraints/structural_kernel/gateway/storage.rs:30:5
   |
29 | pub(in crate::constraints::structural_kernel) struct StructuralData {
   |                                                      -------------- fields in this struct
30 |     proof: ProofRelations,
   |     ^^^^^
31 |     bounds: BoundRelations,
   |     ^^^^^^
32 |     constraints: ConstraintRelations,
   |     ^^^^^^^^^^^
33 |     rows: RowRelations,
   |     ^^^^
34 |     identities: IdentityRelations,
   |     ^^^^^^^^^^
   |
   = note: `StructuralData` has a derived impl for the trait `Debug`, but this is intentionally ignored during dead code analysis

warning: methods `record_proof_shadow`, `record_bounds_shadow`, `record_constraints_shadow`, `record_rows_shadow`, and `record_identities_shadow` are never used
  --> crates/infer/src/constraints/structural_kernel/gateway/storage.rs:38:19
   |
37 | impl StructuralData {
   | ------------------- methods in this implementation
38 |     pub(super) fn record_proof_shadow(&mut self) {
   |                   ^^^^^^^^^^^^^^^^^^^
...
42 |     pub(super) fn record_bounds_shadow(&mut self) {
   |                   ^^^^^^^^^^^^^^^^^^^^
...
46 |     pub(super) fn record_constraints_shadow(&mut self) {
   |                   ^^^^^^^^^^^^^^^^^^^^^^^^^
...
51 |     pub(super) fn record_rows_shadow(&mut self) {
   |                   ^^^^^^^^^^^^^^^^^^
...
55 |     pub(super) fn record_identities_shadow(&mut self) {
   |                   ^^^^^^^^^^^^^^^^^^^^^^^^

warning: enum `ExplicitNoOpProof` is never used
 --> crates/infer/src/constraints/structural_kernel/gateway/unchanged.rs:4:17
  |
4 | pub(super) enum ExplicitNoOpProof {}
  |                 ^^^^^^^^^^^^^^^^^

warning: enum `ProofReservedOperation` is never used
  --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:58:5
   |
58 |     ProofReservedOperation,
   |     ^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `ProofPublishPort` is never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:57:5
   |
57 |     ProofPublishPort,
   |     ^^^^^^^^^^^^^^^^
   |
   = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: multiple associated items are never used
  --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:46:62
   |
33 |           impl<'write> $port<'write> {
   |           -------------------------- associated items in this implementation
...
46 |               pub(in crate::constraints::structural_kernel) fn publish_shadow(self) {
   |                                                                ^^^^^^^^^^^^^^
...
56 | / shadow_port!(
57 | |     ProofPublishPort,
58 | |     ProofReservedOperation,
59 | |     record_proof_shadow,
60 | |     {
61 | |         proof_occurrences => ProofOccurrences(ProofOccurrencesDomain),
   | |         ^^^^^^^^^^^^^^^^^
62 | |         projection_support => ProjectionSupport(ProjectionSupportsByRecordDomain),
   | |         ^^^^^^^^^^^^^^^^^^
63 | |         projection_formula => ProjectionFormula(ProjectionFormulaByRecordDomain),
   | |         ^^^^^^^^^^^^^^^^^^
64 | |         projection_lower => ProjectionLower(ProjectionLowerByConstraintDomain),
   | |         ^^^^^^^^^^^^^^^^
65 | |         dependent_records => DependentRecords(DependentRecordsByPremiseDomain),
   | |         ^^^^^^^^^^^^^^^^^
66 | |         upper_claim => UpperClaim(UpperClaimArenaDomain),
   | |         ^^^^^^^^^^^
67 | |         reduction_claim => ReductionClaim(ReductionClaimIndexDomain),
   | |         ^^^^^^^^^^^^^^^
68 | |         live_coverage => LiveCoverage(LiveCoverageFlatDomain),
   | |         ^^^^^^^^^^^^^
69 | |         replay_finite_map => ReplayFiniteMap(ReplayFiniteMapArenaDomain),
   | |         ^^^^^^^^^^^^^^^^^
70 | |         replay_qualified => ReplayQualified(ReplayQualifiedArmResultDomain),
   | |         ^^^^^^^^^^^^^^^^
71 | |     }
72 | | );
   | |_- in this macro invocation
   |
   = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: enum `BoundsReservedOperation` is never used
  --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:76:5
   |
76 |     BoundsReservedOperation,
   |     ^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `BoundsPublishPort` is never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:75:5
   |
75 |     BoundsPublishPort,
   |     ^^^^^^^^^^^^^^^^^
   |
   = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: associated items `bound_records` and `publish_shadow` are never used
  --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:46:62
   |
33 |           impl<'write> $port<'write> {
   |           -------------------------- associated items in this implementation
...
46 |               pub(in crate::constraints::structural_kernel) fn publish_shadow(self) {
   |                                                                ^^^^^^^^^^^^^^
...
74 | / shadow_port!(
75 | |     BoundsPublishPort,
76 | |     BoundsReservedOperation,
77 | |     record_bounds_shadow,
78 | |     { bound_records => BoundRecords(BoundRecordsDomain) }
   | |       ^^^^^^^^^^^^^
79 | | );
   | |_- in this macro invocation
   |
   = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: enum `ConstraintsReservedOperation` is never used
  --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:83:5
   |
83 |     ConstraintsReservedOperation,
   |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `ConstraintsPublishPort` is never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:82:5
   |
82 |     ConstraintsPublishPort,
   |     ^^^^^^^^^^^^^^^^^^^^^^
   |
   = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: associated items `constraint_records`, `replay_drop`, and `publish_shadow` are never used
  --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:46:62
   |
33 |           impl<'write> $port<'write> {
   |           -------------------------- associated items in this implementation
...
46 |               pub(in crate::constraints::structural_kernel) fn publish_shadow(self) {
   |                                                                ^^^^^^^^^^^^^^
...
81 | / shadow_port!(
82 | |     ConstraintsPublishPort,
83 | |     ConstraintsReservedOperation,
84 | |     record_constraints_shadow,
85 | |     {
86 | |         constraint_records => ConstraintRecords(ConstraintRecordsDomain),
   | |         ^^^^^^^^^^^^^^^^^^
87 | |         replay_drop => ReplayDrop(ReplayDropRecordsDomain),
   | |         ^^^^^^^^^^^
88 | |     }
89 | | );
   | |_- in this macro invocation
   |
   = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: enum `RowsReservedOperation` is never used
  --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:93:5
   |
93 |     RowsReservedOperation,
   |     ^^^^^^^^^^^^^^^^^^^^^
   |
   = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `RowsPublishPort` is never constructed
  --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:92:5
   |
92 |     RowsPublishPort,
   |     ^^^^^^^^^^^^^^^
   |
   = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: associated items `row_residual`, `row_derivation`, `row_reduction`, `row_owner`, `lower_filter`, and `publish_shadow` are never used
   --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:46:62
    |
 33 |           impl<'write> $port<'write> {
    |           -------------------------- associated items in this implementation
...
 46 |               pub(in crate::constraints::structural_kernel) fn publish_shadow(self) {
    |                                                                ^^^^^^^^^^^^^^
...
 91 | / shadow_port!(
 92 | |     RowsPublishPort,
 93 | |     RowsReservedOperation,
 94 | |     record_rows_shadow,
 95 | |     {
 96 | |         row_residual => RowResidual(RowResidualRecordsDomain),
    | |         ^^^^^^^^^^^^
 97 | |         row_derivation => RowDerivation(RowDerivationArenaDomain),
    | |         ^^^^^^^^^^^^^^
 98 | |         row_reduction => RowReduction(RowReductionRecordsDomain),
    | |         ^^^^^^^^^^^^^
 99 | |         row_owner => RowOwner(RowReductionOwnerDomain),
    | |         ^^^^^^^^^
100 | |         lower_filter => LowerFilter(LowerFilterRecordsDomain),
    | |         ^^^^^^^^^^^^
101 | |     }
102 | | );
    | |_- in this macro invocation
    |
    = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: enum `IdentitiesReservedOperation` is never used
   --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:106:5
    |
106 |     IdentitiesReservedOperation,
    |     ^^^^^^^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: struct `IdentitiesPublishPort` is never constructed
   --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:105:5
    |
105 |     IdentitiesPublishPort,
    |     ^^^^^^^^^^^^^^^^^^^^^
    |
    = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: associated items `origin`, `scheme_instantiation`, and `publish_shadow` are never used
   --> crates/infer/src/constraints/structural_kernel/gateway/write_ports.rs:46:62
    |
 33 |           impl<'write> $port<'write> {
    |           -------------------------- associated items in this implementation
...
 46 |               pub(in crate::constraints::structural_kernel) fn publish_shadow(self) {
    |                                                                ^^^^^^^^^^^^^^
...
104 | / shadow_port!(
105 | |     IdentitiesPublishPort,
106 | |     IdentitiesReservedOperation,
107 | |     record_identities_shadow,
108 | |     {
109 | |         origin => Origin(OriginIdentityRecordsDomain),
    | |         ^^^^^^
110 | |         scheme_instantiation => SchemeInstantiation(SchemeInstantiationIdentityRecordsDomain),
    | |         ^^^^^^^^^^^^^^^^^^^^
111 | |     }
112 | | );
    | |_- in this macro invocation
    |
    = note: this warning originates in the macro `shadow_port` (in Nightly builds, run with -Z macro-backtrace for more info)

warning: field `data` is never read
  --> crates/infer/src/constraints/structural_kernel/read_view.rs:61:5
   |
60 | pub(in crate::constraints) struct ScopedQueryView<'query> {
   |                                   --------------- field in this struct
61 |     data: &'query StructuralData,
   |     ^^^^

warning: method `is_empty_shadow` is never used
  --> crates/infer/src/constraints/structural_kernel/read_view.rs:77:35
   |
65 | impl<'query> ScopedQueryView<'query> {
   | ------------------------------------ method in this implementation
...
77 |     pub(in crate::constraints) fn is_empty_shadow(&self) -> bool {
   |                                   ^^^^^^^^^^^^^^^

   Compiling yulang v0.1.0 (/workspace/scratch/1d0b4aaa3394/yulang-audit-y2/crates/yulang)
warning: `infer` (lib) generated 107 warnings (run `cargo fix --lib -p infer` to apply 4 suggestions)
    Finished `release` profile [optimized] target(s) in 1m 31s
```

## yulang-audit-build.log

```text
/bin/bash: line 1: cargo: command not found
```

## yulang-audit-cast-ambiguous-nominal-interpreter.log

```text
run roots [target({left: 1, right: 2})]
```

## yulang-audit-f1-ascribe-noprelude.log

```text
roots d0:ping d2:id d3:lifted d4:used
d0:ping mod {
}
d2:id: 'a -> 'a = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:lifted: int -> int = e2:r1:id->d2:id
d4:used: () -> [ping] int = e8:(fn p1:() -> e7:(e3:r2:lifted->d3:lifted e6:(e4:r3:"ping::get"->d1:"ping.get" e5:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
}
```

## yulang-audit-f1-direct-noprelude.log

```text
roots d0:ping d2:id d3:direct
d0:ping mod {
}
d2:id: 'a -> 'a = e1:(fn p0:d4:x -> e0:r0:x->d4:x)
d3:direct: () -> [ping] int = e7:(fn p1:() -> e6:(e2:r1:id->d2:id e5:(e3:r2:"ping::get"->d1:"ping.get" e4:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:x arg
}
```

## yulang-audit-f1-direct-run-check.log

```text
```

## yulang-audit-f1-direct-run-run.log

```text
```

## yulang-audit-f1-direct-run-runtime.log

```text
run roots [7]
```

## yulang-audit-f1-direct-standard-run.log

```text
run roots [7]
```

## yulang-audit-f1-higher-inferred-run-interpreter.log

```text
run roots [7]
```

## yulang-audit-f1-higher-inferred-run-runtime.log

```text
run roots [7]
```

## yulang-audit-f1-higher-noprelude.log

```text
roots d0:ping d2:id d3:apply d4:higher
d0:ping mod {
}
d2:id: 'a -> 'a = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:apply: (int -> [ping] int) -> int = e7:(fn p1:d6:f -> e6:(e2:r1:f->d6:f e5:(e3:r2:"ping::get"->d1:"ping.get" e4:())))
d4:higher: () -> int = e11:(fn p2:() -> e10:(e8:r3:apply->d3:apply e9:r4:id->d2:id))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:f arg
}
```

## yulang-audit-f1-higher-run-check.log

```text
```

## yulang-audit-f1-higher-run-interpreter.log

```text
conflicting type candidates: [ping] vs []
```

## yulang-audit-f1-higher-run-noprelude.log

```text
roots d0:ping d2:plain d3:higher d4:handle
d0:ping mod {
}
d2:plain: int -> int = e1:(fn p0:d5:x -> e0:r0:x->d5:x)
d3:higher: (int -> [ping] int) -> int = e7:(fn p1:d6:f -> e6:(e2:r1:f->d6:f e5:(e3:r2:"ping::get"->d1:"ping.get" e4:())))
d4:handle: int ['a & [ping; 'a]] -> ['a] int = e14:(fn p2:d7:action -> e13:catch e8:r3:action->d7:action { ping::get p3:_, p4:d8:k -> e11:(e9:r4:k->d8:k e10:7); p5:d9:v -> e12:r5:v->d9:v })
root exprs e19:(e15:r6:handle->d4:handle e18:(e16:r7:higher->d3:higher e17:r8:plain->d2:plain))
runtime roots e19:(e15:r6:handle->d4:handle e18:(e16:r7:higher->d3:higher e17:r8:plain->d2:plain))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d5:x arg
  d6:f arg
  d7:action arg
  d8:k arg
  d9:v arg
}
```

## yulang-audit-f1-higher-run-run.log

```text
conflicting type candidates: [ping] vs []
```

## yulang-audit-f1-higher-run-runtime.log

```text
conflicting type candidates: [ping] vs []
```

## yulang-audit-f1-pipe-noprelude.log

```text
roots d0:ping d2:id d3:piped
d0:ping mod {
}
d2:id: 'a -> 'a = e1:(fn p0:d4:x -> e0:r0:x->d4:x)
d3:piped: () -> [ping] int = e7:(fn p1:() -> e6:(e5:r2:id->d2:id e4:(e2:r1:"ping::get"->d1:"ping.get" e3:())))
detached {
  d1:"ping.get": () -> [ping] int = <missing>
  d4:x arg
}
```

## yulang-audit-f1-pipe-run-check.log

```text
```

## yulang-audit-f1-pipe-run-run.log

```text
```

## yulang-audit-f1-pipe-run-runtime.log

```text
run roots [7]
```

## yulang-audit-pure-control-noprelude.log

```text
roots d0:id d1:pure
d0:id: 'a -> 'a = e1:(fn p0:d2:x -> e0:r0:x->d2:x)
d1:pure: () -> int = e5:(fn p1:() -> e4:(e2:r1:id->d0:id e3:7))
detached {
  d2:x arg
}
```

## yulang-audit-rustup.log

```text
info: downloading installer
info: profile set to minimal
info: default host tuple is x86_64-unknown-linux-gnu
info: syncing channel updates for stable-x86_64-unknown-linux-gnu
info: latest update on 2026-10-15 for version 1.99.1 (58cf8f9c3 2026-10-13)
info: downloading 3 components
info: default toolchain set to stable-x86_64-unknown-linux-gnu

  stable-x86_64-unknown-linux-gnu installed - rustc 1.99.1 (58cf8f9c3 2026-10-13)


Rust is installed now. Great!

To get started you need Cargo's bin directory 
(/workspace/scratch/1d0b4aaa3394/audit-cargo/bin) in your PATH
environment variable. This has not been done automatically.

To configure your current shell, you need to source
the corresponding env file under /workspace/scratch/1d0b4aaa3394/audit-cargo.

Consider running the right command for your shell (note the leading DOT):
. "/workspace/scratch/1d0b4aaa3394/audit-cargo/env" # For sh/ash/dash/pdksh/zsh
cargo:rerun-if-env-changed=CC_x86_64-unknown-linux-gnu
CC_x86_64-unknown-linux-gnu = None
cargo:rerun-if-env-changed=CC_x86_64_unknown_linux_gnu
CC_x86_64_unknown_linux_gnu = None
cargo:rerun-if-env-changed=HOST_CC
HOST_CC = None
cargo:rerun-if-env-changed=CC
CC = None
cargo:rerun-if-env-changed=CC_ENABLE_DEBUG_OUTPUT
cargo:rerun-if-env-changed=CPATH
cargo:rerun-if-env-changed=C_INCLUDE_PATH
cargo:rerun-if-env-changed=CPLUS_INCLUDE_PATH
cargo:rerun-if-env-changed=OBJC_INCLUDE_PATH
cargo:rerun-if-env-changed=OBJCPLUS_INCLUDE_PATH
cargo:rerun-if-env-changed=COMPILER_PATH
cargo:rerun-if-env-changed=SOURCE_DATE_EPOCH
cargo:rerun-if-env-changed=GCC_EXEC_PREFIX
cargo:rerun-if-env-changed=CRATE_CC_NO_DEFAULTS
CRATE_CC_NO_DEFAULTS = None
cargo:rerun-if-env-changed=CFLAGS
CFLAGS = None
cargo:rerun-if-env-changed=HOST_CFLAGS
HOST_CFLAGS = None
cargo:rerun-if-env-changed=CFLAGS_x86_64_unknown_linux_gnu
CFLAGS_x86_64_unknown_linux_gnu = None
cargo:rerun-if-env-changed=CFLAGS_x86_64-unknown-linux-gnu
CFLAGS_x86_64-unknown-linux-gnu = None
```

## 無効なrunner呼出

途中のrunner生成で、辞書ではなく最後のsource文字列からnamesを生成したミスがあった。642回の非存在path呼出は全てexit1。これらはYulang意味論の結果ではない。名前を正しい7モジュールへ修正し、再実行した。raw metadataはローカルnotes/audit/logs/invalid-runner-control.json、出力は/tmp/yulang-audit-invalid-runner/に保持。不要な誤filenameファイルは公開予定成果物には含めない。
