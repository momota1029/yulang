# Frozen source handoff — PROVIDER-LEXICAL-OWNER-20261027/r1

- Assignment: `PROVIDER-LEXICAL-OWNER-20261027-SOURCE`, handoff revision 1.
- Sprint contract: `tasks/agent-loop/sprints/provider-lexical-owner-20261027-r1.md`, SHA-256 `51f03748775a45a486953728762a40507c4950678abe478151d17c72b65c042d`.
- Baseline: `97d5c5d7f8316b29107b1fc4084fd67e696fe265`; branch `yulang3`.
- Parent claim: unchanged universal provider execution/source-publication obligation inside the whole-language inference/executor soundness theorem. This handoff closes no parent gate.
- Worker: `/root/provider_lexical_source`; session `PROVIDER-LEXICAL-OWNER-20261027/r1`; task delivered by `/root` in this session. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN (runtime metadata unavailable to this worker).
- Claim class: executed source evidence, not proof of logical source correspondence or production authority.

## Frozen outputs and direct source evidence

- Adapter: `tools/inline-authentic-extraction/src/bin/original_provider_lexical_owner.rs`, SHA-256 `4ca19da0ec1ed628ff40355416ce612a23ed1c88577be03abdad796a92588a74`.
- Executed generated trace: `notes/theory/lean/YulangClosure/OriginalProviderLexicalOwnerTrace.lean`, SHA-256 `4719fe129bee3a04fc321589d2c765413ec81cf309d7ad88d118c99b49ed57a0`.
- Successful Cargo receipt: `/tmp/yulang-provider-lexical-owner-20261027/source/cargo-02.log`, SHA-256 `c6f85fb0965592802db205b298c474488dbcd87e0cd2c2362d8c3f488cd26ee9`.
- Provider bytes are exactly `pub id x = x\n`, SHA-256 `9b830a0650483a3387ced1724463b5fb18434366fb5a082f8cf7597ca8e7519e`.
- The emitted trace has structured declaration, formal and body-name records, plus explicit declaration→lambda→formal→body-name lexical parent edges. It keeps byte ranges separate from `HirParameterId` ordinal, LocalSource lambda/body indices and HIR occurrence ordinal. No debug `String` is used as row evidence.
- Before writing the trace, the adapter selected one exact public HIR `id` definition with a provider-owned source key and byte range, checked the LocalSource carrier and named group against that `DefinitionRootId`, checked `LocalSourceParameter.id == HirBinding.parameters()[0].id()` as branded IDs, checked the body's resolved parameter equals that same branded ID, checked provider parse ownership for formal/body source keys, and checked the exact `x` byte ranges. It also rejected a separately parsed foreign key and foreign HIR occurrence while retaining the selected body's HIR ownership.
- Both explicit `identity` and implicit prelude `id` resolve to `SourceExportId` equal to the selected provider export. Equality covers module, name, branded source key, range and syntax kind. The generated exposure rows reflect these post-comparison results.
- Owner-path source inspected: `crates/yu-hir/src/module.rs` SHA-256 `6bf92c93fa37f425a7380248c12c50c0d04ea6eb282e76edb6df54e628260646`; `crates/yu-hir/src/module/local_source.rs` SHA-256 `7055975d582dfb198836c2aa659f8b8033c29dff419d522feea4fea4c42523d1`; `crates/yu-hir/src/module/source_exports.rs` SHA-256 `03727fd3918738a48afde7f7a875de60b63b43ac2cc620896a4ed73d8b0a9179`.
- The actual HIR construction in `module.rs` mints each `HirParameterId` under the selected definition root with its formal ordinal, then records that identity with the parameter source key. LocalSource retains the same parameter identity, source key, range and spelling. `SourceExportResolution::identity()` constructs `SourceExportId` from the exact module/name/source/range/kind fields.

## Execution and checks

- Invocation 1: `CARGO_BUILD_JOBS=1 cargo run --locked --manifest-path tools/inline-authentic-extraction/Cargo.toml --bin original_provider_lexical_owner -- /home/momota1029/rust/yulang/notes/theory/lean/YulangClosure/OriginalProviderLexicalOwnerTrace.lean`; failed after dependency compilation on a Rust invalid `\\u00d7` escape. No trace was written.
- Invocation 2: same exact locked command; exit 0, generated the trace above. Stdout records provider SHA, HIR definition `std::core::id#0`, declaration/formal/body ranges, explicit/prelude exact identity match and foreign-owner rejection. Cargo warnings were pre-existing `yu-hir` dead-code warnings.
- Cargo allowance is exhausted at 2/2. `--locked` was present both times; Cargo.lock was not changed by the commands. No tests, Lean checks or formatters were run. Successful call wall time was about 0.39 s; first failed call about 22.06 s. CPU/RSS were not measured; build parallelism was limited with `CARGO_BUILD_JOBS=1`.
- Prior evidence reused: successful r2 provider parse/lower/foreign-owner and exact export checks, and the reviewed twelve-audit result under unchanged dependency bytes. Prior r1 debug-String transcription was rejected as table evidence. Frozen prior adapter/trace were not edited.
- Relevant reused frozen hashes: prior source adapter `original_provider_reify.rs` `39be34a6c0ae2eea673af07dd427e9316f72290687cc937ba2faa13615067729`; helper manifest `Cargo.toml` `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b`; Cargo.lock `2ee467b8f6416aa7dda36f96e3401a0b0ae24a739ff7c6a2efccc1323777ee91`; prior emitted trace `OriginalProviderPublicationCoverageTrace.lean` `9e2578c3e96f95d335263d1c0ed874af36ed411676fbb4977676314a28af56e1`.

## Remaining owner gap and correspondence boundary

- This executed table authenticates provider HIR/LocalSource/CST owner relations. It does not instantiate `OriginalSource.Source`, original logical coordinates, source admission, initializer execution, Return/Shared payloads, replay/map compatibility or exposure equations.
- `OriginalProviderSourceSolution.Occurrences.source` remains a parameterized candidate; its incoming `Context` remains universal. Existing `OriginalSourceOwnerReification` records no caller Context equation. The exact missing input is an owner-derived root `Context` preparation relation tied to this provider source. The source paths inspected here do not establish one; construction feasibility remains unresolved, not refuted.
- The fixture is unannotated (`pub id x = x`), and the emitted formal row records no annotation claim. Any administrative Wild or binding/Name owner translation is a Lean constructor derivation over the emitted lexical graph and remains the proof lane's responsibility.
- Native correspondence is absent from this slice. Source/native correspondence, universal `SourceJudgment`, A/B, effect hygiene, complete Call, inference/executor soundness and production remain OPEN.
- Provisional boundary: only the HIR/LocalSource owner table and exact export joins are established. Falsifiers are a wrong branded owner, foreign source key/occurrence, incomplete parent chain, body resolution to another formal, or any mismatch in the exact public export identity. No cutover is authorized. Luna owns cleanup/disposition.

## Open TODOs, resources, paths and stop

- Proof TODO: consume only the exact trace hash above; map its constructor incidence to distinct logical coordinates; prove `Occurrences.source`, formal Context extension and body lookup while keeping the incoming root Context universally quantified. Report the root-context preparation equation as missing if unavailable.
- Luna TODO: apply the partial result to the unchanged parent claim and retain all open premises; arrange fresh independent review only after both lane artifacts freeze.
- Files written in this assignment: this adapter, this generated trace, this handoff. No other source paths were intentionally written.
- Scratch: `/tmp/yulang-provider-lexical-owner-20261027/source/cargo-02.log`. Cargo's default build target was also created/used at `tools/inline-authentic-extraction/target`, outside the packet's named scratch; do not clean it here. This target tree is known disposable scratch for primary-only hygiene. No other scratch is known.
- STOPPED receipt: all writes by `/root/provider_lexical_source` ended after freezing this handoff; no subprocess or descendant remains active to this worker's knowledge. No active-work runtime accounting beyond observed command wall times is available here.
