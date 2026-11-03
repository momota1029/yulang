# R307 source Apply extraction — frozen handoff r2

Sprint-ID / contract revision and SHA-256: R307 / `tasks/agent-loop/sprints/source-apply-incidence-r307.md`, SHA-256 `983a347b741551dc3f14dea45ce19f424d8bf0710d9d252961de045cb9678c06`.
Assignment-ID / handoff revision: `R307-SOURCE-APPLY-EXTRACTION`, revision 2. Revision 1 remains byte-preserved at `/tmp/yulang-r307-extract/source-apply-extraction-r307-r1.md`, SHA-256 `0a5ebb1bdb835e5c3740a83549d000d057f654cc4627b4bfd5243b850439d586`.
Parent gate / original theorem and scope locator: unchanged source Union → catalogue → original child/result correspondence and R159 application; this packet supplies only the source-owned Apply parent-to-child incidence specified in R307. No theorem, source domain, semantic rule or production authority changed.
Baseline / direct dependency hashes: baseline HEAD `ef1b11a91`; original extractor input SHA `e72138e1982bebe2ca6fe1e867b4cc8d70126524b1946875e05deb8a7cc35c18`; selected existing owner extractor `tools/inline-authentic-extraction/src/bin/original_owner_reify.rs` SHA `4921d14f813e931cb064ecc87d8120734b69d1eedaf48fe0bd36deb014e862e9`; owner Lean `notes/theory/lean/YulangClosure/OriginalSourceOwnerReification.lean` SHA `95d9749ce93ecfc82d6423ba193a261f2725178a7e62cea469b57ae316af3d7e`; R159 `SourceAppAdmissionR159.lean` as supplied by R307 contract SHA `5e948a1f8a3aab66028f885ebf16b6ffeed81999039e8a5a4e9c3caf84464408`; unchanged `Cargo.lock` SHA `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`; unchanged `tools/inline-authentic-extraction/Cargo.toml` SHA `21c64b4a22318a1ae89c346357161812a6ac313b6f0c4999853272cf73e2832b`.
Role / actual worker / session / launch receipt: source implementation; `/root/r307_apply_extractor`; session `01a1873a-a93b-7dc3-a8ce-028a7b543a80`; active task assignment from `/root`, with successful Cargo and CLI receipts below.
Requested model and effort / observed model and effort: `gpt-6-luna` / high; observed model and effort UNKNOWN (runtime metadata unavailable to worker).
Exact leased paths / authors: `tools/inline-authentic-extraction/src/bin/source_signature_r300.rs` (authored by `/root/r307_apply_extractor`) and this handoff file. No other repository file changed. Scratch outputs are under `/tmp/yulang-r307-extract`.
Outcome class: implementation; finite source-native extraction evidence, not proof.

## Behavior and schema

For every `LocalSourceForm::Apply` in each top-level binding's actual `LocalSource`, extraction now verifies the owner is that binding's definition root; verifies the Apply occurrence is owned by the selected HIR and maps back to its exact source key; and follows the actual branded LocalSource child indices for callee and argument. Each ref independently records LocalSource index, HIR occurrence ordinal, interned source-key ID, source-position ordinal, byte range and source form. Native occurrence identity is not conflated with `SourceNodeKey` identity.

The Lean-readable output adds `ApplyNodeRef`, `ApplyOccurrenceRow`, and `applyIncidences : List ApplyOccurrenceRow` under `YulangClosure.SourceSignatureExtractionR300`; JSON adds `apply_incidences`. Existing operation signature definitions and old JSON fields are retained. `rawCallee` always names the direct Apply child. `rawCalleeGroupProjection` is empty when it is not a Group; otherwise it lists each real `Group.inner` target in order, including the terminal child. Thus a projection never replaces the original callee incidence.

The executed owner fixture has exactly 35 source bytes and no trailing newline, matching the prior owner-reification input: `my value = \x -> { (\x -> x) x; x }`. Its row is: owner definition source-key ID 0 and root body index 0; Apply `(index 3, occurrence 3, key 1, range [29,30), form Apply)`; raw callee `(index 4, occurrence 4, key 2, range [19,28), form Group)`; projection `(index 6, occurrence 5, key 4, range [20,27), form Lambda)`; argument `(index 5, occurrence 7, key 3, range [29,30), form Name)`; original Apply source form `MlArgument`. The extractor retains the fixture's `UnsupportedExpression` diagnostic; this row is authentic retained HIR evidence, not a successful solver or semantic judgment.

The nested computed-call fixture `my value f = f() (f())` emits all three actual Apply rows, including the outer application whose raw callee is itself an Apply and whose argument is a Group containing another Apply. The empty-call fixture `my invoke f = f()` emits an Apply and Unit argument with the same source-key ID, source-position ordinal and range `[15,17)`, but distinct occurrence ordinals 2 and 3 and distinct LocalSource indices 1 and 3.

Fixture artifacts and SHA-256 (all in `/tmp/yulang-r307-extract`):
- `owner.yu` `1cb3c052efe4b6b43923b4b92686ae9a103ba6dce5bf7f98e3261a01a23185ad`; `owner.lean` `27fb71cb057980f32c827ddc591cf72846dd646649452f554abf322291ca116d`; `owner.json` `be165e5b49f258ad8b4cd1dbaf106879d83eeedbdf036c78acaa26980acb5a11`.
- `nested.yu` `35c272ccfe6a05f842fcd055a012fe2d012a5be58bc2c46b8f78080484ea9aa7`; `nested.lean` `c4d12693cc0b53f2a16ef43f63091e640ae2a2b3aecb23f584aab07ae2ba7733`; `nested.json` `007205b277fea9178f66aa74be4c63eef74b5998b2f2bfe081573dc780197fae`.
- `empty.yu` `5c6fead2b477408913d6ac4ffef3ca55dd171b06150b5c64ce6fb40a3601c7aa`; `empty.lean` `d52bbe0f26bbba7f4a3a3a0e3b0840d9e97f7845f7ee772666ff55819be69f60`; `empty.json` `f555b9eb996657123b9276727ea608fc2c0eb0e4e7bf08ceb0829f8420c3f614`.

## Parent/source/native correspondence and limits

The Rust execution checks the selected parsed key against the same ShadowArtifact, the binding definition source key against the binding root, each Apply/callee/argument occurrence against the selected HIR, each source key against the selected parse, and each child index against the exact same LocalSource owner. Group traversal follows actual `LocalSourceForm::Group { inner }` references. The finite fixture therefore gives the proof lane actual source-owner data for `OriginalSourceOwnerReification.TableToSource.app`; it does not prove a general Rust-to-Lean correspondence or itself construct/derive the Lean parent relation. No source-to-constraints propagation or execution behavior is claimed by this extraction packet.

Reused: reviewed R300 `Keys::intern` selected-parse/artifact authentication and run-local key interning; R300 direct HIR occurrence ownership style; prior `original_owner_reify.rs` checks for binding-root ownership, exact child indices and retention of raw Group plus projection; R301 finite extraction/JSON/Lean convention and R302 limits against equating extracted syntax with semantic/native admission.
Rejected: unwrapping the callee into a guessed child; keying occurrences by source key/range; emitting an Apply row from source text alone; inferring an EI arm, logical admission, child judgment, or R159 result from syntax/fixture success.

Unresolved premises: this finite emission does not establish general extractor/source equivalence, arbitrary source coverage, typed child/source judgments, independent arms, authentic EI interpretation, q_c registration, original checking/admission or R159 closure. Proof lane must check the row against actual parent and both child occurrences and the unchanged `TableToSource.app` / R159 consumer, rejecting swapped children, dropped Group edges, duplicate source positions conflated as one occurrence, and rows not emitted by the selected source. Existing OriginalCoordinates/CoordinateLaws requirements remain exactly as before.

## Checks, resources and frozen artifacts

Offline locked focused test command:
`CARGO_TARGET_DIR=/tmp/yulang-r307-extract/cargo cargo test --offline --locked --manifest-path tools/inline-authentic-extraction/Cargo.toml --bin source_signature_r300 -j1`
Result: exit 0, 10 passed, 0 failed. This includes prior R300 signature tests plus deterministic extraction, nested computed calls, the exact owner fixture and empty-call identity separation.

Offline locked standalone build:
`CARGO_TARGET_DIR=/tmp/yulang-r307-extract/cargo cargo build --offline --locked --manifest-path tools/inline-authentic-extraction/Cargo.toml --bin source_signature_r300 -j1`
Result: exit 0. CLI emitted JSON and Lean for all three fixtures. JSON parsed with Python's `json` module; rows/data above match. `lake env lean /tmp/yulang-r307-extract/owner.lean` was attempted from `notes/theory/lean` and did not run the Lean checker because the local `.lake/build` lacks `YulangClosure/SourceSignatureRealizationR300.olean`; no dependency build/output was authorized in this assignment. The Lean text is syntactically serialized for the existing imported schema, but this packet does not report a Lean checker pass.

Time: approximately 360s wall elapsed of the fixed 1800s assignment; no budget extension. Cargo emitted existing `yu-hir` dead-code warnings only. Frozen implementation source SHA-256: `ebb1ee47bf5e76f8414dbf0145c96373b8e5a4394885924f6b24e32b0e2649c1`.

Next related step inside envelope: proof lane consumes the frozen owner fixture schema above and constructs/checks the Apply incidence edge; implementation writes are complete. If proof identifies a missing source field, return the exact counterexample and requested field to Luna; this worker does not enlarge the schema lease independently.
Worker state / writes stopped: STOPPED; source edits and scratch generation complete. No descendants or generated repository paths. `/tmp/yulang-r307-extract/cargo` is disposable Cargo target output; the fixture `.yu`, `.lean`, and `.json` files in that same directory are frozen evidence required by the proof lane, not disposable until proof intake.
Commit-ready milestone: pending primary's review/integration; worker did not perform Git operations or self-certify.

## Revision 2 — focused regression additions

Luna requested these regression cases after independent regression execution. The implementation behavior/schema above is unchanged; this revision adds only two tests to the leased extractor file.

- `multiple_group_projection_preserves_each_inner_edge_in_order` uses `my value f = (((f))) x` and asserts the ordered actual projection forms are `Group, Group, Name`, with LocalSource indices `4, 5, 6` and a raw callee separate at index 2.
- `two_definition_owners_can_reuse_local_index_without_sharing_owner` uses `my one f = f(); my two g = g()`. Both actual Applies have LocalSource index 1 and owner body index 0, while definition source-key IDs differ (0 versus 3), as do occurrence ordinals and application source keys.

Revision-2 focused check:
`CARGO_TARGET_DIR=/tmp/yulang-r307-extract/cargo cargo test --offline --locked --manifest-path tools/inline-authentic-extraction/Cargo.toml --bin source_signature_r300 -j1`
Result: exit 0, 12 passed, 0 failed. Captured log `r2-focused-test.log` SHA-256 `344b5f9894aa1360616aa61a58ab5c1c93af57aaac1fd457acbe63ef73acb574`. The prior 10 R1 cases still pass. The R2 fixture JSON/Lean outputs are frozen in `/tmp/yulang-r307-extract`: `multi-group.yu` `e8a46eeb4489e1e68117c361bc8fd2b9a64e3c987da7b5e91f02821614f50ced`; `multi-group.lean` `456b5fbc257c375eddb0807dc66d705097b14da9e5b26cc7f7b9fb149bde2bdb`; `multi-group.json` `2b4ba828f4816a70b456040e940e99e20b6a067203e3ed6e40bedc6de8272612`; `two-owner.yu` `7cc30c1f1bb0886630c7701a69e0c72030f0fa323845616322a9a4653edabe3d`; `two-owner.lean` `4506ff1a766c0f52b7d4140cfbeafbecd8c2ff80f8643f97c6378b0662e73f50`; `two-owner.json` `e56aea65078067cd23f787bce2944db27f9e8ae4d67536df7f5f38f094e7a294`.

Revision-2 extractor source SHA-256: `0f55c2afff3a491585326b34e27d36ba6bf4c750cfb4e62d33fba5f0bcf01f20`. Total time remains within the fixed 1800s assignment budget. Writing stopped after this revision; primary review/integration remains pending.
