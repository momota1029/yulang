# Sprint R316 — authenticated operator value owner

Status: OPEN_CONTINUATION evidence checkpoint; parent R149 remains OPEN.
Branch / baseline: `research/simple-sub-intrusion` continued from local checkpoint `614fa5e672bd2577efa52c5eb0f4099fb0626a44`; the R316 source-owner checkpoint and its parent range are pushed.
Authority: unchanged Yulang2 playground samples; unified design §§4.1–4.5, 5.1, stages 4/10; proof companion §§2.16, 4.1–4.5, 7.1–7.5; R308 imported operator use bridge; R315 parser-associated carrier.
Dispatch: serial primary. `next_action_selector` is not callable in the current tool schema; record degraded dispatch. User prohibits subagents. No independent proof or review is claimed.

## Parent outcome and bounded step

The original outcome remains unchanged: Yulang2 playground samples must pass ordinary tests, and implementation plus source/native proofs must close. R315 makes the exact four-use `Display.show` body a source carrier while preserving parser association. The candidate collector still returns `Unavailable` for `LocalSourceForm::InfixOperator` because no authenticated operator value-owner bridge reaches its candidate input.

This sprint establishes a source identity for an imported operator's exact provider declaration and adjacent value body, resolved from the parser-selected `HirOperator` provenance. The identity must retain provider module/revision, declaration and body `SourceNodeKey`s, ranges, spelling and fixity, and fail closed on wrong dependency, stale range, mismatched metadata, ambiguity, non-public/recovered body or local operator provenance. This is an ownership bridge only: it must not infer a candidate scheme, map `+` to `.add`, type the provider body, admit the infix use, select a method, or claim runtime execution.

## Evidence, next seam and falsifiers

R308 already joins imported use provenance to the exact public provider operator declaration and body text. `SourceImportEnvironment::operator_body_for_use` currently returns only `&str`; the exact `SourceOperatorDeclaration` remains private. Candidate collection rejects infix operators at `candidate_source.rs` and cannot consume the provider body as a value root. Expose immutable exact owner receipts from the provider index resolver and the imported-use resolver, and test that both return the same parse-owned declaration/body identity as the existing text lookup.

Falsifiers: owner fields disagree with the selected dependency path/revision or declaration range; body key/range is not owned by the provider parse; two records resolve; a local operator is misreported as imported; recovered/non-public source resolves; or tests show any change in parser/operator semantics. If the provider module's current export index cannot produce a complete identity without a new unauthenticated assumption, stop at that exact obstruction and keep infix admission deferred.

## Exact write leases and budget

- `crates/yu-hir/src/module/source_exports.rs`
- `crates/yu-hir/src/lib.rs` (focused owner receipt tests)
- `tools/inference-playground/src/lib.rs` (pinned dependency integration regression)
- `tasks/agent-loop/current.json`
- this contract and `notes/theory/2026-10-22-r316-authenticated-operator-value-owner.md`

Read-only dependencies: `crates/yu-hir/src/module.rs`, `crates/yu-hir/src/module/local_source.rs`, `crates/yu-solver/src/candidate_source.rs`, R308/R315 evidence, converted design/proof Markdown, and pinned source bytes. Baseline hashes: `source_exports.rs` `636f582535b1eae8ba022d7be6185e8c8c165761d0d232b22a11cc5c152cd56e`; HIR `lib.rs` `54a5cb8d73e4192abe4f66d8677ccfa27c29c94b0123c97632e0640da6bf0004`; playground `lib.rs` `9cab7f082364d8e21901af5b61b1dbb84b04f8f69ae5abcf0c95844cc4c7756c`; read-only `candidate_source.rs` `1127ade5b0c36758b262e27a3a4e8e060b5dacbd05162f240c1b0b21801972a8`.

No subagents or concurrent writers. Solo cap 1800 seconds, no carryover. Run focused HIR and pinned integration checks, sprint static check and `git diff --check`. Preserve a clean worktree and commit/push a coherent research checkpoint when Git/network permit. Stop on the exact cap or authenticated identity ambiguity. R149, source/native proof, A/B, principal type, termination, independent review and production stay OPEN.

## Outcome

`SourceOperatorOwner` now carries exact provider module/revision, declaration/body parse-owned keys and ranges, spelling, syntax fixity, visibility and lazy metadata. `SourceImportEnvironment::operator_owner_for_use` uses the existing imported-use resolver; `SourceExportIndex::operator_owner_for_receipt` exposes the same identity at the provider index. Existing body-text lookup remains backed by the same exact resolver. The pinned regression verifies the imported owner equals the owner from the exact selected provider index, and that its keys are foreign to the consumer parse. Re-parsing the same pinned bytes creates a different parse brand; the first version of the test incorrectly expected keys to transfer across parse products and was corrected to compare against the index that actually minted them.

Checks passed: `cargo test -p yu-hir --lib` (165 passed), `cargo test -p yu-playground --lib` (41 passed), focused private-operator receipt rejection, and focused `pinned_stdlib_role_impl_sources_keep_distinct_module_identities`. The unchanged Types deferred-boundary test ran in the playground suite and remains unchanged. `cargo fmt --all -- --check` was stopped because it produced repository-wide formatting diffs across untouched files; no formatter changes were applied. Candidate collection still rejects `InfixOperator`, and this owner receipt supplies no scheme, typing, selection or execution. Git checkpoint: committed as `33cb23d79` (`Track authenticated operator source owners`) and pushed to `research/simple-sub-intrusion`; worktree was clean after the push.

Next source/candidate seam: make this owner resolvable from the exact LocalSource infix node and connect its provider value body into the candidate application path without manufacturing an ordinary definition, inferring semantics from spelling, or losing the exact consumer occurrence. Parent R149 and all proof/production gates remain OPEN.
