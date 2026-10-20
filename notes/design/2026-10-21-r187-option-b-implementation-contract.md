# R187 Option B braced conditional sequence contract

Revision: 9, sequential path delta review pending. Rev8 malformed braced-else delta was CLEAN and the terminal-separator repair received CLEAN static review. Rev9 proposes one Web dropdown option after source inspection found the selector options are hard-coded.

Sprint contract: `tasks/agent-loop/sprints/post-lambda-age-and-option-b-sequences-20261021-r187.md`, SHA-256 `9942192386814b59e1026a877cb4fd888eff68dcd211b68d367730deee154de2` (candidate revision 9).
Baseline: `d314168e12e2e5138c7d45f84767f5e6eb39edbc`, branch `research/simple-sub-intrusion`. Design inspection used only the 51 committed source blobs and the cited frozen R147/R184/R186 design evidence. Dirty worktree versions and external Yulang2 worktrees were not read.

## Outcome and boundary

Implement the unchanged fixture's currently missing braced `if` body path, from parser through execution, as an ordered expression sequence. Each source item is retained once and evaluated left to right; intermediate values are discarded; the last value is returned. Every item's computation effects remain represented. A selected item may suspend and resume; continuation state must resume at the next item without repeating or skipping work. Braced `if` without `else` still executes the selected body and produces Unit. Existing colon, inline, and indented forms retain their behavior. The pinned Web fixture must remain byte-identical and continue to produce `countdown_result -> 8`.

This concrete slice covers the fixture's `if flag { 8 } else { countdown true }` route plus multi-item braced-body regressions. It does not claim all R147 Option B behavior: record literals, fields, spreads, record access, record formatting, and mixed record/non-record bodies remain OPEN/deferred. Do not reinterpret record syntax as a sequence. The fixture's identity examples are part of the unchanged end-to-end regression, not evidence that record behavior is implemented.

All original inference A/B claims, quantifiers and source/native correspondence remain OPEN. The R187 proof lane is independent. This contract closes no theorem or production gate.

## Baseline observations and exact owner obligations

At the pinned baseline, `LocalSourceForm::If` stores one body index per arm; `Builder::conditional` accepts only `OperatorChain` or `IndentedStatementBlock`. The target fixture's braced arms therefore lack a retained-source route. The runtime has `Instruction::If` / `Frame::Condition`, but no ordered expression-sequence instruction/frame. The primitive certificate explicitly covers every constructed definition, arm and dependency, including unused code (`runtime/primitive.rs`); adding a sequence must extend coverage to every retained sequence child and may never certify only the selected runtime arm.

The following exact source owners are already within the R187 51-blob manifest. Any owner outside the manifest or any dirty excluded path needed for implementation blocks activation until a sequential exact-path revision and fresh review:

- Parser/CST/recovery: `yu-syntax` conditional and expression-list owners in the R187 manifest. Preserve brace/arm boundary ownership, lexical item order and recovery; malformed input must not publish executable partial sequences.
- HIR/source identity: `yu-hir/src/module/local_source.rs`, `module.rs`, `lib.rs`, `source_identity.rs`. Add a dedicated conditional sequence representation with a parent occurrence and ordered direct child indices; every child keeps a unique source key, occurrence and range. Do not alias parent and child identity. Preserve current single-body, indented-body, and no-else representation.
- Inference: `yu-solver/src/candidate_value_graph.rs` and `candidate_source.rs`. Traverse each child once in source order; link sequence value to the final child's value; retain every child's effect and normal checking. Keep condition/body slots and occurrences distinct. For no-else, check/evaluate the body and retain its effects while the conditional result stays Unit. Preserve existing scheduling, rollback, and source-owner behavior.
- Runtime: `runtime/program.rs`, `machine.rs`, `continuation.rs`, `receiving.rs`, and `primitive.rs`. Lower ordered children plus a final-value rule. The sequence frame must preserve its next-child position and environment across operation handling, continuation capture, resume and replay. No completed child is repeated; no suffix child is skipped. Extend primitive certification over all retained definitions, every arm including unselected arms, every dependency and every sequence child. If any retained object is not covered, decline certification.
- Public regression route: `web/playground/src/main.ts`, `smoke-test.mjs`, the rev9 proposed `web/playground/index.html` selector option, plus the newly leased focused CLI test at `tools/inference-playground/tests/cli_ordinary_islands.rs`. Exercise the unchanged fixture through the existing route and assert `countdown_result -> 8`. Add focused multi-item order/final-value/effect/suspend-resume/`elsif`/no-else checks. The only proposed old-expectation change is the exact parser brace-rejection case below, pending CLEAN pre-write spec review. Never edit the fixture or weaken unrelated expected output.

The exact allowed conditional write-path set is the subset in the revised R187 sprint candidate's “Conditional candidate paths,” including the newly leased `tools/inference-playground/tests/cli_ordinary_islands.rs` file. The fixture, `tools/inference-playground/src/lib.rs`, and dirty `candidate_context.rs`, `candidate_scheme.rs`, `lib.rs`, and `shadow_apply.rs` remain excluded. If exhaustive matching, source construction, accounting, rollback, or runtime routing requires an excluded owner, stop and report NO_SAFE_CODE_SLICE; do not write around it or touch dirty bytes.

Verification-only scratch lease: `/tmp/yulang-r187-validation-r7`, Luna-owned. Create from the pinned baseline archive, overlay only changed paths from this exact candidate set, and keep Cargo output inside `target/`. Do not copy dirty excluded files, create Git metadata, or implement there. Delete the scratch tree after isolated checks and final review.

## Exact expected-output amendment proposed for review

At the pinned baseline, two reviewed deltas remove the braced source from missing-introducer rejection assertions and add consumed/error-free braced `IfArm` parsing. Rev8 addresses only `if_inline_boundaries_preserve_pending_payload_leading_and_successor` for `head == "if x: a else"`, no error, and suffix `" { rest"`: the parser now consumes the opening brace as an incomplete braced else body and records recovery. Remove only that tuple combination from the pending-boundary matrix and add a dedicated recovery assertion; verify HIR refuses to publish the partial sequence. All other suffix cases, parser expectations, Web output, and fixture bytes remain protected until separately reviewed.

Revision 1 review was NOT CLEAN: the new CLI path lacked a governing lease and the old-expectations clause was too broad. Rev2 fixes the lease and narrows the one expectation exception; no code or test was written under rev1.

## Review and implementation gates

1. Rev6 prospective review was CLEAN and Luna activated the exact source path set. Rev7's delta is CLEAN. Rev8 needs CLEAN review for the malformed-else recovery expectation before that test change.
2. Continue Luna implementation on the existing exact source path subset, with 1080 seconds remaining after 120-second transfers for rev7, rev8, and proposed rev9 spec reviews. Any added source owner or semantic choice needs a sequential contract revision and fresh review.
3. Run only focused checks in the leased isolated tree and 600-second verification allocation. Keep one heavy Cargo process at a time. The malformed-else expectation remains protected until the rev8 pre-write review is CLEAN.
4. Obtain separate independent proof and implementation/source/check reviews under their own allocations. A test pass is not proof or universal source coverage.
5. Stop with honest unresolved gates if the exact path or budget does not support the complete fixture route. No borrowing, blanket staging, or expected-output edits.

## Evidence, exclusions, and falsifiers

The frozen baseline and 50 blob hashes/modes are pinned in the R187 sprint contract. The unchanged fixture SHA-256 is `f10e7e57cdfc165436a89326c9f069f19aa0afd24cea80b2b570463fcc553487`. Relevant prior design evidence: R184 source-owner map `f38e913e7e0eda6558dac293714176b9d6d1bd8f66e2a28e4bf7e69cda2a6f9f`; corrected R186 contract `4e59c25947f3e3ea5acc746ca3e4483f7c4225028f93ad9ec54db3035c2117d9`.

Falsifiers include a lost, duplicated or reordered source item; a value other than the final child's value; missing item effects; a resumed continuation that repeats or skips a suffix; no-else returning a body value; malformed syntax yielding partial executable source; an unused retained definition/arm/dependency/child escaping certification; a fixture result change; or any implementation dependency outside the exact reviewed path set.

No source mutation, test, build, sample execution, compiler/evaluator run, or expected-output change occurred during this design assignment. Record-specific semantics and parent theorem obligations remain OPEN.

Revision 2 review was NOT CLEAN on candidate/current resource mismatch and a stale handoff pin. Its pre-write spec review approved the exact brace expectation change. Rev3 synchronizes candidate, design, handoff and current-state resources; no tests were edited.

Revision 3 bundle review was NOT CLEAN on inconsistent candidate budget prose and stale handoff pin. The exact expected-output delta independently passed pre-write spec review. Rev4 synchronizes all pins and reduces code to 1680s to fund another 240s bundle recheck; no source/tests were edited.

Revision 4 bundle review was NOT CLEAN on budget-charge accounting and the handoff code grant; the exact parser expectation change remains independently approved pre-write. Prior receipts: `notes/progress/2026-10-21-r187-contract-review-history.md` SHA-256 `b18aca005fe9b670dc8c2d9e1e556fd10a89b53e90ea58dc70112377aa755850`. Rev5 reduces the code grant to1440s and separates consumed from future resources.

Revision 5 bundle review was NOT CLEAN on review-charge interpretation and the stale implementation handoff grant. Rev6 records charged/reserved separately; code1440, no expected-output delta change.

Rev7 delta: source implementation has begun on already approved clean files. `cargo check -p yu-hir` and `cargo check -p yu-solver` pass. `cargo check -p yu-playground` is blocked by two diagnostics in the dirty excluded `crates/yu-solver/src/shadow_apply.rs`; those bytes were not inspected or edited. Dispatcher `/root/r182_dispatch` recommends continuing on leased paths and preparing a baseline-isolated validation tree, with current workspace verification marked BLOCKED. Rev7 adds the exact temporary root and the newly discovered parser assertion delta; no edit to that assertion occurred before review.

Rev7's isolated `cargo test -p yu-syntax if_` run passed 29 tests and exposed one remaining old pending-boundary expectation for incomplete `else {`; only that specific combination failed. No rev8 expectation edit occurred before its review.


## Rev9 exact Web selector delta (pending)

Baseline inspection shows `web/playground/index.html` hard-codes the `<select>` options. The existing rev8 TypeScript map and smoke test cannot expose the unchanged fixture through the visible selector without one new HTML option. Rev9 proposes a single option value `yulang2_ordinary_islands`, matching `main.ts`; preserve all other options, defaults, fixture bytes and outputs. Baseline committed SHA-256: `68ffb6b9c064dc6b0d6047a70acec19c11b55e3082873af640336aad509e587b`, mode `100644`. This path remains unedited until independent prospective review is CLEAN.

The user has stopped further builds/tests due storage use; isolated `cargo clean` removed 1236 files / 1.3 GiB. Rev9 review allocation 120s transfers from the code reserve; after issue, charged3660/reserved2340, code1080, verification600 inactive. Parent theorem and production remain OPEN.
