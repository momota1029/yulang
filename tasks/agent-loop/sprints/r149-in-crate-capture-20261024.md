# Sprint R149-IN-CRATE-CAPTURE-20261024 — provisional parser/HIR observation

Status: AUTHORIZED by Luna primary; revision 2 frozen before source edits.
Revision: 2
Supersedes revision 1 only by isolating every worker/source artifact in a new dedicated worktree because the three legacy UNKNOWN reservations include unspecified implementation/proof paths. No authority or evidence goal changes.
Branch / baseline: `research/simple-sub-intrusion` / `424566114b10aaa948c2a0ffac53f56567416114`
Primary: `/root`; owns current state, provisional capture code, outcome and Git.
Dedicated worktree: `/tmp/yulang-r149-in-crate-capture-20261024` on local branch `codex/r149-in-crate-capture-20261024`, created from the baseline above. The primary-owned scheduler contract/current state remain in the main checkout. The worker and all leased source/proof outputs stay in the dedicated worktree. Do not cherry-pick or merge its source edits into `research/simple-sub-intrusion` while any legacy reservation remains UNKNOWN; branch integration requires confirmed cessation/lease handoff first.
Original goal: implement Yulang type inference and evaluator from established proofs and approved source behavior; commit and push coherent changes, leaving the worktree clean.

## Parent claim and outcome

Advance the unchanged R149 Types/Console source-to-inference-to-execution admission by observing the actual parser and main HIR objects produced from the exact source bytes and the actual pinned provider parse/index objects. This continues, but does not replace or narrow, the R149 claim. The original Simple-sub and evaluator A/B claims, their quantifiers and source domain remain OPEN.

The requested observation ends after the actual main HIR is constructed and before `pinned_candidate_world`. It covers the main HIR plus provider parses, export indexes and role indexes. It does not cover selected provider/member HIR, full initializer membership, inference publication, evaluator execution, or host output.

Success is either (a) one reviewed capture of actual syntax environments, parser diagnostics/recoveries, source-key identity/equality and main-HIR/provider-index identities for the unchanged Types and Console inputs, joined to the earlier R149 admission trace, or (b) an authenticated actual constructor failure. A visibility/API limitation alone is not parser evidence.

## Fixed inputs and dependencies

Authoritative source inputs and prior evidence remain those pinned by `tasks/agent-loop/sprints/r149-exact-source-readback-20261024-rev2.md` (SHA-256 `20541baa2157ffaa9453b7b076bb0b686b61c4663d187cc00af822026905fbe2`). In particular, Types is 142 bytes (`8cbfb97a8df8e5dc4916313769c39a84626ae124f91f8a9672f1ad8b866f98e6`), Console is 92 bytes (`ada6174d8795ddb10a8c533c812b771d9dddced816762e0e246022467499a076`), and the embedded standard-library bundle is 89,288 bytes (`9eb726f179fa407122f1c31f4cd4cf98484bce3052d2486d7d7be84d4ec22b66`). The existing reviewed source-admission outcome is `tasks/agent-loop/sprints/r149-current-source-admission-20261024-outcome.md` (SHA-256 `7cd904d92e6318b4af9957b50ac78a0ff04c694e6eabaa0a61fe9e4dd0d10450`), with proof note SHA-256 `d4c6b9e176f9577e20d05dc2fae24b9c0ff68c926525373b3568900acf39db06`.

At sprint start, the four direct hashes still match the prior readback contract: `lib.rs` `45bf78af436efa50e02ca97ba3b639c11f7dd88272d87c47f2822643786653d4`; `pinned_stdlib.rs` `3d1a32946e764effd354271653e68edd1b2edaf980f51ea5178ad21adb633d4e`; playground `Cargo.toml` `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56`; and `Cargo.lock` `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`. The checked-in parser manifest and transitive `yu-syntax/src` pins remain exactly as enumerated in the prior contract. Any changed dependency pin stops this packet.

The code snapshot at `aba6c8eb9b9caf2559bf955670d662503950c98d` is unchanged at the direct source owners; the current baseline adds only the reviewed proof-index documentation commit. No manifest or lockfile edit is authorized.

## Reviewed provisional code boundary

A prospective static design review by `/root/proof_implementation_referee` accepted this exact style of temporary capture on 2026-10-24 01:18:01–01:18:35 UTC (34 seconds, two read-only shell calls; no edits, build, tests, probes, Git, or descendants; session/model/effort UNKNOWN). This receipt is design review only, not code review or runtime evidence. Its findings are frozen here:

- A cfg-gated capture module/entry inside the local `playground` module graph can expose the real objects without a durable public API. Do not mix `yu_playground` library types into the captured type universe.
- When `lib.rs` is included as a module by the temporary example, root aliases must cover `output`, `scheme`, `render`, `location_into`, `conflict_ranges_for`, and `OperationV1RuntimeReceipt`; a `runtime` alias is harmless. These aliases refer to existing modules/types and must not create duplicates.
- The only required temporary crate-visible widenings are `output`, `scheme`, and `conflict_ranges_for`. `location_into` is already crate-visible; the other listed symbols are public.
- Preserve the existing constructor inputs, order, decisions and failure paths. Capture the main parse before diagnostics, actual provider parses before their indexes, and actual main HIR immediately after lowering; stop before `pinned_candidate_world`.
- The resulting boundary is main HIR plus provider parses/indexes, not selected provider/member HIR, which is constructed later.
- The supplied source hashes matched at review time; compilation was unverified.

The permitted code delta is limited to a temporary `#[cfg(r149_exact_source_readback)]` capture arrangement in `tools/inference-playground/src/lib.rs`, any strictly necessary cfg-gated helper in `src/pinned_stdlib.rs` that exposes the same resolved provider objects without reparsing or altering their order, and the one example driver below. The only visibility changes allowed are the three above, and only for this custom-cfg build. If the implementation needs a different gate, additional symbol widening, changed call order, a second parse, another environment, manifest/lockfile changes, parser/HIR crate edits, or semantic/API behavior outside the cfg build, STOP and return to Luna for a new review and grant.

The temporary example may report stable local labels, syntax kinds/ranges, diagnostics/recoveries, genuine same-parse source-key equality/ownership, HIR declaration IDs, and provider source/index identities. Names, Debug output, pointers, or byte ranges alone do not prove source-key identity. Apply the real downstream acceptance rule; do not treat every recovery as fatal by assumption.

## Exact leases and lanes

Primary-owned source/scratch paths inside `/tmp/yulang-r149-in-crate-capture-20261024`:

- `tools/inference-playground/src/lib.rs` — cfg-only capture and exact visibility changes above.
- `tools/inference-playground/src/pinned_stdlib.rs` — read-only dependency; edit only the narrowly allowed cfg helper if the frozen implementation demonstrates it is necessary.
- `tools/inference-playground/examples/r149_exact_source_readback.rs` — one temporary example, no expected-output/test changes.
- `target/r149-in-crate-capture-20261024/` — ignored scratch only: `readback.json`, `stdout.txt`, `stderr.txt`, `command.txt`, and generated `cargo-target/`.

Proof/source worker exact output paths inside `/tmp/yulang-r149-in-crate-capture-20261024`:

- `notes/theory/2026-10-24-r149-in-crate-capture.md`
- `tasks/agent-loop/inbox/20261024-r149-in-crate-capture.md`

Primary-owned scheduler paths in the main checkout: `tasks/agent-loop/current.json`, this contract, and `tasks/agent-loop/sprints/r149-in-crate-capture-20261024-outcome.md`. The source/proof worktree artifacts remain isolated until the unknown lease boundary is reconciled; copying them into the main checkout is also integration and is not authorized before that boundary is confirmed.

The proof worker must establish the capture-transparency argument against the exact frozen source delta, join the actual observations to the reviewed R149 partial trace, and state the first remaining provider-selection/fetch or inference/evaluator premise with its owner. A source-level argument without the actual readback does not claim an observation. The worker must not edit code, shared state, other proof records, tests, expectations, or Git.

## Verification, resources and review

Total cap: 3,600 seconds; proof lane at most 1,200; primary implementation/evidence at most 900; independent review at most 300. Zero Astra. Preserve all three legacy UNKNOWN identities and their quarantined reservations; do not reclaim or overlap their paths. The dedicated worktree is the isolation boundary for any source/proof paths that might coincide with those unspecified leases. One proof worker runs beside Luna's primary lane. One fresh independent `compiler_referee` reviews the frozen code delta before any build/readback and the bounded resulting evidence within the same review allocation.

Run no tests and no evaluator/runtime execution. After the code delta is frozen and independently reviewed, allow one `cargo run --locked --example r149_exact_source_readback` invocation with the custom cfg and a task-specific target directory, with one CPU and at most 120 seconds for readback. It may perform the single bounded build and single readback together. No second build, test, probe, network access, or command that recreates the readback. Record exact command, exit status, all stdout/stderr/JSON, source/dependency/artifact hashes and elapsed resource evidence. Remove only this sprint's exact temporary source/scratch paths after processes stop and durable review/outcome receipts are frozen; retain no production-visible capture API.

Stop on changed pins, non-identical capture inputs/order, a required second/alternate parse, lost recovery evidence, foreign or reconstructed source keys, unexpected constructor failure, resource limit, unavailable reviewer/runtime, or any need to exceed the above authority. Preserve the failed/partial evidence honestly. R149, source-to-CST closure, the original A/B claims, implementation and production gates remain OPEN until their own evidence is independently adjudicated.

Next dispatcher boundary: reviewed readback/falsifier, authenticated constructor failure, evidence that identifies a concrete authorized compiler repair, dependency/authority expansion, resource limit, or integration.
