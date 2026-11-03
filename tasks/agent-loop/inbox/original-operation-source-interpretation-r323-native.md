# R323 native operation/continuation evidence — revision 3

Sprint contract: `tasks/agent-loop/sprints/source-operation-interpretation-r323.md`, SHA-256 `8e9fd4bba658cc441a1c68af82af5fb50e8fe9f27cabef49b7c9978c4dad4854`.
Assignment: `original-operation-source-interpretation-r323-native`; handoff revision 4, superseding revision 3. Baseline `62797081d`. Parent remains unchanged R159 and its R311/R293 dependent source obligations. Worker `/root/r323_native`; descendants none; runtime session/launch receipt unavailable in this child view. Requested model/effort: Luna/high per fixed packet. Observed model/effort: UNKNOWN.

Revisions 1–3 remain preserved under `/tmp/yulang-r323-native/`; revision 3 snapshot SHA-256 `5ce30765a01a1661bf42f36ea6b22ca13f2da46f9ae42c0f5c888bed7564f341`, revision 2 snapshot SHA-256 `c640d07d010dcd460c7263b65f7be01ba1c228406eb1b455d09d8440416ef362`, and revision 1 snapshot SHA-256 `e80e5c3d48d806f0f33741ae092cdf722df189a639841831afa9aad265711afe`.

## Result and parent application

Outcome: **provisional source/native evidence**, not a source-semantic proof. The existing accepted R315 run exports the actual source `tick` request, declaration identity and HIR annotation signature, payload and runtime value, its captured template root/node graph, and the accepted response delivered to the same template. It now traverses the live `resume_templates` node graph and validates root, node count, every inner link, ordered suffix labels, declaration pointer, and the capture-owner node before emitting data. It records the actual Owner-node replay resolution, including the pre-resolution control map, original/resolved/final owner, active/owned status, previous/current owner, invocation call/provider sites and template node index.

The supported suffix frame set is deliberately limited to the observed R315 case: `BlockExpression`, `Callee`, invocation/ambient Owner boundaries, and `RootCompReturn` View. `Callee` identity includes its frame id, optional callee label, argument label, environment, source-root/occurrence/range, and code identity. Other saved-frame or template-node kinds fail closed for this R323 exporter. Mutation checks alter the live template root, order, node count, inner link, and saved Callee environment; each is rejected. Same-HIR cross-run request/template/response data, wrong response value/handle, and fabricated owner remapping are also rejected.

This gives the proof owner concrete operands for the original operation/continuation interpretation at `.calleeRequest`; it does not establish that runtime execution implements the original mathematical `Request`/`Continuation`, a typed response/current-world domain, lawful whole-tuple response action, original observation guards/fields, `Meaning`, EI membership, or an `Inputs` instance. The response receipt is taken when `Frame::ResumeArgument` validates the response immediately before `EnterTemplate`; later owner remapping is a separate receipt at each live `TemplateNode::Owner`. No claim is made that those two owner observations are one semantic world or one original owner.

## Frozen evidence

The test-only exporter runs from the same R315 accepted source/parse/HIR/Machine and writes `/tmp/yulang-r323-native/r323-operation-source.lean`, SHA-256 `184bc988a31b2ec654b83e19c47cd6d8bedff0fd519e74ff9cbf0cd63d19ba1c`. It contains the full R314 source/code export, R315 `make` source/use and return snapshot, plus R323 request/response data. R323 records operation `tick`, its source operation identity and full HIR signature, actual received payload and dereferenced runtime value, same request event/template handle, actual outer Callee frame/site, exact response received value/view/runtime value/site, and response invocation owner/live bit. The template rows are derived from the live node vector after validation, including its root, node count, and inner-link sequence. Owner replay rows come from actual execution of each Owner node. Generated runtime `ValueKind` and nested received-interface constructors are namespace-qualified under `R314Artifact`; Lean 4.35 elaborates the exact artifact.

The source tree preserves the physical `act io: our tick: int -> int` declaration and the actual `make` initializer/request use. This is native/source evidence only; no semantic Union membership is inferred from it.

| Path | SHA-256 |
| --- | --- |
| `tools/inference-playground/src/runtime/machine.rs` | `7584f2e4630ec549dc2f4214a06e7c6feef48c912d3ab57692efe383044f246a` |
| `tools/inference-playground/src/runtime/program.rs` (read-only) | `2c03ff8681c50520e0527f139a86ac8427097c27aeafcf247e76673310be4b0c` |
| `tools/inference-playground/src/runtime/dispatch.rs` (read-only) | `d99acad3e344bc06970faf0486ff7d10ba92bc7514cfb7eec58df8bbb28f6360` |
| Governing operation construction §§2–4 (read-only) | `4fe70b18cad9ded249869b21b84bbf26e2a5f95320f79632a29a5071ddb1c4e9` |
| R315 source/native handoff (read-only) | `0be1adb4eada8251e68046d2ffafb87ac67a7a2d53a748d686b0f5587012ac8a` |
| R322 open proof/source obstruction (read-only) | `78e9eed06eebf80be1aada0a0a48d3e640ac99bfdd529e9efb93ab50599be2cd` |

## Checks and resources

- `CARGO_TARGET_DIR=/tmp/yulang-r323-native/target YULANG_R323_LEAN_WITNESS=/tmp/yulang-r323-native/r323-operation-source.lean cargo test --locked --offline -p yu-playground r313_accepted_source_callee_returns_after_request_and_observes_value_name --lib` — **1 passed**, 94 filtered out; regenerated the frozen artifact above.
- `CARGO_TARGET_DIR=/tmp/yulang-r323-native/target cargo check --locked --offline -p yu-playground --lib` — passed in the non-test configuration, confirming `resolution_control` collection/sort is compiled out.
- `git diff --check -- tools/inference-playground/src/runtime/machine.rs` — passed.
- Pinned Lean 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`): `/home/momota1029/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean -M2048 /tmp/yulang-r323-native/r323-operation-source.lean` — **passed** on the exact generated artifact; log `/tmp/yulang-r323-native/lean-check.log` is empty. Semantic parent check and source-semantic proof/axiom audit — **NOT RUN**. Full Rust suite — **NOT RUN**.
- The assignment ceiling was 1800 seconds. Wall/CPU/RSS instrumentation was unavailable; the targeted Cargo test and one pinned Lean elaboration completed and no heavy checker or background process remains. Cargo output is isolated under `/tmp/yulang-r323-native/target`; the same leased scratch directory contains the witness, checker log, and preserved earlier handoffs. No other scratch path, dependency/config edit, `program.rs`/`dispatch.rs` write, Git operation, or child was used.

## Reused evidence, open premise, and next step

Reused R315's source/native run, parse/HIR ownership, `make` root, exporter, and snapshot ownership checks. R315 publication and R321's formal declared-response result were not treated as original operation-request/response semantics. R322's failed proof attempt remains the falsifier: the original source/semantic owner still must derive the request observation guards and fields and executable continuation meaning; native reachability cannot supply those independent facts. The reviewed operation-image construction §§2–4 constructs bounded source equations, but explicitly does not choose W/Z semantics or prove this runtime corresponds to the original source relations.

TODO `R323-NATIVE-TO-PROOF-1`: for unchanged `OriginalComputedCallInterpretationR311.phaseBody` at `.calleeRequest` and `ComputedCallUnionRealizationR293.app_result_pair`, consume this frozen artifact alongside R315/R321/R322 and derive the first actual typed response/current-world domain and lawful whole-tuple response action from the original constructors and laws. Preserve all alternatives, providers, worlds, substitutions and Checking goals. Return a checked parent-edge application or exact residual Lean goals with the source-semantic owner. No source semantic rewrite or production promotion follows from this handoff.

P2 repair: the control-map vector collection and sort now both have `#[cfg(test)]`; production still uses only the original `resolve_control` and owner decision. This revision also qualifies generated runtime-value constructors under `R314Artifact`, fixing the reported Lean namespace error without changing runtime behavior.

The exporter, test instrumentation and artifact remain provisional until fresh independent source/native review and proof-owner consumption. Falsifier: any proposed correspondence fills an original independent premise from runtime reachability, callback/diagnostic evidence, desired `Meaning`/EI membership, or altered original domains. Luna owns cleanup after review. Worker writes stop after this revision; no descendants or running process remain.
