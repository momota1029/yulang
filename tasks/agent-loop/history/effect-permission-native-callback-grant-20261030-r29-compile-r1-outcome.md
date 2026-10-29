# R29 compile-only stage 1 outcome

Recorded: 2026-10-29 23:58 UTC. Primary adjudication after the compile-stage authorization and worker STOP.

## Decision

**PASS for the authorized library test-target compilation only, with an output-preservation limitation.** The exact authorized command ran once and returned exit status 0 after 44.96 seconds. The worker reports that Cargo finished the test profile and emitted the unit-test executable; it was not run. This establishes successful compilation of that target for the frozen source, not successful test execution, runtime behavior, certificate generation, mutation rejection or Lean correspondence.

The source hashes before and after execution match the admitted pins: `machine.rs` `b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425`, `receiving.rs` `55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2`, and mutation design `75a408c3cd4f0a8b95a156fb5687cf577d9a927e0a9667c3dd704d154c18c5c2`. No source edits occurred. The timeout and Cargo processes exited; no runtime or Lean/Lake process ran.

## Frozen execution evidence

The original authorization is `tasks/agent-loop/history/effect-permission-native-callback-grant-20261030-r29-stage-compile-r1.md`, SHA-256 `75585241d3a7aedd1316cc1a3b3153740cfd87f907a32e29479a34f81ff979b8`.

Worker receipt: `isolated/ep-native-callback-grant-r29/project/receipts/r29-compile-r1.receipt.json`, SHA-256 `5e6a6b3baff1aa1f4b879942fb7fade1415f91cba2fa76a0cb20efc4c756cbe9`.

Saved output transcription: `isolated/ep-native-callback-grant-r29/project/receipts/r29-compile-r1.output.txt`, SHA-256 `e2f633881e3370ec0ce37b0fa93d873a3263447bc4f7ef9f977b005b11571337`.

The execution interface returned one combined stdout/stderr stream, and the saved transcription is explicitly incomplete. It is not byte-exact and does not preserve stream attribution. Do not treat it as complete compiler output or infer that there were no warnings. The structured receipt records the tool-reported argv, cwd, exit status, elapsed time, source-hash comparison, output-path bound and stopped-process state. This logging limitation does not negate the exit-0 compile result; the R29 contract does not make separate complete compile streams an additional runtime prerequisite. The next runtime authorization requires separate stdout/stderr files captured directly by shell redirection.

The worker-session label in the stage authorization had an extra `RUST` token. The actual task alias was `R29-COMPILE-R1`; the repository current session remained `R29-20261030`. This naming correction changes no source, argv, process identity, scope or budget.

Cargo allowance charged: 44.96 / 360 seconds. No retry is authorized or needed. Independent reviewer charge remains 900 / 1,400 seconds, leaving 500 for final artifact and proof-applicability review.

## Next gate

The dispatcher recommends a separate Luna receipt for only the focused R29 certificate/mutation test. That test asserts callback selected-main result `1` and the pinned companion result `23`, and writes `project/receipts/owner-certificate.json`; it must establish every changed-target mutation result. A runtime receipt must pin the same accepted source/dependency hashes, preserve complete raw stdout and stderr, exit/resource data and the generated certificate, and stay within the 360-second aggregate Cargo limit with one heavy process at a time. No test or selected-main route has run yet. Lean remains STOPPED until runtime evidence and certificate are frozen and authenticated, then requires a fresh serialized audit receipt.

All original A/B, full History, whole-language hygiene, source generation/propagation, soundness, principality, termination and production claims remain OPEN.
