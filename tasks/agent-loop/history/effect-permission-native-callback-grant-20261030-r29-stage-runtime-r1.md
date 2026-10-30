# R29 focused runtime stage R1

Date: 2026-10-30 (JST)
Primary: Luna
Repository session: `R29-20261030`
Task alias: `R29-RUNTIME-FOCUSED-R1`

## Authority and gate

This receipt authorizes only the frozen R29 focused certificate/mutation test after the R3 exact-source ACCEPT, the compile-only R1 exit-0 result, and the dispatcher's bounded-runtime recommendation. The test is the single contract-pinned test named below. It exercises the callback selected-main result `1`, the companion selected-main result `23`, certificate joins, and the changed-target mutation assertions implemented by that test. This receipt does not authorize separate CLI route runs, source edits, Lean/Lake work, another compile, retries, or production changes. Any next step needs a new Luna receipt.

The source review is `tasks/agent-loop/history/effect-permission-native-callback-grant-20261030-r29-review-r3.md` (SHA-256 `8645fcc1adb9fe0beb82ca29d1bd7c9a8ae654006efa403d57b3688ba56a78da`). Its ACCEPT is limited to the exact frozen source and precompile gate. The compile-only outcome is `tasks/agent-loop/history/effect-permission-native-callback-grant-20261030-r29-compile-r1-outcome.md` (SHA-256 `d126dec270a9912f0185f97fc3c88fa8e91101924e1cfa292177cacaa7c34977`): exit 0, 44.96 seconds, no harness execution, and incomplete combined-output transcription. The dispatcher adjudicated compile PASS with that output-preservation limitation and recommended a separately recorded focused runtime stage. The compile output limitation remains visible; this stage must save complete streams.

## Frozen inputs rechecked before authorization

Workspace: `isolated/ep-native-callback-grant-r29/project`.

- `tools/inference-playground/src/runtime/machine.rs`: `b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425`
- `tools/inference-playground/src/runtime/receiving.rs`: `55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2`
- workspace `Cargo.lock`: `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`
- package `tools/inference-playground/Cargo.toml`: `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56`
- companion fixture `tools/inference-playground/examples/original-suffix-outer-receiver.yu`: `0530c7ce6ef6d881d3106c9f69b42a992d701928f163c4c34c8b14f89408b6c7`
- schema: `tasks/agent-loop/sprints/effect-permission-native-callback-grant-20261030-r29-schema-r1.json` (SHA-256 `b2d03bbba4ae78f8e2f9b0517c4b25c176372a158d77a1baa0e3c6d601294379`)

The exact test exists in frozen `machine.rs` and writes the certificate to `receipts/owner-certificate.json`. The preflight comparison matched all listed files. Existing Cargo target cache is retained in the isolated workspace.

## Exact authorized operation

Run once, from the workspace above, with one Cargo job, offline and locked, using the existing `build-target` cache and a 120-second timeout. Preserve the exact raw streams, process status, resource receipt, before/after frozen-source hashes, and generated certificate under `receipts/`.

Cargo argv:

```text
timeout 120s env CARGO_TARGET_DIR=build-target CARGO_BUILD_JOBS=1 cargo test --locked --offline -p yu-playground --lib r29_native_callback_grant_certificate_authenticates_request_observation_dynamic_installation_and_mutations -- --nocapture
```

Capture wrapper:

```sh
/usr/bin/time -v -o receipts/r29-focused-r1.time.txt timeout 120s env CARGO_TARGET_DIR=build-target CARGO_BUILD_JOBS=1 cargo test --locked --offline -p yu-playground --lib r29_native_callback_grant_certificate_authenticates_request_observation_dynamic_installation_and_mutations -- --nocapture > receipts/r29-focused-r1.stdout 2> receipts/r29-focused-r1.stderr
```

Record the wrapper's exit status exactly in `receipts/r29-focused-r1.status.txt`; do not replace either stream with a paraphrase. Record SHA-256 hashes and byte counts for stdout, stderr, time/resource output, status, and `owner-certificate.json`. Confirm the source hashes before and after execution and confirm the test process has exited. The wrapper only captures this one command; it does not authorize another Cargo invocation.

Aggregate Cargo time already charged: 44.96 / 360 seconds. This invocation cap is 120 seconds, leaving at most 195.04 seconds of aggregate Cargo allowance if it reaches the bound. One heavy process at a time. Independent review has 500 seconds reserved for final evidence review.

## Stop and reporting rules

Stop immediately on nonzero status, timeout, missing certificate, failed/absent/unchanged required mutation, selected-main mismatch, frozen-source hash change, missing raw output/resource/status, or any newly required source path. Preserve all evidence and report the exact first failure; no retry or repair under this receipt. A successful test is runtime evidence only. It does not check the Lean bridge, authenticate Lean theorem application, close History/RootComp, prove parent A/B or whole-language hygiene, or authorize production promotion.
