# R29 focused runtime R1 outcome

Date: 2026-10-30 (JST)
Repository session: `R29-20261030`
Task alias: `R29-RUNTIME-FOCUSED-R1`

## Decision

**STOP — focused runtime test failed on a frozen semantic assertion. No retry, source repair, separate route run, or Lean process is authorized by the stage receipt.** The test did not produce `owner-certificate.json`; certificate authentication and the proof application are therefore still unavailable.

The authorizing receipt is `tasks/agent-loop/history/effect-permission-native-callback-grant-20261030-r29-stage-runtime-r1.md`, SHA-256 `4a9a8bc864e653b3b6262c6422ed270115e9650e91147ee324d27222bbcc0428`. It authorized this one focused test only and required stopping on a semantic mismatch. Source review R3 ACCEPT and compile-only PASS remain limited to their separate gates; neither predicts this runtime result.

## Execution

Workspace: `isolated/ep-native-callback-grant-r29/project`. The single authorized command was:

```text
timeout 120s env CARGO_TARGET_DIR=build-target CARGO_BUILD_JOBS=1 cargo test --locked --offline -p yu-playground --lib r29_native_callback_grant_certificate_authenticates_request_observation_dynamic_installation_and_mutations -- --nocapture
```

The wrapper returned **101**. The test harness ran one test: **0 passed, 1 failed, 89 filtered**. It failed at `tools/inference-playground/src/runtime/machine.rs:4418:9`, where the assertion says the consuming write request must differ from the captured request. Both actual values were the same `SourceOperationId`. This is the first failure; it occurred before certificate generation.

`/usr/bin/time -v` reports wall time **0.09 s**, user time 0.04 s, system time 0.01 s, maximum RSS **33,760 KiB**, exit 101. Aggregate Cargo time is now **45.05 / 360 seconds** (44.96 seconds compile plus this 0.09-second runtime); remaining nominal allowance is 314.95 seconds, subject to a new stage authorization.

## Authenticated evidence

Worker receipt: `isolated/ep-native-callback-grant-r29/project/receipts/r29-focused-r1.receipt.json`, SHA-256 `6d55fcb41e6ba3e37e1d842d60f0d76eb16e72fc9869dea92b0af0157bdcb4ad`.

| Artifact | Bytes | SHA-256 |
|---|---:|---|
| stdout `r29-focused-r1.stdout` | 459 | `2534052e07068967a7f18460bb810491bfa05a6e891cc8a03cf97889abf4e342` |
| stderr `r29-focused-r1.stderr` | 15,760 | `bcdbbd5aac000ae4c4cd5a908cd3d137c0751f48933e8629b2eb135cf22ec8b8` |
| `/usr/bin/time -v` `r29-focused-r1.time.txt` | 1,002 | `a5875326a04e2a9af2f36016efe1bcca8af13ed3df0216702f3a073ccfdcc666` |
| status `r29-focused-r1.status.txt` (`101\n`) | 4 | `39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c` |
| structured worker receipt | 2,822 | `6d55fcb41e6ba3e37e1d842d60f0d76eb16e72fc9869dea92b0af0157bdcb4ad` |

All five frozen-input hashes matched before and after execution: `machine.rs` `b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425`; `receiving.rs` `55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2`; workspace `Cargo.lock` `de2c030452a0764cbeb459e2545585a880edc6683a8acceaea45276e24b67ca5`; package manifest `tools/inference-playground/Cargo.toml` `87e77de221b023c1c9f07e90f1ce6a692a56e8bb398eca4725f4910254be0a56`; and companion fixture `original-suffix-outer-receiver.yu` `0530c7ce6ef6d881d3106c9f69b42a992d701928f163c4c34c8b14f89408b6c7`. The certificate path is absent. The test thread PID was 3745755; the process ended, and a subsequent process check found no Cargo, rustc, Lean, Lake, timeout, or time process.

No runtime evidence was created for the callback certificate or either result as an accepted gate. The source assertion’s expected distinct-operation premise remains unadjudicated against the fixture/compiler semantics. The parent theorem, source correspondence, whole-language hygiene, principality, termination, and production all remain OPEN.

## Next boundary

Luna records the exact failure and asks the sprint dispatcher to select the next bounded action. Any source change, repeat test, selected-main CLI run, or Lean audit needs a new exact stage receipt and any newly required independent review. Do not treat the output-preservation success or exit 101 as a proof result.
