# R29 closeout — CLOSED_INCOMPLETE

Sprint: EFFECT-PERMISSION-NATIVE-CALLBACK-GRANT/20261030-R29. Closeout revision: 1. This record resolves R29 as a failed, incomplete runtime packet; no parent proof or production gate closes.

## Frozen outcome

- Last coherent checkpoint: cf382d2a8a401de74a6d2ed355240bee7827b440 on yulang3; origin/yulang3 was verified at the same commit.
- Contract SHA-256: 8c9784de8a3e33f7e17c2747fcc7e452bda02bb8f4a4a7358c14290642c1457f.
- Schema SHA-256: b2d03bbba4ae78f8e2f9b0517c4b25c176372a158d77a1baa0e3c6d601294379.
- Inputs SHA-256: 8022d3e6462012f4a8bbf3124d6c286683976f259fe8b5bd084dfaf8ac4cf83f.
- R3 source review: ACCEPT, limited to the exact frozen source and precompile review. machine.rs SHA-256 b74c8345e6e07155f482440bb9299b5fc12763accb666ca8f543156dd4a87425; receiving.rs SHA-256 55b468cda3c3cf8180647a6429da28fc70badf7a371bf1b327539c8556b9b0f2.
- Runtime authorization: tasks/agent-loop/history/effect-permission-native-callback-grant-20261030-r29-stage-runtime-r1.md, SHA-256 4a9a8bc864e653b3b6262c6422ed270115e9650e91147ee324d27222bbcc0428.
- Runtime outcome: tasks/agent-loop/history/r29-focused-runtime-r1-outcome.md, SHA-256 eef034225eb0bf1165d4dfbe5176b74c52974a23a7a0a21b85bd76ce601f40de. Runtime receipt SHA-256 6d55fcb41e6ba3e37e1d842d60f0d76eb16e72fc9869dea92b0af0157bdcb4ad.
- Raw stdout SHA-256 2534052e07068967a7f18460bb810491bfa05a6e891cc8a03cf97889abf4e342; stderr bcdbbd5aac000ae4c4cd5a908cd3d137c0751f48933e8629b2eb135cf22ec8b8; time a5875326a04e2a9af2f36016efe1bcca8af13ed3df0216702f3a073ccfdcc666; status bytes are 101 newline, SHA-256 39b8dc3fc8b44765c8e6f1adee04c5b465e555ab791cc42d0d9e810d5b64297c.

The single focused runtime invocation exited 101 at machine.rs:4418. It had already observed callback result 1 and companion result 23. It failed before reaching the operation_family == write assertion. The test compared Debug-rendered identity strings. SourceOperationId derives typed Eq/PartialEq; SourceNodeKey Debug deliberately hides identity fields, so two distinct typed IDs can serialize to equal Debug text. The failure establishes a lossy test-evidence representation defect only. Typed identity equality itself was not asserted, so neither an effect-hygiene nor source-resolution counterexample is established. No certificate JSON was generated. No retry or source repair occurred under R29.

## Resource and worker disposition

The dispatcher classified the result as CLOSED_INCOMPLETE — RUNTIME_FAILED / SOURCE_ALLOWANCE_EXHAUSTED. Rust source authoring was conservatively charged: R1 600 of 1,200 seconds; R2 used an uninstrumented portion of the remaining 600; R3 was within a 60-second cap but lacked a measured charge. The record cannot authenticate at least 150 seconds of source-author budget. Cargo use was 45.05 of 360 seconds. Reviewer use was 900 of 1,400 seconds, with 500 remaining; Lean audits were 0 of 2 and 0 of 120 seconds. No R29 balance transfers to a successor. All three R29 workers are STOPPED and no heavy process remains.

The exact R29 project paths remain frozen or held under their original R29 leases. The unchecked bridge remains at SHA-256 e49a320fbb148712b59e27a57cde57072e2192cdcdd84c936b10175f3a6ce6e0. It is not an accepted native instantiation. R26 model SHA-256 remains 0621f43739c12ce1e7919a50de129414a4748d8359bf46740babd69f4854011e.

## Claim boundary

The failed run, accepted precompile source review, and unchecked Lean candidate do not close the R26 projection. Original A/B, History/RootComp, whole-language source/native correspondence, effect hygiene, soundness, principality, termination, and production remain OPEN. R29 is closed incomplete; its immutable sources, raw evidence, and unchecked proof candidate remain addressable through this history record and the R29 outcome files.
