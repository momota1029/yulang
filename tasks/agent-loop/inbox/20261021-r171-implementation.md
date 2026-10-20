# R171 implementation handoff — result revision 3

Assignment `formal-name-forwarding-instance-20261021-r171`, contract revision 1 SHA-256 `2491bcdc3dc7b09f8aeb06754ebe635b1dae4b8c1e8cef5f526c7517ea667241`.
Status: **result frozen for independent final review**. This sequential revision supersedes invocation revision 2 SHA-256 `dc7afac5b53acfd33371205a6e525a8c531984aa502adb9d72351a0c9e57cbca`; its exact command, confinement and pre-run reviews remain pinned there and in Git history. No further probe is authorized or performed.

## Frozen inputs and reviews

- Baseline code HEAD: `e27d00039`.
- Fixture `tools/inference-playground/examples/r171-formal-name-forwarding.yu`: SHA-256 `cb2fff33a1ab983a932064cc1699d9f4f4a8d5e00d52986525884d42bc58234f`.
- Harness `tools/inference-playground/examples/r171_provider_incidence.rs`: `b8d9afd91154c7b0df1d1192ad1567a0e25fac7ef4ff4b698d989acd1c205e75`.
- Proof note: `notes/theory/2026-10-21-r171-forwarding-instance.md` SHA-256 `d19b5ceb2c1ace95ce2cc49bdd6c35ef4bd4de223f07e181a472a037a35a133b`; proof handoff: `tasks/agent-loop/inbox/20261021-r171-proof.md` `37f3057c3c5be46eb36e6624cdc98e4945d9943d90ebcd9cb765c32e85b13525`.
- Independent source/native proof review: `/root/r157_contract_review`, CLEAN. Independent code/source-harness review: CLEAN. Independent exact invocation review over revision 2 and all pins: CLEAN. Reviewers did not execute builds, tests or probes.

## One authorized probe result

The exact revision-2 command was run once in-repository after all gates were recorded CLEAN. The fixture parsed/lowered and `CandidateInference::solve` succeeded. Probe status, exact managed process-group status and separate marker scan status were all **0**.

- Stdout `tasks/agent-loop/probes/20261021-r171-provider.stdout`, SHA-256 `5c47875a6bdb59da380772df81660ec71ac59b9317030de149e26599c883fff5`.
- Stderr `tasks/agent-loop/probes/20261021-r171-provider.stderr`, `46e3e404c5231180c92d1562b3ec380c135cf9901ea7638640c01b9627d06be5`.
- Status `tasks/agent-loop/probes/20261021-r171-provider.status`, `68c10920ac9b4b082ad35849d64232dd27adbe99c2c22f108f9104548d052cad`.
- No Yulang2/web demo, evaluator, tests, retry, external runtime, alternate checkout, nested CLI, network or background service.

Observed provider q values 27/77/95 and FunctionPort ordinals 43/45, 123/125, 156/158. Capture routes include occurrences 8/13 with context_use 1/2. The observer says `NotJoinedToContextRecord`; output reports `rows_truncated=true` under the shared 64-row cap, with individual record truncation also visible. These observations do not establish source FactId/Terms → same provider Capture/shared-anchor/maps → ordered transport/Replay → same A_F consumer q. The exact first missing association and owner/falsifier are in the proof and result notes. No mismatch, counterexample, or universal theorem closure is claimed.

Result note: `notes/theory/2026-10-21-r171-native-instance.md`, SHA-256 `a57e2b3aa012251d99a34f1dab42894a9c2ed76541b1e51ddc7c8526b6b3f147`. Final result review is pending and must be independent of Luna. Parent R169 incidence, R70/R71/R165/R166/Replay residual, original A/B and production gates stay OPEN. Writes are stopped for this result; no descendants or generated outputs remain outside the dedicated `target/r171/` probe tree and exact receipts. Luna owns final review adjudication, current state, closeout, commit and push.
