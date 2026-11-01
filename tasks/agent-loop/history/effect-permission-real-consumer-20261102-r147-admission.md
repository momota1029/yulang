# R147 admission

- Sprint: `EFFECT-PERMISSION-REAL-CONSUMER/20261102-R147`.
- Baseline: pushed `3560df97dab02744da10e897c73c1cf94118f4ee`.
- Dispatcher: R146 end dispatch selected an independent source rederivation plus proof correspondence and fresh review. R146 proof budget is spent/closed; none is restored. R146 proof handoff remains a procedural NO_VERDICT receipt, and its substantive observations are excluded from R147.
- Contract: `tasks/agent-loop/sprints/effect-permission-real-consumer-r147.md`; its exact SHA-256 is recorded in `current.json`.
- R146 closure receipt: `tasks/agent-loop/history/effect-permission-native-incoming-state-20261102-r146-outcome.md`; source handoff remains unreviewed until the R147 reviewer reads the frozen baseline independently.
- Frozen inputs: exactly those listed in the R147 contract, including nine immutable Rust blobs, two immutable native Lean source blobs, governing compose-release decision, and the R146 source handoff. All Rust source hashes are qualified by baseline commit; dirty working-tree paths are excluded.
- Source assignment: Luna/high, max 600 seconds, output `tasks/agent-loop/inbox/effect-permission-real-consumer-r147-source.md`.
- Proof assignment: registered prover / role default, max 480 seconds, output `tasks/agent-loop/inbox/effect-permission-real-consumer-r147-proof.md`.
- Independent review: fresh compiler referee, max 300 seconds, only after both author lanes stop, output `tasks/agent-loop/history/effect-permission-real-consumer-20261102-r147-review.md`.
- Resources: total 1,560 seconds including 180 seconds primary integration. No Astra, executable checks, source edits, scratch, environment, checkout or worktree. Existing user capacity release for 16 exact reservations remains in force; no new override or path release is applied.
- Live roster sync immediately before admission: `collaboration.list_agents` showed `/root` active; every returned child was completed. No R147 worker was RUNNING/WAITING yet; no notification was due. Existing UNKNOWN observations and quarantined paths remain intact. Active/reserved assignment count after admission will remain within the global limit under the already authenticated capacity disposition.
- R147 author intake: source handoff SHA-256 `d4f20f0f47d64b35416053c1f3be86daba197113b60acfb17ebf2cde9a3793ef`; proof handoff SHA-256 `f12a4cdbfe27bccb5a9a617ad40f775e7896b7c8b644f440a4b8c43f0de6a010`. Dispatcher classified the proof lane's R146 source handoff check as `ADMITTED_INPUT_HASH_ONLY / LATE_INTEGRITY_CHECK / CONTENT_NOT_USED`: all twelve direct Rust/Lean/design hashes preceded source inspection; the admitted R146 source artifact was hash-checked afterward, with its body/conclusions not opened or used. This is not a source-boundary deviation and does not adjudicate proof content. Reviewer must hash all frozen inputs before review and independently rederive source claims; R146 proof deviation contents stay excluded.
- Git: Luna only; explicit staging of a coherent reviewed result and normal fast-forward push. No force push.
- Original A/B, semantic approval, source/native closure and production readiness remain OPEN.
