# R135 — reviewed receiver checkpoint readiness

Status: ADMITTED for one exact `candidate_receiver.rs` target and fresh static review.
Parent goal remains unchanged: Yulang soundness and original Simple-sub A/B; this packet closes no theorem or production gate.

## Authority and baseline

User-authorized objective: analyze Rust implementation and push coherent reviewed checkpoints. This version permits only the exact one-file source-only research checkpoint below after independent PASS. It does not waive R111's private compile/resource gate or authorize compilation, tests, Lean, or production.

Baseline branch `yulang3`, commit `ff3751ea588ad5840d49fc0fb0e23c71215766d7` (HEAD = origin at admission). Committed receiver base SHA-256 `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`; exact proposed target SHA-256 `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165`, 296,602 bytes.

Frozen composition inputs: R117 rev-2 patch SHA `c3858b35433433806e7f8a01f27c12ab5491a8116e6e88c2b1e32a6ccf5beab1`; R119 corrected patch SHA `5bc02af31d3c80ecae3848760b8723195dd568a7bf924cfc8b3b614b1227a18a`; R127 ordered composition receipt SHA `0c503338c144eab1feb2fce128227a7409f312b947876cd504f5b1af9fd1050e`; R127 independent review and correction-only rereview are recorded in its outcome. Current committed API dependencies: `lib.rs` SHA `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`, `candidate_scheme.rs` SHA `9cb8349a6ad43ddde8f54ae04ea464a61781b626b25917e928d45d49de3b2012`, `candidate_effect.rs` SHA `102d0c78bb57339ccf110b9da721f005c83ad88d5a32901d6c676b90376ddf01`.

## Outcome and exact work

Reconstruct the exact target in memory from the committed receiver blob and only the frozen R117/R119 patches in the reviewed order. Report complete hash/byte count and changed hunk inventory. Check the target's referenced APIs against the current committed dependencies above, and record whether R134's committed test-only trace changes any receiver interface. Do not inspect dirty or quarantined working-tree source; do not materialize source or scratch files.

The bounded semantic audit covers same-record permission transport, separate packed/native/concrete indices, first-position selection, `.get(index)` consumer behavior, missing/out-of-range/duplicate/foreign-owner guards, and unchanged fallback behavior. State clearly what static inspection does not establish.

Implementation lease: `tasks/agent-loop/inbox/effect-permission-consumer-checkpoint-r135-source.md`, max 240 seconds. Fresh independent compiler referee reviews only the frozen handoff and pinned committed dependencies, max 240 seconds. No source, test, manifest, lockfile, checker, Lean, build, environment/storage probe, scratch, staging, commit or Git mutation by workers. Total ≤900 seconds; Astra 0.

A PASS permits Luna to apply only the exact target to the index and push a research-only Rust checkpoint under this user's explicit request. Any hash/API mismatch, behavior expansion, ambiguous patch application or major finding blocks integration. Preserve all other dirty and untracked paths. The checkpoint remains uncompiled and untested; R111's compile/resource gate, A/B, Rust-to-Lean correspondence, effect hygiene and production remain OPEN.
