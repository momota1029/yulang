# R154 — audit receiver ownership and permission checks

Status: admitted continuation under the user's ongoing Rust/Lean goal. This packet audits the exact remaining dirty `candidate_receiver.rs` diff from immutable inputs. It cannot modify or integrate source.

## Baseline and frozen input

Committed baseline: `41c1582a26a8e80dbaa95171b298fc229a53d4aa`.

The sole subject is `tasks/agent-loop/inbox/effect-permission-receiver-ownership-r154-input.patch`, SHA-256 `db49313b2b4dd1e3623f135cc043b4d8be296868c5ec3dbfe90efa6ae5a66438`, 8,132 bytes. It is the exact binary diff from that baseline for only `crates/yu-solver/src/candidate_receiver.rs`; target worktree bytes had SHA-256 `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`.

Committed baseline receiver SHA-256: `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165`. Other pinned committed Rust sources:
- `candidate_effect.rs`: `4becefc07b81c1b298cafa190a3698e9e15e94656e1f17390eee13435dcb9b15`
- `candidate_scheme.rs`: `bc99466ff65d716c28295a0ab3ef2d50b1aef81c437bfcbac6ea4b79450a6ff2`
- `candidate_context.rs`: `a6e8bde3a187369ddf847a31f2ae6eb443434a34d819e44a7fc72c9788809905`
- `lib.rs`: `429456c4e19723c652842860aa2746988f4ab43550707cf840b1d047c69cb2be`
- `candidate_intrusion.rs`: `475edf15acbb5d986b5aebd1cb22b9c5fad61c50811690a763b39ff003cccd97`
- `candidate_source.rs`: `bb8348a4cf6f83df1099f06bb0e853a178d4629f85778730bb2f394d74745a49`

Relevant prior evidence: R117 native-decoder proof `0d5d17927a9b1cd2c7c72fb8b1ba0f7be44c146f7057cd1730b1b31dfcd32e53`; R118 Rust integration handoff `edec3e3d1747b9b4c78ea6ce19c9cc19de9db1f1ac113e4001c230db9249fd2f` and review `d82023743bd5fd0c47d5baf21082aaa702359c787acd8687cc2ebd15177551f5`; R119 Rust handoff `731cc66eacc5f271bdf1d70054b8430ac0641ac55ac07281123f9fe5645e8e98` and proof `cd7f488faa9bc3ae5670fa3dfc3ab050a19e0ec8f772a5003f0125bf6b891c6d`; R135 receiver review `tasks/agent-loop/history/effect-permission-consumer-checkpoint-20261102-r135-review.md` (read only for the accepted consumer distinctions relevant to this packet).

Workers must verify hashes before use and read committed blobs plus the frozen payload only. Do not inspect live `candidate_receiver.rs`, dirty `candidate_scheme.rs`, or quarantined runtime paths.

## Fixed outcome and exact leases

Implementation lane: registered `implementer`, at most 600 seconds. Exact outputs:
- `tasks/agent-loop/inbox/effect-permission-receiver-ownership-r154-source.md`
- `tasks/agent-loop/inbox/effect-permission-receiver-ownership-r154.patch`

Trace each deleted owner/batch/live-state check, provider/arm/operation check, and permission-origin check to its real constructor, caller and retained record. Classify it as independently guaranteed, requiring restoration, or unsupported. If one exact, source-supported useful patch remains, construct it in memory against committed blobs; otherwise report `NO_PATCH` or `HOLD`. Do not assume provider equals constructor/source owner for returned/local functions.

Source-correspondence lane: registered `prover`, at most 600 seconds. Exact output: `tasks/agent-loop/inbox/effect-permission-receiver-ownership-r154-proof.md`. Relate the receiver checks to the exact R117/R118/R119 identities and actual selected permission/member/consumer path; give a falsifier for cross-session equal ordinals, another provider/arm, or another permission origin. Reuse accepted evidence; do not rerun builds or Lean or invent missing correspondence.

Fresh independent `compiler_referee`, at most 300 seconds, reviews all frozen outputs and the complete candidate. Exact receipt: `tasks/agent-loop/history/effect-permission-receiver-ownership-20261102-r154-review.md`.

Primary integration/adjudication ceiling: 180 seconds. Total: 1680 seconds. R154 authorizes no source edits, patch application, staging, commit or push. A later exact source-only gate is required for any integration. No build, tests, Lean execution, environment/cache/scratch/worktree or snapshot copy.

## Stop boundary

Keep R153's source-only authorization limited to its exact three paths; it does not apply to this receiver target. Keep INITIAL-STATE, CONSUMER, H, original A/B and production open. If source owner, selected arm, or permission-origin evidence is missing, retain the uncertainty instead of restoring a guessed predicate.
