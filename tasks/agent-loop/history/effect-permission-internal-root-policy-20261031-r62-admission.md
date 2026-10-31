# R62 admission receipt — 2026-10-31

Primary: `/root` (Luna). Sprint: `EFFECT-PERMISSION-INTERNAL-ROOT-POLICY/20261031-R62`. Status: admitted, exact continuation leases granted; workers launch only after this receipt and current state are frozen. Baseline and upstream tracking ref: `437716cc057368932fc233809960ae0f378f9e60` (`origin/yulang3`); previous R61 reviewed code checkpoint: `69570fe8e7fcc4f22154ddf0014a995cf074d7c6`.

Frozen contract `tasks/agent-loop/sprints/effect-permission-internal-root-policy-20261031-r62.md`, SHA-256 `682982c0ddd2a4251918362986c5563b352ea4a59843e124da451c795c683d57`.

## Selection and evidence

At R61 sprint end, the primary consulted the existing read-only `next_action_selector`. It recommended constructing R60/R61's remaining Internal-root policy reader from the same owning R45/R47 records. The primary adopted this bounded direction without changing the ongoing goal, source scope, accepted semantics, production authority, or original parent claims.

R61 status and independent review are archived at `tasks/agent-loop/history/effect-permission-bounded-ancestry-20261031-r61-outcome.md` (SHA-256 `c3376525f002a810b4d1158bf312a8b0681b847e3434bdaf3c3ee1f7d5c476ea`). Reviewer body SHA-256 `ce97b0ccaca0c1c0b36944d14f0d545d2212dcdb22c559c83dac46ac2d8c83fc`; primary placement SHA-256 `5d41d8bba8ab0c2b51e2b45d55111805098981e5f5a075c5958e4ce5bde9aff4`. The R61 Rust/Lean authors and reviewer returned STOPPED/WRITES STOPPED. The live roster was synchronized immediately before admission: no R61 worker or other active writer remained; historical completed workers remain historical. Unknown workers and their 12 quarantined path leases remain UNKNOWN/QUARANTINED.

The current scheduling snapshot retains all 32 pending items, every UNKNOWN observation, all 12 quarantines, and the released-capacity receipt. Resolved R61 author/reviewer rows and frozen file leases may be compacted only because the frozen outcome above authenticates them; their artifacts remain committed. No unknown path is reclaimed.

## Exact grants and resource ceiling

- Rust Luna/high: `/root/r62_rust`; 1,500 seconds; writes only `candidate_context.rs`, `candidate_receiver.rs`, and `tasks/agent-loop/inbox/effect-permission-internal-root-policy-r62-rust.md`.
- Constructive prover Sol/high: `/root/r62_proof`; 2,100 seconds; writes only `notes/theory/lean/YulangClosure/InternalRootPolicyR62.lean` and `tasks/agent-loop/inbox/effect-permission-internal-root-policy-r62-proof.md`.
- Fresh reviewer compiler_referee Sol/low: `/root/r62_review`; 1,200 seconds; launched only after both author lanes stop; writes only `tasks/agent-loop/inbox/effect-permission-internal-root-policy-r62-review.md`.
- Primary: 1,200 seconds total including 500 seconds closeout. Aggregate sprint cap 6,000 seconds. Astra 0. No descendants. No builds, tests, Cargo, formatter, Lake project edits, new environment, worktree, cache, target, scratch, or persistent service.

Frozen exact dependency hashes are in the contract. Both dirty source dependencies (`candidate_effect.rs`, `candidate_scheme.rs`) are pinned read-only and are not leases. Any input drift stops the affected lane before writes and returns to Luna. Authors must acknowledge their exact outputs and hashes before freeze; reviewer receives only the frozen snapshot. Luna alone stages/commits/pushes the exact reviewed outbound range.

Primary approval: admitted as an in-scope bounded research sprint, not as theorem-parent closure or production authorization. General Rust-to-Run, pointer/Nat, arbitrary resource/failure correspondence, original A/B and production remain OPEN.
