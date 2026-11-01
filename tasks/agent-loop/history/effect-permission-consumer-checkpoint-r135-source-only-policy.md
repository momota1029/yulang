# R135 exact receiver source-only integration authorization

Authority: the user's explicit request to analyze Rust implementation and push
coherent reviewed work, carried by the R135 contract. This versioned policy
authorizes only the exact receiver target below as an uncompiled research
checkpoint.

- Integration baseline: `94414dd62e334ede7f58f8a8ab30f6145bd9c59e`.
- Sole source path: `crates/yu-solver/src/candidate_receiver.rs`.
- Baseline file SHA-256:
  `3ec1a45f5cdcfa5f5f28c2ef433c37d03322150a3155228f898e6fc5b77725cf`.
- Reviewed target: 296,602 bytes, SHA-256
  `335f5f2cd4841dd8288306623ee863606e355b9ceda6948ab6877d944bed3165`.
- Independent review:
  `tasks/agent-loop/history/effect-permission-consumer-checkpoint-20261102-r135-review.md`,
  PASS.
- Frozen candidate:
  `tasks/agent-loop/inbox/effect-permission-consumer-checkpoint-r135-source.md`,
  SHA-256 `44f47d5cbc18802f63d3a5c683ee59ea6691b7e5510a9add4443ff2b9483d1ff`.

Apply only the exact R117 then R119 reviewed receiver hunks from the frozen
handoff through the Git index. The target file is clean at the committed
baseline; preserve every other dirty or untracked path. No other source, test,
manifest, lockfile or artifact is included.

The source checkpoint remains uncompiled and untested. R111's private
compile/resource gate remains unmet and untouched. This grants no compiler,
Cargo, test, Lean, checker or production authority. Original A/B,
Rust-to-Lean correspondence and effect-hygiene gates remain OPEN.
