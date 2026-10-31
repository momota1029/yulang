# R115 admission — EFFECT-PERMISSION-RUST-CONSUMER-PATH

Admitted after R114 closed INCOMPLETE. The standing Rust/Lean soundness and effect-hygiene goal remains active; the user explicitly renewed focus on analyzing Rust implementation and pushing coherent reviewed checkpoints.

Dispatcher selection: trace the pinned caller through residual suppression/publication because `lib.rs:18320` reaches `internal_formal_entry_permission` at `:18441`, and `candidate_receiver.rs` connects `current_internal_emission`, `provider_entry_certificate`, `complete_residual_plan`, and `publish_authenticated_residual`. This is a private experiment path, not ordinary compiler integration.

Fixed result is the exact source-owned defect and minimum statically reviewable candidate, with dependencies and counterexample, or an owner-specific `NO_SAFE_CODE_SLICE`. A correct path requires no change. No source edits or promotion are authorized. The proof lane waits because R114 did not establish authenticated source admission transport.

Baseline and four SHA-256 pins are in `tasks/agent-loop/sprints/effect-permission-rust-consumer-path-20261102-r115.md`. Existing R62 guard-order and R54 same-owner evidence are the only reused owner contracts. Dirty paths and quarantines remain untouched. R111 compile gate is unchanged; no resource/storage feasibility probes.
