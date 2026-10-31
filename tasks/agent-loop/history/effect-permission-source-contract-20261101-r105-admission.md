# R105 admission

Admitted by Luna under the continuing user-authorized Rust/Lean research goal
after R104 closed with Lean's bounded gate passed and Rust source promotion
failed. Contract SHA-256
`7285a5d8cb6ca8d39c8f0427278c633ecccaf12d8591e9109825c7afce162e4d`:
`tasks/agent-loop/sprints/effect-permission-source-contract-20261101-r105.md`.
Baseline commit: `d19315503f911c615d4d3a9ab9329146f757acbf`.

The dispatcher selected source-contract adjudication and one valid Rust
permission path, paired with a logical-owner route bridge. The named-header
fixture mismatch is a hypothesis only. R105 grants no semantic change or
production implementation authority. Rust writes are limited to test code in
`candidate_effect.rs` and its one handoff; Lean writes are limited to the new
bridge module and its one handoff. Fresh independent reviews precede any
execution or integration.

The sprint envelope is 2,400 seconds, Astra 0, with at most one reviewed Cargo
invocation using a cleaned `/dev/shm` target and at most one pinned flattened
Lean invocation. No persistent worktree, target, cache or new dependency.
