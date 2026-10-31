# R98 admission — EFFECT-PERMISSION-RUST-OBSERVER-COMPILE-REPAIR

Admitted by Luna under the user's standing Rust/Lean goal continuation after R97 closed `CLOSED_FAILED` with Cargo exit 101 before tests and a fresh reviewer returned REJECT for missing protected assertions.

- Contract: `tasks/agent-loop/sprints/effect-permission-rust-observer-compile-repair-20261101-r98.md`
- Contract SHA-256: `50e0335389f9a059a21c6bfc92b7b5d056d29037ffcb937f1a963edaf646c887`
- Baseline: branch `yulang3`, HEAD/upstream `fd97f480fd1090f686907a44072ba736649ac5e5`
- Original parent: effect hygiene and source/native correspondence remain OPEN; this packet is test/diagnostic-only.
- Writable worker paths: `candidate_effect.rs`, `candidate_receiver.rs`, and one exact source handoff as listed in the contract. Primary-owned diagnostic and final verification logs are named there.
- Resources: implementer <=900s; independent reviewer <=500s; primary <=1,000s; total <=2,400s; two serial Cargo invocations maximum, each <=180s, one CPU, <=2 GiB RSS, <=8 GiB tmpfs artifacts; offline/locked; Astra 0.
- Stop conditions: durable first diagnostics must map required edits to leased files; no extra source owners, semantics, retries, persistent target fallback, or third invocation.
- Required final gate: restored protected nonrecursive assertions, successful focused Cargo test, fresh independent complete-diff PASS, then primary-only explicit staging and non-forced push.

R97's failed source bytes remain uncommitted. This admission does not approve them or close a proof/production gate.
