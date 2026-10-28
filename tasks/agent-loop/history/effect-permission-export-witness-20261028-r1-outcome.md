# EFFECT-PERMISSION-EXPORT-WITNESS-20261028/r1 outcome

Disposition: **CLOSED_INCOMPLETE**. No source/native, parent, effect-hygiene, A/B, principality, termination or production gate is closed.

## Frozen evidence

Contract SHA-256: `06581e3741ddf8a330ba8c1975a35c80e2bda06ad8d00cff3030173c6b3a370f`.

Rust candidate hashes: `candidate_effect.rs` `881e2051caa2d4f8c7af617a3a135f85eba33bf3ad375c2fd33b2afd8233fb3e`; `candidate_scheme.rs` `ef58ad40c63e09f64a419558618a311f9adffa94931e49129c09d738dfb95ad6`. Final Rust handoff SHA `b88a3b6e84c885ddbc0cbde5c7511c6e6434320ac2caa3f46b7e554655dee49a`. Exactly one released feature-correct Cargo invocation exited 101 after 34.02 seconds, peak RSS 1,157,496 KiB, zero swaps. Three E0603 errors (`FormalCaptureTypedEvent` private across sibling module); zero selected tests ran. No retry. Raw receipt hashes are in the frozen handoff.

Lean decoder SHA `7c01a80c8d8e868d9349a3d02ec2d465ca976edfb515e04b57161b5c9744a67f`; proof handoff SHA `6813f9cd03d5b43b15fb2e9d7624da7d5dbb1cdd24bd5d49acaaf193c638232b`. Pinned Lean 4.35.0 completed all 13 type and transitive-axiom audits. Previous audited modules were reused exactly: 11 ConstructorRealization and 12 SourceOrigin audits; no fresh execution of those 23 is claimed. Failed first Lean check was preserved.

Fresh non-author read-only review receipt `tasks/agent-loop/inbox/effect-permission-export-witness-review.md`, SHA `9e4eb22d9bd8911880deb7eaf6a0119c66603991567dc45fadae7f4ba79711ac`. Reviewer verified final hashes and raw receipts and returned **BLOCKING + 2 MAJOR**:

- Blocking: compile failure above.
- Major: Rust join records canonical representative `q` but does not validate it against the actual captured node/row. Altering only `q` to `r` or another Effect row leaves assertions satisfied; the required `r → q` mutation is not rejected.
- Major: `Origin.concrete` is discarded. Export join compares occurrence/source row/path, and mutual equality of both exports allows the same incorrect concrete metadata in each.

Wrong owner wrapper, omitted second origin, and swapped sibling ports are rejected by Rust's static assertions. Lean's four fixed-mathematical-fixture mutation theorems reject the four mutations, but they are not decoded from the failed Rust run and do not establish native snapshot authenticity. All original/native/production boundaries remain OPEN.

## Next seam

Selector consultation proposed `EFFECT-PERMISSION-CANONICAL-EXPORT-20261028/r1`: narrowly expose the event type within the test-only internal module boundary; validate q from actual captured node/row identity with polarity and intern/export node equality; preserve and join each `Origin.concrete` to its actual exported permission; exercise genuine `r != q`; keep the checked decoder read-only; add a new Lean evidence-instantiation module only after Rust freezes. Fresh Cargo authority is required. Preserve all frozen failure artifacts and unrelated dirty/quarantined paths.
