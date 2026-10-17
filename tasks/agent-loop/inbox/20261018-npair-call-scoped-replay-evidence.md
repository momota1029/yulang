# Handoff: NPAIR-CALL-SCOPED-REPLAY-EVIDENCE-20261018 (rev 1)

Outcome: the reviewed scoped-query attempt did not produce call-scoped Replay evidence. Frozen query SHA-256 `5e4e4b9e0ff75bb4574c5856c7e0518bcb0cdbe32eda38344fbb1df1a50356d5`; temporary fixture SHA-256 `5a6627896bb5817b5e665fa531223755a3951bdb8fe3018ac09eb8d7691e1f52`. Fresh independent compiler review was CLEAN on those exact bytes and dependencies.

Single authorized command, invoked 2026-10-17 20:48:35 UTC with 172s measured cap remaining:

```text
timeout 120s cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
```

Exit 2; diagnostic: `STOPPED at candidate-solve: Collection(ComponentIdentityExhausted)`. Candidate solving stopped before returning `CandidateInference`, so there is no source-call record or scoped relation from this run. The call-to-relation/scope link and both ordered Replay `BoundKey`s are UNOBSERVED. Aggregate Replay remains unlinked. The prior native-demand lane's exit 101 is a separate old outcome and is not attributed to this command.

Exact current restored hashes: example `25bcd770ed40e10f0f2b621dfe63d26d71178430ae8f787deb346c6a087985ca`; fixture `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`. No production/compiler API change, no test/build retry, no Git operation, no scratch. The existing typed scoped lineage/observation API offers route, relation and scope identities only if solving succeeds; the scoped dependency surface is opaque `Debug`, and this lane did not establish a typed same-call relation to ordered Replay bounds.

Remaining exact TODO: diagnose candidate identity exhaustion at its owning path, without semantic changes; then establish the authenticated received Apply/source-call -> scoped relation/scope -> ordered Replay-bound correspondence. Preserve owner/Apply/callee/argument occurrence+pointer+source-key+scope checks. No inference of `eta`, `T_rho`, `At`, or parent closure (still 0).

Evidence note: `notes/progress/2026-10-18-npair-call-scoped-replay-evidence.md`. Requested Luna/high; observed UNKNOWN/UNKNOWN. This is a failed experimental observation, not proof or cutover authorization.
