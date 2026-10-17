# Npair call-scoped Replay evidence (2026-10-18)

## Frozen assignment and result

Sprint contract: `tasks/agent-loop/sprints/npair-written-conservative-lift-20261018.md`, assigned SHA-256 `84549487fc3ce3faa36764599a85a79e417a997455f57e2299b61b1df2452c5e` (the independent review receipt later recorded contract rev2 SHA `704a20cf457ed02ff07b52a399f6440c2fb145d02d6f840db10896f8d892c856`). This lane's exact query before its only Cargo invocation was SHA-256 `5e4e4b9e0ff75bb4574c5856c7e0518bcb0cdbe32eda38344fbb1df1a50356d5`; temporary fixture SHA-256 was `5a6627896bb5817b5e665fa531223755a3951bdb8fe3018ac09eb8d7691e1f52`. The compiler review was CLEAN for those exact bytes and the pinned dependencies.

The query used the existing `solve_scoped_experiment` route and intended to join the authenticated `received` source-call occurrence/index to typed scoped input routes, observations, relation IDs and protection scopes. The run stopped during candidate solving, before a `CandidateInference` was returned. Therefore this run produced no source-call record, scoped relation, or call-to-relation/scope link. Both ordered Replay `BoundKey`s and their same-call relation remain **UNOBSERVED**. No aggregate row was selected, no `Debug` text was parsed, and no `eta`, `T_rho`, or `At` claim follows.

## One authorized command

Measured lane start: 2026-10-17 20:43:57 UTC; cap 450s. Immediately before invocation, 2026-10-17 20:48:35 UTC: elapsed 278s, remaining 172s. Ran exactly once:

```text
timeout 120s cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
```

Exit status: **2**. The compiler/build step completed, then the harness reported:

```text
STOPPED at candidate-solve: Collection(ComponentIdentityExhausted)
```

No second command, test, build, probe, or compiler change was made. This exit 2 is the scoped-experiment attempt. It is distinct from the prior native-demand lane's exit 101; neither result is evidence of call-scoped Replay children.

## Restored files and proof boundary

After the run, the example was restored byte-for-byte to its pre-lane SHA-256 `25bcd770ed40e10f0f2b621dfe63d26d71178430ae8f787deb346c6a087985ca`; the fixture was restored byte-for-byte to SHA-256 `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`. No production/compiler files were changed.

The examined typed surface provides scoped input lineage and scoped observations (including typed route IDs, relation IDs and protection scopes), but this failed run did not produce values to join. The scoped dependency accessor is opaque `Debug`; no typed same-call join to the two ordered Replay bounds was exposed in the reviewed surface. The source proof obligation remains open: correlate the original Operation projection to the returned-provider Call action, then establish exact parent/source/native correspondence. Parent theorem closure: **0**. This is a failed experimental observation, not a proof or a semantic approval.

## Follow-up

The exact missing source/native TODO is to make candidate solving succeed for the fixture without changing semantics, then expose/establish a typed, authenticated same-call link from the received Apply/source-call through its scoped relation/scope to both ordered Replay `BoundKey`s. Keep the call identity exact (owner, Apply, callee, argument occurrence, pointer, source key and scope); do not infer it from aggregate Replay output. Any API gap or construction failure goes to the primary for authority review; this lane made no API change.

Handoff: `NPAIR-CALL-SCOPED-REPLAY-EVIDENCE-20261018`, revision 1. Requested model/effort: Luna/high. Observed model/effort: UNKNOWN/UNKNOWN. New paths: this note and its paired inbox handoff only. Disposable scratch: none. Stop receipt: source and fixture restored; only the leased evidence/handoff files were written; no Git operation.
