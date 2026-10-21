# Sprint R241 — Live-root propagation and Apply correspondence

Status: ACTIVE_PROOF_SOURCE_AUDIT; Luna sole primary. No child workers.
Baseline: `bdf6d64a7` (`research/simple-sub-intrusion`), after corrected R240 partial freeze.

## Parent and fixed outcome

Parent: `notes/theory/2026-10-15-computation-forwarding-preservation.md` §§1, 6–7, SHA-256 `d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79`. Preserve its shared assignment, original formals, arbitrary finite chain length, repeated calls, simultaneous entries and finite-prefix quantifiers.

R239 conditional bound admission: `notes/theory/2026-10-21-r239-parent-instance-admission.md`, SHA-256 `8ecb68feb9177a78af6f5cfb47faa161081ee13bf27376c490c52caf96a9769f`. Corrected R240 route distinction: `notes/theory/2026-10-21-r240-source-instance-correspondence.md`, SHA-256 `11c53272e36569c0d58c3292c89a97866b8316bac8601304e2206ff6378fb959`.

Establish whether later source Function/bound admissions on an internal same-SCC provider's live root propagate through an already admitted target-root-to-use-row route. Then authenticate the typed Function comparison at that use against the same source Apply's argument effect, demanded AE/RE and output. Keep this live shared-root route separate from incoming graph capture/FreshUse routes and retained Local uses. Apply any proved constructor lemma to the fixed parent immediately. R71/R72 and the whole forwarding induction remain OPEN absent direct discharge.

## Method and falsifiers

Trace `route_candidate_open_use` → `route_internal_inner` → `route` → `constrain_live_value`; follow typed pair identity, retained adjacency, bound insertion/wakeup, worklist drain, and Function child dispatch. Compare admitting the route before provider facts with admitting provider facts before the route. Account for source occurrence/provenance, propagation transaction, rollback/retry and typed deduplication. Join the reached Function fields to the actual Apply occurrence and operands; a matching shape or endpoint alone is insufficient.

Falsify the propagation claim if a later required provider bound is not replayed to the existing use row, loses its source/provenance identity, or fails to dispatch the appropriate Function child. Falsify the Apply square if AE/RE or argument/output endpoints come from a different occurrence/interface or do not match the parent source quantities. Unresolved flags alone decide neither result.

Success is a constructor-derived incremental propagation invariant plus the authenticated Apply square, or the first exact failed wakeup/endpoint transition and its falsifier. No counterexample is assumed from R240's withdrawn stale-capture inference.

## Lanes, leases, limits

Serial Luna source/proof audit; no children or Astra. Read-only: no code changes, tests, builds or samples. Implementation remains `NO_SAFE_CODE_SLICE`; this packet grants no production authority or semantic change. Freeze when the exact invariant/square is established or falsified, at a material blocker/dependency/lease change, or at the budget boundary. Fresh independent review is required for promotion.

Exact write leases:
- `tasks/agent-loop/sprints/simple-sub-live-root-apply-correspondence-20261021-r241.md`
- `notes/theory/2026-10-21-r241-live-root-apply-correspondence.md`
- `tasks/agent-loop/current.json`

Resource cap: 900 seconds, serial; no carryover. Unknown legacy leases stay quarantined. No worker is recorded RUNNING without runtime evidence.

## Direct dependency pins

```text
d732980d7706538fe18b5d8de312e9a2b6367ec6638ab938b239d46272624e79  notes/theory/2026-10-15-computation-forwarding-preservation.md (§§1,6–7)
8ecb68feb9177a78af6f5cfb47faa161081ee13bf27376c490c52caf96a9769f  notes/theory/2026-10-21-r239-parent-instance-admission.md
11c53272e36569c0d58c3292c89a97866b8316bac8601304e2206ff6378fb959  notes/theory/2026-10-21-r240-source-instance-correspondence.md
135b72655d948d5035b21eaddce9fbeb0260c49bc3093e4bf2df73b03d88c4a1  crates/yu-solver/src/candidate_scheme.rs
90ed01915688b9c13c95593ddce296e7e3702a623e23dd4b9255d718b380a599  crates/yu-solver/src/candidate_source.rs
90665143f127394316b950d039fc498d460ac680df20b2387911a2fbdcaaeee1  crates/yu-solver/src/candidate_context.rs
5185481127cb619d66d49025c0a20ee7d829bc1e7a46072a05adecf4d22aa891  crates/yu-solver/src/candidate_extrusion.rs
45324aaec3825b1bf5cb15811ce309b8ff2dc020d5882383c0ed33d9d0b779f8  crates/yu-solver/src/candidate_effect.rs
285a39449360b050d7689f9e52f400b821e651ec9ce300bd14a1a3d9a9ab8b64  crates/yu-solver/src/lib.rs
50ad99c3afabb12816e9ec17fe50372bac758964699519d9ce6f1fc1f6649599  crates/yu-solver/src/shadow_apply.rs
```
