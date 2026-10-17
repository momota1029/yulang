# Npair scoped collection diagnostic (2026-10-18)

## Assignment and reviewed diagnostic target

Sprint: `npair-fixed-c-source-selection-scoped-collection-20261018`, revision 3, contract SHA-256 `6b3780d13b47ad5742b0cc375f803254d6d33a41c487543c88f3d625cc9d949f`; baseline `d9e6949a4cdc2d1899f55d5e7a75a014d4630606`. Parent `CHOOSE-SOURCE-2 / RECEIVE-NEGATIVE-PAIR` remains OPEN, closure 0.

The exact diagnostic target received fresh independent compiler review CLEAN before command 1. Reviewed hashes:

- `crates/yu-solver/src/candidate_source.rs`: `09a29794eafd2c93aac69b3335120878308a6804ebd6e95c2272556b744e943b`
- `crates/yu-solver/examples/research_source_registration.rs`: `f5c61bd5a4515545fad49bfc24158ef235c6ac2ebc6f00e15daabade394e79ad`
- temporary fixture: `7d7ad10d00773ecef583c53a1d546737dbf92daf75a9637f45c03798eb893fad`

The fixture had one temporary line, `my received = receive f0`. The harness checked the exact HIR Apply, callee and argument owner, occurrence, source key, parse owner and scopes. It called `CandidateInference::solve_scoped_experiment`. Under `YU_SCOPED_COLLECTION_DIAGNOSTIC=1`, the harness printed received-expression identities and the candidate collection diagnostic printed the caller file/line. Both diagnostic outputs are gated; the candidate behavior is unchanged.

## Command 1 and exact refusal

Immediately before the one command, at 2026-10-17 21:05:00 UTC, lane elapsed was 372s and remaining cap was 528s. Command:

```text
YU_SCOPED_COLLECTION_DIAGNOSTIC=1 timeout 120s cargo run --offline --manifest-path crates/yu-solver/Cargo.toml --example research_source_registration --features shadow-apply-candidate
```

Exit status: **2**. Cargo compilation completed; the harness stopped at candidate solving. Exact decisive output:

```text
candidate_collection.unavailable branch=crates/yu-solver/src/candidate_source.rs:1098:171
STOPPED at candidate-solve: Collection(ComponentIdentityExhausted)
```

At that branch, `emit_candidate_source` scans a scoped Apply callee spine through Group/Ascription/Block nodes. It refuses a terminal `LocalSourceForm::Name` resolved as `Local(_)` or `CatchBinder(_)`. The fixture's `receive` body contains `my g = f (); g ()`; the `g ()` Apply's callee is the local `g` name and reaches this refusal. This identifies a source-provenance admission branch, not an allocation failure or record/work limit. The existing error category still says `ComponentIdentityExhausted`; this diagnostic does not change that category or claim it is a fixed error. No `CandidateInference`, source-call, scoped relation or exact-call relation was returned.

## Existing identity route and missing edge

Within the same HIR-owned `LocalSource`, the Apply retains its exact `callee: LocalSourceIndex`. That index identifies the `Name(Local(local_id))` expression. `local_slots`, built from the same source's binding IDs, maps `local_id` to a slot; Finish emits `Action::Local { slot, occurrence }` for that exact name. The binding initializer is emitted as `Action::Install { slot, initializer endpoint, boundary }` for that same slot. Runtime local-use routing captures the installed graph and prepares `FreshUse` with the local-use occurrence's source region and scope remaps. This is the existing Install/Capture/FreshUse route.

There is no single explicit typed edge from the `ApplySourceInput` callee to the local slot/initializer and captured supplier. The route is structurally recoverable through exact owner + `LocalSourceIndex` + `HirLocalId` + action occurrence/slot. The current scoped callee guard deliberately rejects local aliases before admitting that reconstruction. A Local-only relaxation would change this candidate admission rule; this lane did not decide that the reconstructed route is a sufficient authenticated supplier, and made no correction. CatchBinder remains unsupported as well.

## Boundary, next step and resources

The exact received Apply was authenticated in HIR before candidate solving, but no candidate output exists to link it to a scoped relation/scope or ordered Replay BoundKeys. Those remain UNOBSERVED. No `eta`, `T_rho`, or `At` conclusion follows. Original theorem/source obligations remain open; parent closure remains 0.

Primary stop decision: 2026-10-17 21:09:41 UTC, lane elapsed 653s / 900s, remaining 247s. The worker froze both outputs and actually STOPPED at 21:10:24 UTC, elapsed 696s / 900s, remaining 204s. No repair or command 2/3 was authorized in this lane outcome: a rule decision on local-callee supplier identity would be needed, and the remaining cap did not support a fresh final review plus another command with the required >=120s guard. No semantic/API change, focused regression, retry, second build, or Git action was made.

Temporary fixture restored byte-for-byte: SHA-256 `969e20e0f38a2c341a96ff4fe07028bf567ca134e0fb24602fadf6e4c723d9c0`. Instrumented query hashes at stop remain as above. The `YU_SCOPED_COLLECTION_DIAGNOSTIC` instrumentation is provisional and reversible; falsifier: a future authorized exact-fixture run must report the same caller branch for the `g` local callee occurrence, or this attribution is withdrawn. Cleanup owner: Luna primary `/root`, after preserving/consuming this diagnostic evidence and before any promotion. It is not a production compiler change.

Next related step: decide and prove whether the existing structural local slot/Install/Capture/FreshUse chain is a sufficient scoped supplier for a local callee. If yes, define a narrow authenticated join and regression preserving exact owner, local ID, occurrence, initializer endpoint, scopes and fresh remaps; if not, keep the admission refusal and specify the missing source-owner rule. Parent owns that adjudication.

Requested model/effort: Luna/high. Observed model/effort: UNKNOWN/UNKNOWN. Handoff: `NPAIR-SCOPED-COLLECTION-REPAIR-20261018`, revision 1. New leased outputs: this note and the paired inbox. Disposable scratch: none. Worker writes stopped after freezing both outputs.
