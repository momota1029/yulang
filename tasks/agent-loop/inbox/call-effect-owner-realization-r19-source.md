# CALL-EFFECT-OWNER-REALIZATION/r19 — source lane STOP receipt

Assignment-ID: `CALL-EFFECT-OWNER-REALIZATION/r19-source`; handoff revision **1**. Author and worker: `/root/latent_demand_root_validation_r15_source` on a reused live handle; no descendants or coauthors. Requested model/effort **Sol/high**; observed effective model/effort **UNKNOWN**. Sole write lease: this handoff. Outcome class: **probe / input authentication failure**. No independent source review or proof is claimed.

## Frozen authority and exact mismatch

R19 contract `tasks/agent-loop/sprints/call-effect-owner-realization-20261028-r19.md` SHA-256 `09400d07a47cb48043983fa4ae43c41962a581a97a732d181c92cdd2a090e6bd7`; amendment 01 SHA-256 `9c90b318aaa322aade2440c9924a1e38d7d8e67b2e1e40fb27bd6c568904aa93`; manifest `tasks/agent-loop/sprints/call-effect-owner-realization-20261028-r19-inputs.json` SHA-256 `f287059a08410cf644644be214ba622de92d3e2d10c4897441cbb360c91ca22d`.

Read-only SHA-256 authentication found **one mismatch among 727 input files** and **zero mismatches among 11 parent artifacts**. The sole mismatch is the primary-owned, concurrently edited path:

```text
isolated/call-effect-owner-realization-r19/rust/crates/yu-solver/src/candidate_scheme.rs
manifest expected 3eb9ba3b414dd0e40f49957e0ee2b9de1ba21fd86dff718111d1b5030ccac6b7
observed          985ea301fbca632ecabe494f4324326759477608c0bf1a81e297c9e8b41cd37c
```

Luna confirmed that this arose from its concurrent primary edit and directed STOP under the R19 contract. I did not inspect the changed candidate body, substitute the R18 path or treat changing bytes as frozen source evidence. No source-body audit was completed.

## Parent application and missing evidence

The unchanged parent is `YulangClosure.SourceProblem.InferenceSoundness`: for all supported `s`, `xi`, generated `d` and solved `a`, construct a source judgment and `sameScoped` witness with the original shared `xi=(nu,K,D)`. The R19 contract also retains original source Call/shared-witness, lawful Generalize allocation, independent F1/FK1, foreign continuation, source/native correspondence, effect hygiene, principality, termination and production obligations. This lane establishes **none** of them. The first missing Call/effect owner-consumer equation is **UNRESOLVED by this lane** because its pinned Rust input was unavailable for a source-body audit. No four-row source/Rust join, zero/multiple same-route typed positive Function result, source-qualified counterexample, Lean theorem type or axiom audit is supplied.

Mutual TODO `R19-SOURCE-PIN-1` (Luna): reconcile this exact manifest-vs-current candidate hash and freeze an authorized dependency state before any new source audit. Falsifier for using the current manifest is any continued mismatch at this exact path. A later owner may then inspect the four R18 replay rows and actual Call/Generalize constructors under a newly authorized frozen input; this receipt grants no new lease or budget.

Checks/resources: SHA-256 read-only authentication only; zero builds, tests, Cargo, Lean, Git, source edits, external contact or descendants. Requested assignment grant 250 seconds; exact launch-relative elapsed, CPU and RSS are **UNKNOWN** to this leaf. All new/scratch paths: only this exact handoff, no scratch or generated outputs. Worker **STOPPED**, writes stopped, no unresolved descendant leases. Pending Luna intake; source/native/proof/production gates remain **OPEN**.
