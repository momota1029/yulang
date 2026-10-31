# R57 admission receipt

Luna admits `EFFECT-PERMISSION-PROVIDER-NATIVE-CONTEXT/20261031-R57`, contract revision 1.

- Branch/baseline: `yulang3` / `41a6bb84c`; working source pins are recorded in the contract.
- Contract SHA-256: `c6b995fe4437547e2aa3bae75933febb36b3621b06018ff17dcde13a8e52c5b6`.
- Exact Rust, proof and fresh-review output paths and 6,000-second aggregate budget are fixed by the contract.
- R47/R48/R49/R55 frozen modules, R56 reviewed receiver and R56 review are pinned there. Dirty read-only dependencies are retained as-is.
- Live roster synchronized: `/root/r52_rust`, `/root/r52_proof`, `/root/r37_inventory_review` are completed and available; no active R56 writer remains. They are assigned sequentially/parallel only on the disjoint exact leases above; reviewer begins after both write-stop receipts. Requested model/effort and actual launch/session metadata remain UNKNOWN until returned by tools.
- Existing UNKNOWN identities, quarantined leases, all 32 pending items, and R63 review quarantine are preserved. Completed STOPPED rows were archived in their linked frozen outcomes and removed from the compact current snapshot; no UNKNOWN lease was released.
- No builds, tests, type-checks, environment/cache/scratch/worktree creation are authorized.
- Current state transitions to R57 ADMITTED.


## Revision 2 — bounded Lean audit correction

The originally frozen revision 1 (`c6b995fe4437547e2aa3bae75933febb36b3621b06018ff17dcde13a8e52c5b6`) accidentally prohibited every type-check while assigning a constructive Lean proof. Before proof writes began, Luna amended only the proof verification method: existing Lean 4.35.0 stdin audits are permitted under the exact 1 CPU / `-j1 -M1024` / 120-second per invocation limit in revision 2. No Lake/Cargo/build/test, cache, scratch, environment or worktree is permitted. This satisfies the repository proof-check requirement without expanding source or semantics scope. Rust remains source-only.

Revision 2 contract SHA-256: `8f4d18e5954588ebd9cf9524e5bf5af56abc688aaac333d183de9a9e94a24576`.
