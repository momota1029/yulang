# R39 stage ledger

Sprint: `EFFECT-PERMISSION-COMPUTATION-ENTRY/20261031-R39`  
Contract SHA-256: `c0336d8077d763138c8a15f6dbb954595d11513908e3a1aa6e8ad8116eab70c1`  
Input manifest SHA-256: `e9b5643fdb925b0c45760c2e9bc930a82da215facc39ac66cdd2be271318efd1`  
Baseline: `06f1ce59eac7a953af18f27558ad0dd8b2a97237`.

## Stage 0 — admission

- The lightweight dispatcher selected the actual source obstruction: the admitted outer computation formal `[E] int` schedules `FormalEntry` and `FormalAnnotation`; the former currently links only an optional symbolic row and the latter reaches root `Int`. Neither retains a concrete computation-permission witness.
- R39 targets only witness retention in `candidate_formal_entry_annotation` and the state/accounting it owns. It does not add inflow, impose a closed bound, subtract an effect, or authenticate provider/Catch consumption.
- Rust baseline `candidate_effect.rs` is already dirty; its exact admitted bytes are pinned in the manifest. The writer's exact path lease preserves that prefix and permits only a review-separable R39 delta; no existing diff or unrelated path may be staged.
- The proof model must derive the retained witness from explicit owner/registration/annotation/row inputs; source correspondence is independently reviewed. Full rollback is not a goal under the governing top-level principles.
- Same checkout, no new environment/worktree/copy/scratch/build artifact, no Cargo/Lake/build/test/formatter. Budget and stop conditions are in the frozen contract and admission.

## Stage 1 — parallel lanes launched

- `/root/r39_rust` launched through registered `implementer`; `/root/r39_proof` launched through registered `lean_prover`. The collaboration roster synchronized after both launches and reported both RUNNING. Effective model/effort remains UNKNOWN for the proof worker; the implementation role requested Luna/high and does not imply effective runtime settings.
- Exact disjoint output leases are recorded in `current.json`. Only the implementer has the exact dirty `candidate_effect.rs` lease; proof writes only its standalone Lean module and handoff. Neither worker has Git or status-record ownership.
- The 6,000-second R39 envelope is reserved at admission; no transfer or renewal. No environment/worktree/build/cache/target/scratch is allowed. No compiler or tests have run.
