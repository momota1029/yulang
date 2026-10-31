# Sprint EFFECT-PERMISSION-ENTRY-UNIQUENESS/20261102-R124

Status: ADMITTED bounded immutable-source audit. The standing Rust/Lean soundness and effect-hygiene goal remains open.

## Objective

Determine whether actual admitted HIR ownership and SCC scheduling can deliver the same Lambda definition to `FormalEntry` more than once on the selected ordinary candidate path. Trace `SccPlan::build` partition/order through candidate execution and compare it with every Lambda-producing HIR route and every `Work::Visit` branch. Distinguish successful-publication soundness (R39's local guarded implication) from progress/admission behavior, where duplicate entry work could reject an otherwise ordinary input.

Success is a source-qualified derivation that the relevant schedule/visit multiplicity is unique, or an authentic duplicate/reuse counterexample and its first owner. Apply only that result to existing R39 premises; no new model, axiom, Lean declaration, source simulation or semantic change.

## Inputs and exact ownership

Baseline `yulang3` at `8914838a21ab2dcf62ccf14dddcec3ea91fd8446`. Manifest `effect-permission-entry-uniqueness-20261102-r124-inputs-r1.json` pins `scc.rs` plus the exact R123 HIR, candidate, source/effect and R39 blobs. Read immutable blobs with `git show`; do not read dirty worktree source.

- Source lane owns only `tasks/agent-loop/inbox/effect-permission-entry-uniqueness-r124-source.md`.
- `lean_prover` owns only `tasks/agent-loop/inbox/effect-permission-entry-uniqueness-r124-proof.md`, after source freeze.
- Luna owns contract, manifest, admission, review, current state, outcome and Git.

Trace SCC definition collection, partition coverage/disjointness/order, and actual execution loops. Trace authenticated HIR construction and source retention of Lambda paths, then all visit branches that can create `FormalEntry`. Stop at the first out-of-scope owner; do not assume the undo bridge or global all-path uniqueness.

Falsifiers: a shared Lambda definition across scheduled SCCs, repeatable `Work::Visit` for one registration, registration reuse that replays Entry, or any hidden path that bypasses exact source ownership. Malformed abstract inputs do not count as source counterexamples.

## Limits and review

No source edits, builds/tests/compiler/Lean/checker execution, storage/environment probes, caches/worktrees/copies, or dirty/quarantined source reads. No new tests are authorized. R111 and runtime quarantines remain unchanged. Preserve UNKNOWN observations and quarantined leases.

Caps: source 450s, proof 300s, fresh compiler referee 180s after both handoffs freeze, Luna 300s; total ≤1,230s; Astra 0. Review branch coverage, source reachability, SCC ownership, multiplicity, and exact distinction between progress and successful-publication soundness. Code integration remains **NO_SAFE_CODE_SLICE** unless a later reviewed gate changes that authority.
