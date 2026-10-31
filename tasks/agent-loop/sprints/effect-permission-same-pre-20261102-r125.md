# Sprint EFFECT-PERMISSION-SAME-PRE/20261102-R125

Status: ADMITTED bounded source-to-existing-R39 representation audit. The standing Rust/Lean soundness and effect-hygiene goal remains open.

## Objective

Determine whether one actual Rust graph, at a `FormalEntry` publication, yields the exact same PRE-state interpretation for both existing R39 `Inputs` and `State`. Trace actual owner lookup, key/registration membership, permission vector, row identities/order/duplicates, indexes and symbolic helper updates. Give concrete correspondence equations for the state before the guard, immediately before permission append, and immediately after append—or identify the first actual representation mismatch and its owner.

The mapping must preserve native typed identity and the exact same graph/vector witness. Do not use independent equal-looking snapshots, hash-map iteration order, integer-only identities, post-state facts to prove PRE conditions, or assumed simulation laws. Apply only existing R39 `prepare_exact` and `constructed_entry_publication`; add no model, theorem, axiom, or semantic restriction. Keep R121's consumer read as a later, separate edge.

## Exact inputs and leases

Baseline branch `yulang3`, commit `bf83716eea816536f3cc1d68b323d1567712dd38`. Manifest `effect-permission-same-pre-20261102-r125-inputs-r1.json` pins exact immutable commits/blob hashes for constructor, retained vectors, identity/equality, lookup, receiver inventory and helper updates, plus R39 and reviewed R124/R122 evidence. Every Rust read must use `git show`; dirty working copies are excluded.

- Source lane owns only `tasks/agent-loop/inbox/effect-permission-same-pre-r125-source.md`.
- `lean_prover` owns only `tasks/agent-loop/inbox/effect-permission-same-pre-r125-proof.md`, after the source handoff freezes.
- Luna owns contract, manifest, admission, review, current state, outcome and Git.

Trace `candidate_formal_entry_annotation` construction and publication, the retained registration/permission vector owner, source/HIR identity constructors and equality, `candidate_call` helpers and `candidate_receiver` consumer record. For each mapping equation, state the actual source location and exact data owner. Follow helpers that can mutate relevant state; do not invent vector provenance from matching contents or pointer starts.

Falsifiers: an owner lookup whose key differs from R39's registration, a permission/state vector from a different graph or allocation, identity equality that does not preserve the R39 coordinates, a helper that changes mapped state between guard and publication, or a collection ordering/duplicate/index mismatch. Arbitrary malformed states are not source counterexamples.

## Limits, review and resources

No source edits, builds/tests/compiler/Lean/checker execution, environment/storage probes, caches/worktrees/copies, or dirty/quarantined source reads. No new tests. R111 and runtime quarantines remain unchanged; preserve UNKNOWN observations and quarantined path leases.

Caps: source 450s, proof 300s, fresh compiler referee 180s after both outputs freeze, Luna 300s; total ≤1,230s; Astra 0. Reviewer checks same-graph identity, exact field/vector interpretation, guard-to-append state, helper updates, and no inferred bridge. Source integration remains **NO_SAFE_CODE_SLICE** unless a later independently reviewed gate changes that authority.
