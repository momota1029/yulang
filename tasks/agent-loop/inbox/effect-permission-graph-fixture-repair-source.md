# Frozen source handoff — EFFECT-PERMISSION-GRAPH-FIXTURE-REPAIR/R102

Assignment-ID / revision: `effect-permission-graph-fixture-repair` / 1.
Parent: R102 admitted at `739cb332d`; observer candidate remains test-only/provisional and does not close the effect-hygiene theorem, source/native bridge, semantic gate, or production gate.
Baseline / exact source hash: `crates/yu-solver/src/shadow_apply.rs` baseline SHA-256 `c328e08662256b57ed9a31a4edd91e0832e9482cabb89952f204a89a78cf72ff`.
Exact writable paths: `crates/yu-solver/src/shadow_apply.rs` and this handoff only. No descendants.

## Change and source rationale

Added `lambda_argument_effects: Vec::new(),` to the two named test-only `Graph` initializers (`candidate_graph_row_hashing_matches_identity` and the adjacent row-representative identity fixture). Both initialize `nodes: Vec::new()` and contain no Function node. As pinned by the R102 contract, the field stores labels for actual Function nodes; ordinary capture starts it empty and adds labels only when it retains a Function node with its argument-effect child. Empty vectors are therefore the correct fixture state. No assertions, registrations, or semantics changed. No further owner is required.

## Checks and limits

Static inspection confirms both named `nodes: Vec::new()` initializers now include the empty field. No Cargo/build/test, Git command, scratch, environment change, or other path write. The pre-execution independent review and focused suite are primary-owned and NOT_RUN here. No theorem/source/native proof or production permission is claimed.

Final `shadow_apply.rs` SHA-256: `caeb837cd13b2e75e76fbed59dcc601e8c9d0a6a6a6f56f6959c0b0b9a98007f`.

All writes ceased before handoff hashing: **STOPPED**. No descendants or disposable scratch were created.
