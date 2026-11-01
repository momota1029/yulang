# R133 admission

Admitted after the exact R132 adapter checkpoint and state synchronization were
pushed at `3429a3e5f` and `cd460e0fa`. The dispatcher selected a small concrete
fixture repair from the committed source: two existing `Graph` struct literals
in `shadow_apply.rs` omit the now-required `lambda_argument_effects` field.

Authority: the user's explicit ongoing request to analyze Rust implementation
and push coherent reviewed work, plus the standing Rust/Lean objective and
current sprint rules. Scope is limited to the exact two empty-vector field
initializers in the R133 target. The source working tree already contains
unrelated edits; the candidate must come from the pinned committed blob, be
reviewed as exact bytes, and later be applied to the index without staging that
worktree diff.

No compiler/Cargo/tests/Lean/checker/environment probe or source materialization
is authorized or needed for this bounded static packet. Runtime, A/B, consumer,
source/native, hygiene and production gates remain OPEN.
