# Detached contextual structural fold checkpoint

Status: reviewed M1 preparatory slice; numeric operation evaluation and all
source execution remain open
Baseline: `02613b7d1`
Authority: `notes/design/2026-10-10-contextual-attachment-admission-design.md`
§§3–6; confirmed append-only context-DAG construction invariant

## Change

`candidate_context::State` now provides an iterative postorder fold over the
retained `ContextExpr` DAG. The callback receives each exact construction token,
the exact expression, and ordered child results. Replay lower/upper order and
bracketing remain intact; shared children are evaluated once. Identity is a
terminal input. Malformed, self, forward, or unavailable context handles return
the existing internal availability failure.

The fold borrows context state immutably and keeps results local. It does not
resolve or execute source weights, validate or authorize entry certificates,
admit relations, consume filters, or connect to `candidate_context_execute` or
source-task construction. It is a structural prerequisite, not a numeric
context evaluator.

## Review and verification

Selected mode: M1. One independent compiler-referee review passed for finite
traversal, ordered replay, sharing, exact token preservation, malformed handle
behavior, and disconnection from source execution.

Focused verification passed:

- `RUSTC_WRAPPER= cargo test -q -p yu-solver --features shadow-apply-candidate --lib detached_fold_ --offline --jobs=1 -- --test-threads=1` — 3 passed, 571 filtered.
- `git diff --check -- crates/yu-solver/src/candidate_context.rs crates/yu-solver/src/candidate_context_tests.rs` — passed.

No broad suite, benchmark, or timing measurement ran. No performance budget was
consumed. The full M1 reviewer budget was consumed by the compiler-referee.

## Next sub-slice and limits

Implement exact numeric evaluation for the finite atom-set fragment while
keeping it detached from source construction, relation admission and live
execution. The approved gate requires unbounded natural counts; legacy Oracle
`u32` saturation is not a valid representation of that successor contract.
Use arbitrary-precision counts with exact add/compare/subtract and propagate
allocation failure through internal availability handling. Finite resolved
families and explicit `All` filters suffice for this bounded evaluator; do not
claim parameterized-family matching or residual/gamma support.

No source operation payload construction, Function-port propagation, filter
discharge, certificate authorization, recursive admission, full contextual
lifecycle, complete Call, full effect hygiene, soundness/principality,
production/default inference, or F5 cutover is closed by this checkpoint.
