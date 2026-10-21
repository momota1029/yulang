# R287 — Preserve role member and implementation source identities

Status: active solo continuation under R149; dispatcher lane omitted under the user's no-subagent instruction.
Baseline: `390609660`.

## Outcome

Extend R286's role declaration sidecar with direct member occurrences in source order, each keyed by its parent role identity and exact member `SourceNodeKey`. Add implementation declaration identity `(ModuleId, ImplDeclaration SourceNodeKey)`, retaining exact target head, role expression, optional body, and ordered member occurrences. Repeated spellings remain distinct source occurrences.

## Limits and falsifiers

Malformed/recovered or structurally unexpected declaration trees fail closed. Every retained range/text matches the original source. This is identity/provenance only: it does not resolve role/type names across imports, compare implementation heads, check members, select candidates, generate constraints, execute samples, or close proofs.

## Exact paths and checks

`crates/yu-hir/src/module.rs`; `crates/yu-hir/src/module/source_role.rs`; new `crates/yu-hir/src/module/source_impl.rs`; `crates/yu-hir/src/shadow.rs`; focused HIR tests; this contract; R287 note; current state. Verify focused role/impl source tests, solver `--no-run`, sprint check, tooling unittest, and diff check. Solo-authored and unreviewed.
