# R285 — Retain structured where-clause source owners

Status: active solo continuation under the user's unchanged Types/Console goal; dispatcher unavailable under the explicit no-subagent constraint.
Baseline: `fc3ed8385`; parent authority: R149 and unchanged Yulang2 sample bytes.

## Outcome

Extend R284's exact declaration-where evidence with parse-branded source keys, byte ranges and exact spelling for the constrained subject and role type expression. Preserve applied role syntax such as `Fold 'item` as one ordered source expression. Keep role/type lookup, semantic IDs, selection, constraint generation, production admission and proof open.

## Success and falsifiers

Single and repeated clauses retain exact clause/subject/role slices and source identities. Applied role expressions remain whole and ordered. Malformed/recovered or structurally unexpected clauses fail closed. No clause becomes a body expression; candidate preflight still rejects unresolved prerequisites.

## Exact paths

`crates/yu-hir/src/module/local_source.rs`; `crates/yu-hir/src/shadow.rs`; `crates/yu-solver/src/candidate_source.rs` tests; this contract; `notes/theory/2026-10-22-r285-structured-where-source-owners.md`; `tasks/agent-loop/current.json`.

## Verification and limits

Focused HIR and candidate tests, solver `--no-run`, sprint static check, tooling unittest, diff check. Solo-authored and unreviewed. This source representation is not semantic resolution, source/native proof, sample execution or production approval. Next critical path remains HIR role identity admission, then constraints and runtime consumers under R149.
