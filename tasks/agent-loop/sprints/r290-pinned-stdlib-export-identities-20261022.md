# R290 — Retain pinned stdlib export syntax with source identities

Status: solo primary continuation; no subagents by user instruction.
Baseline: `5b275c889f841d82b24fe9b483914ecc1e84e606`.
Authority: R149 exact unchanged Types/Console sources and the unified design/proof companion; no semantic or production gate is expanded.

## Original outcome and target

Parent remains running the unchanged Yulang2 Types and Console playground samples with their specified public types and ordered output, then closing their source/native proof obligations. R289 indexed role and implementation identities across the exact 40-file source closure but did not retain top-level declarations or use trees.

R290 constructs a source-owned declaration/export-syntax index for pinned modules, including parse-owned direct declaration identities, syntactic public markers, complete use-tree node structure (paths, aliases, globs and groups), and recovery status. The pinned test ties the source facts for `Display`, `say`, and `println` to the observed prelude/io/console use declarations. The index does not semantically resolve these imports, grant visibility, or authenticate a compiler lookup. Keep source identities module-qualified and tied to exact pinned bytes.

## Proof and falsifiers

Use a finite structural traversal of each parsed declaration and use tree. By induction on the syntax-tree shape, the retained representation preserves each node's kind, order, exact source key, range, text, recovery bit, and syntactic public marker. This proves syntax retention only. Recovered facts remain visible as evidence and are explicitly marked; a later resolver must reject them on required lookup paths.

Fail closed on missing source keys, invalid source ranges/text, or duplicate identity assignment. This index does not decide missing/ambiguous imported names, private re-exports, or alias/glob expansion. Tests are implementation evidence for the exact source slice, not proof of conformance, candidate selection, execution, or the parent theorem.

## Boundaries and continuing work

No spelling-based builtin; no inference/runtime changes in this sprint. Do not assert role conformance or select an implementation. The next source-to-constraints seam is authenticated imports plus FieldTail/role-member resolution. Tuple source constraints, ordered tuple terms, public tuple projection, and runtime tuple values already exist and are not the current obstruction. Console host capability, full HIR publication, sample outputs, source/native correspondence, A/B proof and production remain OPEN.

Solo proof work establishes structural preservation for parsed use trees and records the exact R149 source facts; semantic export resolution and the source-to-constraints bridge remain open. Luna primary owns implementation, exact leases, integration and Git. No independent review runs in this solo session; preserve the result as unreviewed research evidence.

## Exact output leases and checks

`crates/yu-hir/src/module.rs`; new `crates/yu-hir/src/module/source_exports.rs`; `crates/yu-hir/src/shadow.rs`; `tools/inference-playground/src/pinned_stdlib.rs`; `tools/inference-playground/src/lib.rs`; this contract; `notes/theory/2026-10-22-r290-pinned-stdlib-export-identities.md`; `tasks/agent-loop/current.json`.

Use the exact pinned 40-source closure. Run focused and full playground library tests, `cargo check -p yu-hir`, `python3 tools/agent_sprint.py check`, and `git diff --check`. One heavyweight Cargo process at a time. Sprint cap: 900 seconds, no carryover. Stop at the source export-syntax evidence or an exact source/parser blocker; next consultation boundary is a cross-lane import/FieldTail integration seam.
