# Sprint R296 — source role obligation through provider Capture/FreshUse

Status: CHECKPOINTED_UNREVIEWED
Parent: R149 unchanged Types/Console sample and source/native proof, OPEN.
Authority: user-provided Y2 sample goal; Authoritative R149 design; top-level Simple-sub inference principles.
Mode: solo serial implementation because the user explicitly prohibited subagents. No independent review is claimed.

## Goal

Carry each retained declaration `where` clause into the candidate provider scheme with its subject bound to the exact already-interned annotation value row. Capture must retain that RowKey alongside the where-clause and subject/role source identities. Each FreshUse must preserve the corresponding row image through its existing row map. Do not enable declarations with `where` yet: role-name resolution to an authentic `SourceRoleId`, imported provider schemes, obligation solving, and type-directed implementation selection remain absent, so preflight remains fail-closed.

This is a concrete source-to-scheme lifecycle bridge, not a proof of inference soundness or a completed role solver.

## Exact write paths

- `crates/yu-solver/src/candidate_source.rs`: action for retained declaration prerequisites and row-binding dispatch.
- `crates/yu-solver/src/candidate_effect.rs`: resolve a subject only through the exact annotation-scope row already constructed for the declaration.
- `crates/yu-solver/src/candidate_scheme.rs`: per-definition source obligation storage, Graph Capture association and consistency checks against the graph's retained rows; FreshUse row-map correspondence; release temporary per-root carriers after Graph publication.
- `crates/yu-solver/src/shadow_apply.rs`: existing synthetic Graph constructors initialize the new empty obligation carrier.
- `tasks/agent-loop/current.json`, this contract, and one theory outcome note.

No HIR/syntax semantics, role selection, imported-HIR world, runtime, fixture, or sample changes in this sprint.

## Invariants and tests

- The subject variable is not re-created: it must resolve to the same `(AnnotationScope::Definition(root), spelling)` entry established by annotation construction.
- A malformed/unbound subject fails closed; no textual role-name comparison may choose an implementation.
- Capture associates each prerequisite with a graph-owned `RowKey` and exact where/subject/role `SourceNodeKey`s. The row must occur in the provider graph.
- FreshUse maps the associated graph row through the existing canonical row map; sibling uses retain independent images when normal generalization requires them.
- Existing candidate preflight still rejects nonempty where clauses until the obligation has an authentic role identity and consumer.
- Add focused regression coverage for retained identity, Capture row membership, and FreshUse mapping; run the smallest relevant solver tests plus `cargo check -p yu-playground` if time allows.

## Resource and convergence

Envelope: 900 seconds charged, no carryover. The identity-bound Capture/FreshUse carrier is implemented and focused checks pass. The role resolver, obligation discharge, imported provider scheme, source/native proof, and runtime remain outside this completed slice and stay OPEN. Solo primary wrote the code; no independent review is claimed. Commit/push the coherent slice and leave the worktree clean.

## Closure

R149 remains OPEN. This sprint cannot establish imported role identity, role implementation selection, multi-HIR inference, runtime output, whole-compiler proof, independent review, or sample success.


## Outcome receipt

`candidate_source` schedules each declaration prerequisite after annotation construction. The candidate effect owner reuses the exact named annotation row and retains all three parse-owned source identities. `GraphState` retains obligations by `DefinitionRootId`; Capture interns the obligation subject even when it is not reachable from the ordinary type shape and verifies that the graph owns that row. FreshUse retains the obligation ordinal to graph-row index relation through its existing row map. Retained allocation accounting is checked against a full recount.

Focused Capture/FreshUse test and existing fail-closed preflight test pass; `cargo check -p yu-playground`, sprint tooling check, 57 sprint tooling tests, and `git diff --check` pass. No public preflight was opened and no sample/runtime result is claimed. Exact next seam: resolve imported role identity and discharge the obligation in a shared imported-provider inference world. Parent R149 remains OPEN.
