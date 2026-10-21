# R279 — parse Yulang2 `where` clause preambles

Status: CHECKPOINTED_UNREVIEWED; Luna-only parser implementation, no delegated workers.
Parent: unchanged Yulang2 Types/Console and broad playground sample goal under Authoritative R149.
Baseline: `e3ec875ce` on `research/simple-sub-intrusion`.
Authority: Authoritative R149 unchanged-source requirement; exact pinned stdlib census; Yulang2 typeclass constraints and reviewed unified design/proof documents.

## Outcome

Parse declaration-local Yulang2 `where` constraints that appear as the first
indented lines of a function binding body or `impl` body. Preserve each clause
as source-owned CST containing its `where` keyword, constrained type expression,
colon and required role expression. Repeated clauses remain ordered and bounded
to that declaration. Continue parsing the existing body after the prefix.

The required source forms include `where 'a: Display`, independent repeated
constraints such as `'ok` and `'err`, and applied role constraints such as
`where 'container: Fold 'item`. R149's exact fmt source currently reports 36
diagnostics after R278; the complete census must preserve its fourth category:
one `Missing` in `StringEscape`, in addition to 21 root `ErrorGroup`s, 7
`OperatorChain` `ErrorGroup`s and 7 missing `CaseArm`s. The target improvement
is to remove parser errors owned by valid where-clause preambles without
changing any source bytes or consuming following body statements.

## Limits and falsifiers

This sprint adds syntax representation only. It does not attach semantic bounds
to HIR, discharge role prerequisites, implement role selection, or claim sample
inference, execution, proof closure or production. Preserve the `[io]` open-row
interpretation `[io,'e]` from the governing proof documents.

Falsifiers: a supported pinned clause is rejected; a non-`where` first body
statement changes ownership; a malformed clause consumes the first body
statement or next declaration; repeated constraints reorder; ordinary nested
blocks accept declaration-only where prefixes; source bytes are lost; the exact
pinned source census gains unrelated diagnostics.

## Exact write paths

- `crates/yu-syntax/src/syntax_kind.rs`
- `crates/yu-syntax/src/declaration/binding.rs`
- `crates/yu-syntax/src/declaration/impl_tail.rs`
- `crates/yu-syntax/src/statement.rs`
- `crates/yu-syntax/src/tests/declaration/binding.rs`
- `crates/yu-syntax/src/tests/declaration/impl_decl.rs`
- `tools/inference-playground/src/lib.rs` (correct exact diagnostic partition only)
- `notes/theory/2026-10-21-r278-y2-dotted-pattern-target.md` (fourth category correction)
- `tasks/agent-loop/inbox/20261021-r278-y2-dotted-pattern-target.md` (fourth category correction)
- `tasks/current.md` (R278 census correction and R279 progress)
- this contract, `notes/design/2026-10-21-r279-y2-where-clause.md`,
  `notes/theory/2026-10-21-r279-y2-where-clause.md`,
  `tasks/agent-loop/inbox/20261021-r279-y2-where-clause.md`,
  `tasks/agent-loop/current.json`

If completing the parser requires any other code owner, stop at that seam and
revise the lease before editing. Keep the user-directed solo constraint; no
worker is delegated or treated as an independent reviewer.

## Verification and resources

Focused tests for binding and impl where preambles, malformed recovery and
following body/declaration ownership; exact pinned fmt census; `cargo check -p
yu-playground`; `python3 tools/agent_sprint.py check`; `git diff --check`. One
Cargo process at a time. No workspace-wide suite. Cap 900 seconds, no carryover.

Result: the exact pinned fmt census is 32 diagnostics (1 root `ErrorGroup`, 15
`OperatorChain` `ErrorGroup`, 15 missing `CaseArm`, 1 missing `StringEscape`).
Root errors fell from 21 to 1; nested case parsing now reports errors that the
old root recovery had swallowed. Six focused where tests, all 25 existing
`impl_decl` tests, all 16 existing binding tests, the pinned-source census and
the playground check pass. Static consistency and diff checks pass at close.
The user-directed solo constraint precluded independent review. HIR transport,
role prerequisites, role selection, remaining expression syntax, sample output,
source/native proof and production remain OPEN.
