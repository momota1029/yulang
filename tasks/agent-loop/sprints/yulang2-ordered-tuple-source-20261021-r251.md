# R251 — retain ordered tuples in the local source carrier

Status: ACTIVE; solo primary implementation, no delegated workers.
Baseline: `5281c89fd`; original Yulang2 sample goal and R149 scope unchanged.
Resource envelope: 900 seconds, no carryover.

## Outcome

Resolve the parenthesized source mapping required to begin the R149 product path:

- `()` remains Unit.
- `(x)` remains Group.
- `(x,)` is a one-element Tuple.
- Two or more authentic direct parenthesized expression children form an
  ordered Tuple, whether separated by commas or accepted implicit delimited
  newlines. A trailing comma contributes no child.
- Recovery nodes and semicolon/error separator nodes remain unsupported.

Add an ordered `LocalSourceForm::Tuple` carrier that retains each direct child
under its original source identity and accounts for its dynamic index storage.
Do not claim canonical ordinary HIR, inference, graph export, runtime, closed
schemes, or Yulang2 sample acceptance from this carrier change.

## Exact write paths

- `crates/yu-hir/src/module/local_source.rs`
- `crates/yu-hir/src/tests/shadow_colon_application.rs`
- `crates/yu-hir/tests/ordinary_expression_source_carrier.rs`
- `tasks/agent-loop/sprints/yulang2-ordered-tuple-source-20261021-r251.md`
- `notes/theory/2026-10-21-r251-ordered-tuple-source.md`
- `tasks/agent-loop/current.json`

## Checks and falsifiers

Test Unit, Group, singleton tuple, arbitrary multi-element order, trailing
comma, implicit newline items, malformed recovery, and the adjacent colon-tail
case. Run `cargo test -p yu-hir`, focused source-carrier tests,
`rustfmt --check`; compare the result to `HEAD` before formatting so pre-existing
file drift does not trigger unrelated edits. Also run `git diff --check` and
`python3 tools/agent_sprint.py check`.

Falsifiers: a separator or recovery node is admitted as a value; tuple children
are missing, reordered, flattened, or counted from punctuation; Group or Unit
changes meaning; source occurrence ordering or retained-byte accounting omits
tuple storage. Ordinary HIR tuple lowering, inference consumers, evaluation,
imports, effects, closed public schemes, proofs, and both playground samples
remain open.
