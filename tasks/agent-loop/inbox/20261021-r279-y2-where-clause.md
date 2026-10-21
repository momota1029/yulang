# R279 primary handoff — Yulang2 `where` clause syntax

Contract: `tasks/agent-loop/sprints/r279-y2-where-clause-syntax-20261021.md`.
Baseline: `e3ec875ce`; source authority: R149 and the pinned standard-library
bundle. User constraint: solo primary; no delegated workers.

R278 introduced `PatternFieldTail` and lowered pinned fmt syntax diagnostics
from 50 to 36. The rebuilt CLI and inventory identify all 36 as 21 root
`ErrorGroup`, 7 `OperatorChain` `ErrorGroup`, 7 `Missing` `CaseArm`, and 1
`Missing` `StringEscape`. The prior R278 subtotal omitted the final category;
R279 corrects it.

The parser now accepts declaration-local `where` preambles in function binding
and implementation bodies, preserving ordered type expressions around `:` and
resuming ordinary body parsing. Source examples include repeated independent
prerequisites and `Fold 'item`. The exact pinned fmt census is 32: 1 root
`ErrorGroup`, 15 `OperatorChain` `ErrorGroup`, 15 missing `CaseArm`, and 1
missing `StringEscape`. Root recovery fell from 21 to 1 while body parsing
exposed previously swallowed expression diagnostics. No HIR/solver semantics,
role lookup, runtime or proof closure is claimed. See
`notes/design/2026-10-21-r279-y2-where-clause.md` and
`notes/theory/2026-10-21-r279-y2-where-clause.md`.

Checks passed: 6 focused where tests, all 25 `impl_decl` tests, all 16 binding
tests, exact pinned fmt census, `cargo check -p yu-playground`, sprint static
check and `git diff --check`. No broad suite or independent review under the
user-directed solo constraint. R149 sample output and source/native proof
remain OPEN.
