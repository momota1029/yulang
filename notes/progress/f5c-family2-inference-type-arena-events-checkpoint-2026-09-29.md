# F5c family-2 inference arena event checkpoint

Status: §34 family-2 physical owner events and replay are implemented and
independently reviewed in the `f5c_resource_probe` configuration. The
all-eight-family event and measurement gates remain open. No test, matrix row,
preflight, benchmark, or scale process ran.

Authority: F5 §§26/34 in the
[`F5 foundation`](../design/2026-09-21-f5-general-function-scheme-foundation-draft.md),
the Authoritative
[`no-numeric-resource-cap addendum`](../design/2026-09-28-f5c-no-numeric-resource-caps-addendum.md),
and the
[`remaining owner-event map`](f5c-remaining-owner-event-map-2026-09-29.md).

## Verified boundary

This checkpoint covers six §34 family-2 matrix lanes 18–23:

| Lane | Physical owner | Owner lifecycle |
|---:|---|---|
| 18 | One fixed 256-slot `TermPage` backing per page | Each allocation gets a unique ID before page claim; RELEASE follows initialized-node and Box destruction, including a temporary page whose claim fails. |
| 19 | `BranchTermArena.pages` descriptor Vec | One stable ID tracks requested length and actual capacity. Page truncation releases page backings but retains Vec capacity. |
| 20 | `page_positions` map | Capacity growth and shape changes are observed; rollback removes entries without releasing retained capacity. |
| 21 | `positions` interner map | Capacity growth and shape changes are observed; rollback removes entries without releasing retained capacity. |
| 22 | `TermJournal.interned` Vec | The ID follows the same journal through active/spare moves; logical clear changes shape only. |
| 23 | `TermJournal.claimed_pages` Vec | The ID follows the same journal through active/spare moves; logical clear changes shape only. |

The row records the `FinishOutput` event checkpoint and same-time event peak.
The store then moves into `SolvedModule` with each retained owner ID preserved;
the checker requires the exact same-ID transfer and permits those arena owners
to remain live at EOF. The fixed page event also captures a transient allocation
and release if `claim_page` fails after backing allocation.

Family 1, family 3, family 4, and §34 family 7 (sidecar name `family6`) retain
their separate event checkpoints. The six-buffer `FlatDraft` carrier and
same-ID staged transfer remain the earlier separate checkpoint. This family-2
slice does not close families 5, 6, or 8 and does not authorize matrix runs.

## Changed paths and diff units

- `crates/yu-solver/src/term.rs`: six physical lane owners, current-length and
  capacity observation, journal ID stability, page allocation/drop ownership,
  and FinishOutput store transfer.
- `crates/yu-solver/src/f5c_draft_heap.rs`: family-2 kinds 571–576, checked
  current/peak aggregation, same-ID transfer, and checkpoint emission.
- `crates/yu-solver/src/lib.rs`: reconcile family-2 current totals and event
  peak with physical lane samples and emit the terminal checkpoint.
- `crates/yu-solver/src/tests/f5c_resource_probe.rs`: add the family-2 event
  capacity, retained-byte, and peak tuple to matrix rows.
- `tools/check_f5c_resource_matrix.py`: replay family 2, reconcile six row
  lanes and event peak, and verify terminal transfers and EOF retention.

## Review and verification

Selected M2 with `spec_auditor` and `compiler_referee`. Specification review
found no finding in the scoped contract. Compiler review found one major issue:
the original page RELEASE preceded backing deallocation. The repair moved the
release into an owner token declared after the Box; a focused
`compiler_referee` delta review confirmed the Box and initialized nodes are
dropped before RELEASE. Other reviewed reserve, claim-failure, rollback,
journal-move, finish-transfer, and replay paths had no concrete finding.

Compile-only checks passed:

- `RUSTC_WRAPPER= cargo check -p yu-solver --tests --features f5c_resource_probe`
- `RUSTC_WRAPPER= cargo check -p yu-solver --tests`
- `RUSTC_WRAPPER= cargo check -p yu-solver`
- `python3 -c 'import ast, pathlib; ast.parse(pathlib.Path("tools/check_f5c_resource_matrix.py").read_text())'`
- `git diff --check`

The first feature-enabled compile invocation without `RUSTC_WRAPPER=` stopped
before compilation when sccache returned EPERM; rerunning with the wrapper
disabled passed. No tests, matrix, preflight, benchmark, or scale process ran;
measurement budget consumed: zero. The next mapped slice is §34 family 8
`instantiation_substitution`; families 5, 6, and 8 still need event coverage
before a fresh diagnostic plan review and any matrix execution.
