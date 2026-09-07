# Current task: complete and adopt the successor syntax parser

Updated: 2026-09-08. Branch: `yulang3`; do not modify frozen `main`.

## Objective and current authority

Complete `crates/yu-syntax/src/rewrite/` and replace the old parser through the
existing atomic public/root cutover. Private construction is not that cutover.

- `notes/design/2026-09-08-successor-recovery-authority-amendment.md` is the
  current acceptance/recovery authority. Yulang2 is reference evidence only
  for formally accepted input; choose explicit, reasonable successor recovery.
  The local `grammar/` implementation is older Yulang3, not Yulang2.
- Retain accepted syntax, source ownership, caller/fence boundaries,
  effect-free rejection, truthful typed records, structured reservation and
  emitted extent, and successor fresh/frozen/header-full consistency.
- The user authorizes recovery simplification and recommended design changes,
  documentation/environment maintenance, frequent coherent commits, and
  consideration of generally useful `chasa-recover` shorthand.
- The latest user instruction is direct primary-agent work without subagents.
  Do not restart agent panels merely to continue this task. Deterministic
  verification and honest reporting of review scope remain required.

## Current gate and immediate next action

The shared Call/Parenthesized/EffectRow ordinary-horizontal correction is
complete under the recovery authority amendment §4 and the retained P/E
addenda. Selected P/E/numeric-Call structured Error controls cover exact
records, fresh/frozen reconciliation, shifted origins, native outer closes,
prefix/recursive reservations and outer path continuation. Type tests: 124
passed; output: 4 passed; recovery output: 25 passed; package check passed.

The follow-up contextual-Type correction is complete. Same-line contextual
names remain accepted PathSegments and fresh Call arguments suspend the outer
declaration boundary; physical-newline contextual Items remain outer-owned.
Stale malformed controls now follow the approved horizontal owner and selected
streaming-boundary rules rather than old-parser recovery output. Type tests:
126 passed; TypeDeclaration: 39 passed; output: 4 passed; recovery output: 25
passed; package check passed.

The PV-owned typed migration is also complete under
`2026-09-08-successor-pv-current-item-recovery.md`. Every PV-owned recovery
node publishes its typed record; malformed tag/payload runs share one forward
operation and preserve explicit caller Items. Wrong-kind heads retain tight
Type tails inside one structured Error. Type tests: 134 passed; declaration,
output/RB and package checks remain green.

Parenthesized/EffectRow-owned construction is complete under
`2026-09-08-successor-pe-current-item-recovery.md`. Item, separator and close
sites now publish typed records; Error retries emit leading at the P/E owner,
preserve complete caller/fence Items, and recover unclaimed closes locally.
EffectRow activates only the approved OuterTypeApply provenance. Type tests:
141 passed; declaration: 39; output: 4; recovery output: 25; package check
passed. Call and structured PV contracts remain green.

Next: BracketRow item/separator/close, then the mandatory row arrow and leading
head. Retain accepted row grammar, attachment and newline/caller boundaries;
select a current-Item recovery rule explicitly before migrating the raw sites.
The old eighth-terminal proposal is not a required prerequisite.

The pre-Item scalar-frontier evidence plan and reverted primary-completion
proposal are superseded. Their historical evidence does not create a remaining
recovery-equality prerequisite.

## Following work and residuals

1. Complete the remaining Type-owned recovery sites (BracketRow, row arrow/head,
   record and forall). PV-local construction does not certify raw recovery
   still emitted by a nested non-PV owner.
2. Complete the typed-output owner ledger, actual embedded/header-full proof,
   and remaining public integration gates. T2/T3/T4 local evidence does not
   close aggregate O6 rows. Production Yumark and virtual-context adoption
   remain separate obligations.
3. The former six TypeDeclaration failures are resolved at the Type ownership
   boundary. Do not reopen their old malformed-output expectations as Yulang2
   compatibility requirements.

## Verification and environment

Use `cargo test -p yu-syntax --lib rewrite::tests::type_expr:: -- --test-threads=1`
for this gate, the focused `rewrite::tests::output::` and
`rewrite::tests::recovery_output::` filters for output/RB invariants, then one
`cargo check -p yu-syntax`. Check inventory before broadening. No benchmark is
needed for the bounded horizontal-gap branch; budget is zero samples/processes.

`cargo xtask check-graph` is the available dependency-direction check, not a
parser test runner. The workspace-local `crates/chasa-recover` already provides
`token`, `maybe`, and `with_str`; do not add generic API for owner-specific CST
or recovery policy. An API addition needs a concrete reusable operation across
independent callers, not just shorter syntax at one site.

## Navigation and history

- Design entry: `notes/design/INDEX.md`.
- Replacement gates: `notes/design/2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md`.
- Typed output: `notes/design/2026-09-06-successor-typed-output-recovery-amendment.md`.
- Current progress: `notes/progress/daily/2026-09-08.md`.
- The former 2,710-line task log is preserved at
  `notes/progress/rewrite-state-before-recovery-authority-2026-09-08.md`.
  Consult it for completed gates, older residual context, and syntax-reference
  site history; it is not an active queue or a source of new authority.
