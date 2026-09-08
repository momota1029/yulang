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

BracketRow-owned Item/Separator/Close construction is complete under
`2026-09-08-successor-bracket-row-current-item-recovery.md`. The shared
delimiter module has no raw Error/Missing constructors; P/E/B share the total
Item-error scan, B preserves its close-only retry and protects full caller/outer
Items. Type tests: 147; declaration: 39; output: 4; recovery output: 25; package
check passed.

BracketRowArrow construction is complete under
`2026-09-08-successor-bracket-arrow-current-item-recovery.md`. Its missing
and malformed sites are typed, malformed content retries an arrow/RHS without
a same-slot Missing cascade, and incomplete-row handoff preserves the separate
arrow slot. Type tests: 152; declaration: 39; output: 4; recovery output: 25;
package check passed.

LeadingEffectTypeHead construction is complete under
`2026-09-08-successor-leading-row-head-current-item-recovery.md`. One total
nested-Item Error run replaces the ordinary speculative and dedicated fenced
balanced-suffix scanners. Every head slot is typed; complete caller/newline/
fence Items remain pending. Type tests: 159; normalized Type/unmatched head:
27; declaration: 39; output: 4; recovery output: 25; package check passed.
The matrix's T7a/T7b EffectRow/leading-row spelling error has a recorded narrow
correction, not an embedded-certification claim.

Named-record field-internal construction is complete under
`2026-09-08-successor-record-field-current-item-recovery.md`: Name, Colon and
Type records, shared forward colon/RHS recovery and exact field-colon ownership.
The accepted empty-trivia nested record `{a:{b:B}}` now parses correctly;
actual PV RHS remains distinct. Type tests: 167; normalized Type/unmatched head:
27; declaration: 39; output: 4; recovery output: 25; package check passed.

Named-record whole-field, separator and close construction is complete under
`2026-09-08-successor-record-sequence-current-item-recovery.md`. A phase-aware
owner loop and one typed kind-matching run replace the raw recovery loops.
The malformed-name probe and immediate handoff preserve nested caller Items;
all record-owned recovery nodes are typed. Nine sequence tests pass, full
Type: 176; normalized Type/unmatched head: 27; declaration: 39; output: 4;
recovery output: 25; package check passed. The T5f EOF witness transcription
contradiction is corrected in the design without claiming embedded proof.

Forall-owned construction is complete under
`2026-09-08-successor-forall-current-item-recovery.md`: phase-owned forward
Errors replace the role lookahead, with typed Binder/Boundary/Colon/Body and
exact mandatory-colon ownership. Ten new typed tests passed; full Type: 186;
normalized Type/unmatched head: 27; declaration: 39; output: 4; recovery
output: 25; package check passed. No repair round was needed.

The shared required-Type Missing helper is implemented under
`2026-09-08-successor-required-type-missing-roles.md`. Production callers
explicitly select their own missing-slot role; malformed and nested Type
records remain unchanged. Type: 191 passed; package/format/diff checks passed.
The Type/PV implementation now has no raw recovery constructors; the remaining
SCC/global RB ledger and calling owners' bypass sites are still open.

Wider caller controls are now green under
`2026-09-08-successor-type-caller-conformance.md`: all five failures were traced
to stale expectations against the already-approved T3, inherited Type-ML, P/E
horizontal and record-field rules. Every original literal remains covered;
accepted tight-arrow/Call and nonhorizontal caller controls were added. The
expanded serial owner/output filters pass 432, with no failures or skips.

The tuple-field nonprogress path is fixed under
`2026-09-08-successor-required-type-equals-ownership.md`. An exact `=` is a Type
boundary only when the caller owns it; Pattern now forwards that ownership
explicitly. No field-loop workaround or new context API was needed. A bounded
single-callee test failed before and passed after the fix; capped tuple tests
and all 470 expanded owner/output tests pass. Package/format/diff checks pass.

The Type/PV callsite inventory is complete in
`notes/progress/successor-typed-recovery-ledger.md`: every publication helper,
all 28 TypeRole names (including the ApplyArgument non-recovery proof), close
owners and local RB controls are mapped. Matrix D4e now has an explicit
SD-T role correction without an embedded-certification claim. T3's stale
construction-suspension header is synchronized with its approved successor.

Pattern primary/symbol/alias/alternation typed construction is complete under
`2026-09-08-successor-pattern-primary-current-item-recovery.md`. Retry-leading
now belongs outside Error, malformed alias retry respects the layout/IN
boundary, and the RHS slot is explicitly AlternationRhs. No raw recovery
constructor remains in `pattern.rs`. All 33 Pattern tests and 477 expanded
owner/output tests and package/format/diff checks pass; the same accumulating
ledger includes its sites/RB controls. This is an O3b substep, not an
independently completed Pattern owner.

Pattern delimiter Missing/child-role publication is also complete under
`2026-09-08-successor-pattern-delimited-slot-publication.md`: five explicit
element/spread/nested roles, separator Missing, three close-Missing owners
and one guarded RecordFieldName non-recovery proof. Existing CST expectations
are unchanged. Pattern 40 and expanded owner/output 484 pass, along with
package/format/diff checks.

Pattern sequence/close Error construction is complete under
`2026-09-08-successor-pattern-sequence-current-item-recovery.md`: maximal
lexical runs, native wrong-close records and two scoped Record structured
roles. Invalid nested literals retain their own closes; accepted layout
literal elements now share canonical admission and maximal opener Items.
No raw Pattern Error remains. Pattern 48, expanded owner/output/literal/
normalized-Pattern 533, package/format/diff checks pass; one repair bundle.

Pattern default-Expression Missing construction is complete under
`2026-09-08-successor-pattern-default-expression-publication.md`: typed
RecordDefaultExpression, the required OperatorChain wrapper, and explicit
caller-close preservation in both field forms. There are now zero raw
Pattern-owned recovery constructors. Pattern 54, expanded related set 539,
package/format/diff checks pass. The exact-Equals lexical contract is unchanged;
rejected quote-adjacent sources remain covered separately from accepted defaults.

Current gate: O3b SCC construction. Continue with Expression's required
operand kernel (`driver::required_expr_item_normalized`) and its callers,
then tails/delimiters and literal/Statement/declaration dependencies. Map
the immediate roles and boundary rules before editing those owners. Extend the same ledger
and retain the existing joint construction/certification boundary.
The old eighth-terminal proposal is not a required prerequisite.
No public dispatch has been switched yet.

The pre-Item scalar-frontier evidence plan and reverted primary-completion
proposal are superseded. Their historical evidence does not create a remaining
recovery-equality prerequisite.

## Following work and residuals

1. Migrate the remaining mutually recursive Expression/Pattern/Statement/
   declaration/literal owners. Local Type construction does not certify raw
   recovery still emitted by another owner.
2. Complete the typed-output owner ledger, actual embedded/header-full proof,
   and remaining public integration gates. T2/T3/T4 local evidence does not
   close aggregate O6 rows. Production Yumark and virtual-context adoption
   remain separate obligations.
3. The former six TypeDeclaration failures are resolved at the Type ownership
   boundary. Do not reopen their old malformed-output expectations as Yulang2
   compatibility requirements.

## Verification and environment

Use `cargo test -p yu-syntax --lib rewrite::tests::type_expr:: -- --test-threads=1`
for Type construction. The leading-row gate also ran the known-small
`rewrite::tests::normalized::normalized_type` and
`rewrite::tests::normalized::ordinary_type_unmatched` filters. Use the focused
`rewrite::tests::output::` and
`rewrite::tests::recovery_output::` filters for output/RB invariants, then one
`cargo check -p yu-syntax`. Check inventory before broadening. Benchmark budget
for these bounded owner-local gates is zero samples/processes unless material
cost uncertainty requires a separately justified measurement.

The record-sequence gate's initial test build took 2m24s, with one sampled
rustc process around 1.8 GiB RSS and available memory; later focused rebuilds
took 38s and 31s. Test execution remained sub-second. Treat an active rebuild
separately from a running test suite; preserve the focused serial test budget.

`cargo xtask check-graph` is the available dependency-direction check, not a
parser test runner. The workspace-local `crates/chasa-recover` already provides
`token`, `maybe`, and `with_str`; do not add generic API for owner-specific CST
or recovery policy. An API addition needs a concrete reusable operation across
independent callers, not just shorter syntax at one site.

## Navigation and history

- Design entry: `notes/design/INDEX.md`.
- Replacement gates: `notes/design/2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md`.
- Typed output: `notes/design/2026-09-06-successor-typed-output-recovery-amendment.md`.
- Callsite/RB ledger: `notes/progress/successor-typed-recovery-ledger.md`.
- Current progress: `notes/progress/daily/2026-09-08.md`.
- The former 2,710-line task log is preserved at
  `notes/progress/rewrite-state-before-recovery-authority-2026-09-08.md`.
  Consult it for completed gates, older residual context, and syntax-reference
  site history; it is not an active queue or a source of new authority.
