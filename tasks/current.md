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
- The later user instruction explicitly requests subagents. Use only the
  lightest scoped read-only reviewers or one owned implementation worker needed
  for a bounded gate; deterministic verification and honest reporting of review
  scope remain required.

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

Current gate: O3b SCC construction. The required-operand role/boundary gate in
`2026-09-08-successor-expression-operand-current-item-recovery.md` is now
implemented: the saved ` ]` witness is back in the build, the kernel publishes
typed Missing/Error records through its explicit caller role, and For's bypass
uses the same helper. Ordinary and sealed Error paths share one total lexical
Item scan. The focused expression-recovery, operator, If, CaseLike and For
filters plus `cargo check -p yu-syntax` pass; joint certification is still open.

The shared Expression delimiter gate in
`2026-09-08-successor-expression-delimited-current-item-recovery.md` is also
implemented. Parenthesized, Call, Index and Projection owners now select typed
Item/Separator/close roles through one finite descriptor. Close-only inherited
capabilities preserve nested caller closes without leaking ordinary caller
stops. The phase loop publishes maximal lexical Errors, records record-spread
RHS recovery, and makes Parenthesized semicolon a local Separator Error. New
fresh/frozen tests: 9; owners 23; tails 14; normalized 83; recovery output 25;
package check/format/diff pass. Specification and delta-regression audits found
no blocker. Colon/With remains a separate owner.

The Field/Path fixed-tail gate in
`2026-09-08-successor-expression-fixed-tail-current-item-recovery.md` is
implemented. FieldName/PathSegment now publish typed Identifier records; Error
runs are sealed lexical-only, Path preserves sigil retry Items and active
caller stops, and lone colon remains outer-owned. Focused recovery tests: 9;
tails 14; normalized 83; recovery output 25; package check/format/diff pass.
Specification and regression review found one frozen-cursor test-evidence gap,
closed by one bounded repair and delta review. No public dispatch changed.

The Colon/With inline gate in
`2026-09-08-successor-expression-colon-with-inline-current-item-recovery.md`
is implemented. Inline Rhs/InlineArgument and Introducer/Body slots publish
typed records; With now shares canonical literal-first Statement scanning with
its sealed retry. The focused filter passes 9; tails 14; normalized 83;
recovery output 25; package/format/diff pass. Spec/regression reviews found no
scoped defect. The pre-existing `my role = value` Statement assertion still
fails identically at baseline `de8e77f3`, so it remains unchanged.

The shared indented Statement recovery-role transport in
`2026-09-08-successor-expression-indented-statement-role-transport.md` is
implemented. Every direct indented caller now passes its finite existing role;
block-entry/child-slot Missing and sealed lexical Error records are typed, and
close/abstract-boundary handoff is protected. Focused recovery: 7; direct
caller/owner/output set: 227 (with the recorded baseline visibility-collision
test excluded); actual For: 12; package/format/diff pass. Specification/recovery
and regression audits passed. No benchmark process was used.

The current-depth Colon layout outer-sequence correction in
`2026-09-08-successor-expression-colon-layout-sequence-context.md` is
implemented. A private by-value owner context replaces comma-stop inference;
it covers the finite Expression/Statement, Virtual, RecordPattern-default and
Rule-list bridges. Ownerless Colon owns comma/qualifying newline arguments;
outer-owned Colon returns the whole boundary. Focused Colon: 12; Rule: 1;
literal/Yumark/Yumark-cell: 35/14/5; package/format/diff pass. The related
cone has 511 passes and the separately reproduced `(a +\nb)` baseline operator
mismatch. Spec/recovery and regression delta audits passed. No benchmark process
was used.

The non-Rule StringLiteral gate in
`2026-09-08-successor-string-literal-current-item-recovery.md` is implemented.
Terminator, escape and interpolation boundary sites publish six existing typed
Literal roles; UnicodeHex uses one sealed lexical Error and Virtual child
recovery remains separate. Focused: 8; literal/Pattern/Rule/Virtual/normalized/
recovery-output: 35/54/26/9/83/25; package/format/diff pass. Specification and
regression reviews passed. No benchmark process was used.

The Rule DSL literal gate in
`2026-09-08-successor-rule-literal-current-item-recovery.md` is implemented.
Ten Literal roles now publish typed records; Body/Paren newline stops precede
admission, and EOF-leading Missing anchors at successor. Rule: 35; literal:
35; normalized/recovery-output: 83/25; package/format/diff pass. Specification
and regression delta audits passed. No benchmark process was used.

The Rule ExpressionList gate in
`2026-09-08-successor-rule-expression-list-current-item-recovery.md` is
implemented. Dedicated Item/Separator and exact Parenthesis/Bracket close roles
now cover Rule bracket atoms, calls and indexes, while one-Item lexical Errors
and protected terminal Items remain unchanged. Repeated newline Item Missing
anchors use one coordinate-aware leading-prefix emission; the static audit
proved linear leading/fragment work without a benchmark. Rule: 40; focused
records: 5; recovery-output: 25; package/format/diff pass. Independent
specification/recovery and regression audits passed.

The braced canonical Statement sequence gate in
`2026-09-08-successor-braced-statement-sequence-current-item-recovery.md` is
implemented. Existing Statement/Separator/local-brace-close roles now publish
typed records; nonlocal closes stay protected. One repair makes newline-leading
comma/semicolon advance into the separator phase, and the old local-`]` test now
asserts the authorized handoff. Braced: 7; tails: 14; Act/For/Impl/Mod/Role:
15/12/11/9/15; package/format/diff pass. Specification/recovery and regression
delta audits passed; no benchmark process was used.

The Derives gate in `2026-09-08-successor-derives-current-item-recovery.md`
is implemented. Existing RoleReference/ViaTarget records now publish typed
output, and ViaTarget recovery returns protected contextual/newline Items before
identifier retry. Derives: 52; Type: 196; package/format/diff pass; M1
specification review passed. No benchmark process was used.

The declaration Variant gate in
`2026-09-08-successor-declaration-variant-current-item-recovery.md` is
implemented. Existing Item/Name/Separator/close roles now publish typed output;
retry leading is outside Error and terminal roles follow the lexical exit. One
repair added child ownership/effect-free evidence and aligned the authorized
trailing `| with` missing count. Variant/Enum/Error: 23/17/12; package/format/
diff pass; specification/regression delta audits passed.

The Binding gate in `2026-09-08-successor-binding-current-item-recovery.md`
is implemented. Binding now transports its initial Target role through Pattern
only for that required slot; Body publishes typed Missing/Error with lexical
retry and protected handoff. Binding/Pattern/indented/recovery-output:
11/54/7/25; package/format/diff pass; independent audits passed.

The declaration Companion gate in
`2026-09-08-successor-declaration-companion-current-item-recovery.md` is
implemented. All shared introducer/body/item/separator/close records are typed;
the selected colon-only Introducer expectation and protected retry leading are
covered across Struct/Type/Enum/Error/Act callers. Companion: 28; package/
format/diff and specification/regression audits passed.

The Struct header gate in
`2026-09-08-successor-struct-header-current-item-recovery.md` is implemented.
Name and BodyIntroducer now publish typed records with the existing ordered
starter union; header EOF/protected boundary ownership is explicit. Struct 28,
normalized Struct 4, package/format/diff and independent delta audits passed.

The Mod gate in `2026-09-08-successor-mod-current-item-recovery.md` is
implemented. Name/TestName/BodyIntroducer/Body now publish typed records with
sealed lexical retry and protected current-Item handoff. Only the first `test`
is a marker; the second name remains an Identifier. Mod: 13; indented: 7;
normalized: 83; package/format/diff and independent specification/regression
audits passed. The accepted test-only repair pins fresh/frozen boundary
payload, leading, line entry, suffix and fence coordinates.

Next, continue root Statement and declaration typed-recovery dependencies.
Root raw recovery, caller body-introducer bypasses,
Type/other-Pattern/Yumark production context ingress and aggregate/public
certification remain separate. Extend the same ledger; retain the current
acceptance contracts, effect-free optional entry and the atomic public cutover
boundary. No benchmark sample/process has been used.
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
