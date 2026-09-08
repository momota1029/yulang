# Current task: complete and adopt the successor syntax phase

Updated: 2026-09-09. Branch: `yulang3`; do not modify frozen `main`.

## Objective and current authority

Prioritize syntax-owned public header/root connection and atomic legacy
implementation removal once the entry paths have sufficient validation functionality. Exhaustive
private owner completion is no longer an automatic cutover prerequisite;
deferred rows stay open. Private construction is not itself public cutover.

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
- `notes/design/2026-09-08-successor-public-cutover-priority-amendment.md`
  records the current ordering: build syntax header/root entries, exercise the
  actual public two-phase path, then remove the legacy implementation without fallback.

## Current gate and immediate next action

The user-authorized topology cleanup has no generic internal umbrella.
`SyntaxIn` in `cursor.rs` and `CstOutput` in `cst_output/` name the input and
output boundaries. Public exports, syntax behavior and test contracts are
unchanged. Dated design and daily records retain their historical paths;
current source links and test commands name their direct owners.

The Cast PatternIntroducer gate is complete under
`2026-09-09-successor-cast-pattern-introducer-current-item-recovery.md`.
Its Missing/Error sites now publish the existing Cast role with the required
open-parenthesis expectation; malformed retry to a bare Pattern no longer
duplicates Missing after Error. The sealed Error capability keeps nonempty
same-line EOF leading in the Error and extends its record/fact extent with it;
empty/newline EOF leading remains outside. Pattern value/close, target and
body remain separate open Cast owners. Cast: 12; direct Pattern/required-Type/
recovery-output: 84; package/format/diff passed. Benchmark use: zero.

The immediately following Cast Pattern absence gate is complete under
`2026-09-09-successor-cast-pattern-current-item-recovery.md`; local close and
colon/form handoff use the existing transition, while malformed Pattern input
remains Pattern-owned. Cast 13; direct cone 162; package/format/diff passed.

Cast Pattern's local closing-parenthesis gate is complete under
`2026-09-09-successor-cast-pattern-close-current-item-recovery.md`. Its two
Missing paths and bounded malformed run publish `CastPattern` closing-delimiter
records; local close keeps priority, outer boundaries remain unread, and Error
does not add a second Missing. Nonempty same-line EOF leading extends the Error
node, record, and fact together. Cast 14; direct cone 162; package/format/diff
passed. Benchmark use: zero.

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

The VirtualStatementBlock gate in
`2026-09-08-successor-virtual-statement-current-item-recovery.md` is
implemented. Its three raw sites now publish existing Statement Starter /
Separator records: required Statement, missing inter-Statement separator and
one maximal lexical Statement Error. Initial/internal Error leading remains
owned by that Error; retry/boundary leading and borrowed `}` remain pending for
the existing sequence/Literal owners. Fresh/shifted/frozen/seeded, UTF-8,
foreign-prefix, protected boundary and caller controls pass. The exact `"%{,`
literal record order is now Virtual child, interpolation close, terminator;
the pre-write specification audit derives that addition without changing CST
topology. M2 compiler/recovery and regression review found no production defect;
one caller-evidence repair adds actual Expression/Pattern/Rule string paths.
Yumark production convergence and its AST-product decision remain separate.

The If arm gate in `2026-09-08-successor-if-current-item-recovery.md` is
implemented. BodyIntroducer Missing now expects Colon; If/Elsif and Else inline
slots retain distinct Body/ElseBody Missing/Error records through a finite role
transport. The Error scan is sealed lexical-only and preserves existing leading,
boundary and retry handoff. A missing Condition suppresses only the absent
introducer path; after an actual colon, a separate Body slot remains required,
so `if :` and `if : @` publish Condition before Body recovery. The current
Condition boundary flag and indented Statement role remain unchanged. M2
compiler/recovery review found and closed that exact scope clarification;
regression review added actual delimiter-close and nested-dedent caller
evidence. Focused checks, package check, format and diff pass with zero
benchmark samples/processes. CaseLike remains a separate open owner.

The CaseLike structural gate in
`2026-09-08-successor-case-like-structural-current-item-recovery.md` is
implemented. Block and same-or-shallower Arm publish typed records; first arm
Pattern and Catch handler Pattern enter the existing Pattern kernel once with
their finite CaseLike role. Protected newline/close/fence Items now remain
pending at missing Block, while EOF leading remains Block-owned. Nested Pattern
and Type roles remain native. E12b/c/d/k exact fresh/shifted/frozen/seeded,
UTF-8/CRLF/fence, outer delimiter and following-statement controls pass.
Compiler/recovery and regression reviews found no defect. Arrow/Body, arm
Separator and Catch-close recovery remain separate open CaseLike owners.

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

The Role gate in `2026-09-08-successor-role-current-item-recovery.md` is
implemented. BodyIntroducer and inline Body now publish typed records with the
full ordered body-starter union and protected current-Item handoff; existing
Head Type and braced/indented/canonical Statement child ownership remains
unchanged. Role: 18; output: 4; package/format/diff and independent
specification/regression audits passed. The recorded `my role = value`
Statement baseline remains unrelated.

The Impl gate in `2026-09-08-successor-impl-current-item-recovery.md` is
implemented. BodyIntroducer and inline Body now publish typed recovery while
the first colon remains Description and the second colon is the Body phase.
Impl: 16; required Type: 5; indented/braced/normalized/output: 7/7/83/4;
package/format/diff and independent audits passed. The CRLF boundary repair
preserves shallow-newline current-Item handoff in fresh/frozen output.

The Act gate in `2026-09-08-successor-act-current-item-recovery.md` is
implemented. BodyIntroducer Error and inline Body now publish typed records;
bodyless terminal success remains recovery-free and attachment phases remain
unchanged. Act: 21; companion/indented/virtual/output: 23/7/9/4; package/
format/diff and independent audits passed. D9c's close-boundary zero-recovery
contract is pinned fresh/frozen.

Public-cutover foundations are implemented under
`2026-09-08-successor-public-cutover-priority-amendment.md`. HeaderInfo retains
private source identity and `parse_file` rejects a distinct source before
construction; scoped header reconciliation prevents full-only records from
consuming later frozen header IDs. The public syntax entry, public integration
and atomic legacy removal are complete.

The private Header/Root entry is implemented. Header discovery shares
Use and OperatorHeader construction, projects imports atomically, preserves
exact opaque-region boundaries and retains records for later reconciliation.
Root owns direct top-level topology, separators, pending/End handoff, scoped
header publication, and lexical delimiter-aware recovery. The root construction
review found and repaired binding-vs-operator prefix precedence and initial
indentation admission before closure. Header/Use/OperatorHeader/Root focused
filters pass 9/11/5/11; specification and regression review passed. At that
private checkpoint, HeaderInfo record transport, public adapter,
package/workspace validation and legacy deletion remained open.

The public adapter is now connected without fallback: `scan_header` constructs
syntax facts/records and `parse_file` passes the retained frozen header record
slice into `source_file` before diagnostics and conflict construction. Public
pair tests cover UTF-8/CRLF, header/full interleaving, imported/local conflict
provenance and fence recovery/continuation. A public fence fixture exposed and
repaired raw rejected-operator emission in Root Error. The accepted Yumark NUD
owner remains open; its current public proof is recovery/continuation only.
Final `yu-syntax`/workspace validation and atomic legacy implementation removal are
complete.

The first full successor-only lib run after removing the legacy tree passed
1057 tests with 3 failures and 1 ignored. Two are the recorded `my role =
value` and `(a +\nb)` baselines. The third,
`virtual_colon_errors_keep_close_eof_and_quoted_fence_records_frozen`, was
reproduced unchanged on detached pre-deletion `62e77291` (3 records versus
its stale expected 1); it is an unrelated pre-cutover baseline, not a deletion
regression. Expectations remain untouched. Syntax-reference paths were
historicalized and the final deletion review passed before `dfa481c4`.

Next, continue deferred Statement/declaration typed-recovery dependencies and
the accepted Yumark NUD/frame-pop owner. Those remain separate from the
completed public cutover; retain the current acceptance contracts and
effect-free optional entry. No benchmark sample/process has been used.
The old eighth-terminal proposal is not a required prerequisite. Public
dispatch is successor-only; the legacy implementation tree has been removed.

Post-cutover cleanup is complete. The inactive chasa cursor/scanner/CST stack
(`input.rs`, `sink.rs`, and `scan/**`) is gone; `recovery_record.rs` now owns
the typed recovery vocabulary; and the unchanged dynamic-operator judge is in
`lexical/operator_scan.rs`. The removed bridge had no public consumer. Test-only
seams live under `tests/`, about 1,400 further inactive private lines
are removed, and no module-wide `dead_code` suppression remains. The residual
annotations are variant/field/method-local contracts for retained Deferred,
ambient, pending-boundary, Rule and fence vocabulary. Production/test checks,
public pairs, focused recovery controls and the unrelated workspace check pass
with zero warnings; known unrelated full-lib baselines remain untouched.

## Syntax responsibility reconstitution

The user has directed a role-based reconstruction of the private syntax
implementation, not a cosmetic `rewrite` rename. This is a behavior-preserving topology
gate: preserve public `scan_header`/`parse_file`, accepted and malformed CST,
committed-recovery order and frozen reconciliation, exact Item/leading/source
handoff, and all existing source literals and semantic assertions.

The target separates lexical input (Item/current-Item/scanning/stops/fence),
committed output and emission, cursor state, expression policy, statement
admission, declaration families, and family-owned test suites. Extract shared
handoff, coordinate and lexical-stop operations from the Expression owner;
retain required-operand policy, NUD admission and tail control under
Expression. Do not add a generic `core`, `common`, `utils`, aggregate context,
or widened recovery capability. Item retains once-only leading emission and
the sealed Error-run/output protocol remains private.

The review also found a distinct existing contract defect: the For inline-body
caller selects `ForStatement(Body)`, but the common required-operand draft
hardcodes `ExpectedSyntax::Expression`. The authoritative operand contract
requires `ExpectedSyntax::Statement` for that finite role. Repair it as a
separate behavioral correction with Missing, Error and frozen-reconciliation
controls; do not preserve the existing assertion as a topology oracle.

Work in bounded stages: first establish these shared boundaries and declaration
and test-family topology, then split the remaining large family owners only
after their body-level responsibility review. Stop any extraction that changes
recovery ownership/order, Item emission, lexical-only observation, or a sealed
capability; such a change needs its own authority rather than an expectation
update.

Gate A is complete. `input`, `context`, `output`, `handoff`, `expression` and
`declaration` now express their actual ownership; `driver` no longer exists,
and `tests/mod.rs` is a catalogue with explicit support and declaration suites.
The For Body publication now maps only that role to `Statement`; direct and
actual-caller Missing/Error fresh/frozen controls preserve exact CST, Item
extents and `InLine` handoff. M2 conformance and regression review closed after
two test-only evidence repairs. The known unrelated `(a +\nb)` operator test
baseline remains unchanged. Next: body-level responsibility review before
splitting the still-large Expression, TypeExpression and Pattern owners.

Gate B1 is the reviewed Expression split. `expression/operator_chain.rs` owns
admitted NUD dispatch, prefix/infix/suffix recursion, ML application, tail
dispatch and the three-result continuation protocol. `expression/required_operand.rs`
owns the explicit-role mandatory-operand kernel, its boundary predicate, typed
Missing/Error mapping and sealed lexical Error retry. `expression/mod.rs` is
only their narrow façade. Do not split NUD from tail, reintroduce literal
scanning, or move the For Body mapping: those would sever established owner
cycles or contracts. TypeExpression and Pattern boundaries are deferred until
their full body reviews are converted to bounded gates.

Gate B1 is complete. The façade now declares only the two coherent owners;
all executable bodies are equivalent to the pre-split Expression implementation
apart from private child visibility and formatting. Focused handoff, operand,
tail, delimiter, normalized, output and frozen controls passed. Independent
regression review also confirmed the unchanged If/Case/For caller roles and
the retained For Body `Statement` mapping. The known operator baseline remains
unchanged.

Gate B2 is complete. The former mixed tail body is now a narrow
`expression/tails/mod.rs` façade over `colon.rs`, `with_body.rs`,
`delimited_tail.rs`, `fixed_access.rs`, and the only shared `inline_slot.rs`.
Colon owns its RHS/comma/outer-sequence recursion; With owns its introducer,
body and terminal; delimiter wrappers own their open-loop-finish-continuation
sequence; fixed access owns dot dispatch and Field/Path recovery. The shared
boundary predicate is accurately named `is_inline_slot_boundary`; the
misleading Colon-only name and wrapper are gone. Function bodies remain
equivalent apart from owner paths, visibility and that approved rename. M1
regression review found one duplicate lint attribute only; the one-line repair
is complete. Tails/delimiter/fixed-tail/Colon-With controls pass, while the
pre-existing `virtual_colon_errors_keep_close_eof_and_quoted_fence_records_frozen`
record mismatch remains excluded and unchanged. Package check, format and diff
checks pass; no benchmark sample/process was used. Next: prepare the scoped
successor Yumark document/fence construction gate; do not promote its test-only
cell witness directly.

## Crate-root syntax topology replacement

The user has rejected the generic `parser/` umbrella. Supersede the Gate A
private-tree placement without changing observable behavior: the generic
umbrella is removed rather than renamed or replaced with another
generic container. The `yu-syntax` crate root is the syntax-phase boundary;
its direct private children must name their own responsibility.

`operator.rs` becomes `operator_table.rs` for immutable declarations, fixities,
tries and table construction. Its separate lexical consumer becomes
`lexical/operator_scan.rs`; `lexical/stops.rs` owns finite stop masks and
`lexical/trivia.rs` owns source-only trivia observation. The remaining lexical
Item/current/scan/fence/position owners stay under `lexical/`. `cursor.rs`
owns live syntax/lex cursors and recovery state; `cst_output/` owns committed
green output and recovery reconciliation; `recovery_record.rs` owns the typed
recovery vocabulary. `ambient_claim.rs`, `sequence.rs` and `handoff.rs` are
direct narrowly named shared owners.

Grammar owners are direct siblings: `expression/`, `declaration/`,
`type_expr/`, `pattern/`, `literal/`, `rule/`, `statement.rs`, and
`virtual_statement_block.rs`. `header.rs` owns source-leading discovery and
`source_file.rs` owns top-level source progression/reconciliation. Internal
tests move to `tests/` with their existing role-named subtrees. `lib.rs` owns
only the public syntax boundary and direct private module declarations.

The move preserves public exports and all accepted/malformed CST, recovery,
frozen-record, current-Item, lexical-only and cost contracts. Do not merge the
operator table and lexical scanner, create a replacement umbrella, widen sealed
fields/capabilities, or change expectations to make paths compile. Root-level
sibling interfaces may become `pub(crate)` only where the former umbrella
ancestor supplied the same effective private-crate visibility; retain stricter
owner-local visibility everywhere else.

This topology replacement is complete. The independent regression review found
no Rust, visibility, public-boundary or owner-split defect; it found stale
current task/ledger locators only, which are corrected here and in the ledger.
Focused lexical/output/recovery/header/root/public-boundary controls, package
and workspace checks, dependency-graph, format and diff checks pass. The
documented `(a +\nb)` operator baseline remains unchanged. Benchmark use is
zero samples/processes.

The pre-Item scalar-frontier evidence plan and reverted primary-completion
proposal are superseded. Their historical evidence does not create a remaining
recovery-equality prerequisite.

## Following work and residuals

1. Migrate the remaining mutually recursive Expression/Pattern/Statement/
   declaration/literal owners. Local Type construction does not certify raw
   recovery still emitted by another owner. CaseLike structural, Arrow/Body,
   Separator and Catch-close slots are complete; continue with a distinct
   remaining owner rather than reopening that family wholesale. For Pattern,
   `in`, body-introducer and shallow Body slots are also complete.
   TypeDeclaration Name and equality DefinitionIntroducer are complete; its
   typed RHS remains a separate existing owner.
   Enum/Error Name and BodyIntroducer are complete owner-locally; Variant and
   companion/derives owners remain distinct.
   The shared declaration field owner is complete: it transports finite
   Struct/Enum/Error roles; publishes Field, FieldName, FieldColon,
   FieldSeparator, and construct-close records; and owns the neutral sequence
   in `declaration/fields.rs`. Its field lexical acquisition and boundaries no
   longer depend on the Struct owner. Continue with a distinct remaining
   declaration/companion or typed-output owner rather than reopening this gate.
2. Complete the typed-output owner ledger, actual embedded/header-full proof,
   and remaining public integration gates. T2/T3/T4 local evidence does not
   close aggregate O6 rows. Production Yumark and virtual-context adoption
   remain separate obligations.
3. The former six TypeDeclaration failures are resolved at the Type ownership
   boundary. Do not reopen their old malformed-output expectations as Yulang2
   compatibility requirements.

## Verification and environment

Use `cargo test -p yu-syntax --lib tests::type_expr:: -- --test-threads=1`
for Type construction. The leading-row gate also ran the known-small
`tests::normalized::normalized_type` and
`tests::normalized::ordinary_type_unmatched` filters. Use the focused
`tests::output::` and
`tests::recovery_output::` filters for output/RB invariants, then one
`cargo check -p yu-syntax`. Check inventory before broadening. Benchmark budget
for these bounded owner-local gates is zero samples/processes unless material
cost uncertainty requires a separately justified measurement.

The record-sequence gate's initial test build took 2m24s, with one sampled
rustc process around 1.8 GiB RSS and available memory; later focused rebuilds
took 38s and 31s. Test execution remained sub-second. Treat an active rebuild
separately from a running test suite; preserve the focused serial test budget.

`cargo xtask check-graph` is the available dependency-direction check, not a
syntax test runner. The workspace-local `crates/chasa-recover` already provides
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
