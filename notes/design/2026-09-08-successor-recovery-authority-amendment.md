# Accepted-input compatibility and successor recovery authority

Status: Authoritative; §4 private delimiter integration complete

Date: 2026-09-08

Scope: compatibility and recovery authority for the ongoing `yu-syntax`
replacement; the private shared-delimiter integration gate in §4

Drafted-by: primary from independent architect analysis

Reviewed-by: independent compiler/recovery and specification review of the
authority split and retained invariants; final numeric contract completed by
the primary after the user's explicit no-subagent direction

Approved-by: user, through the explicit recovery-selection and simplification
delegation quoted below

Approved-at: 2026-09-08

User authority: the user explicitly directed the following, then requested
continuation. Earlier delegation also permits recommended choices and asks for
frequent coherent commits.

> Yulang2で参考にして良いのは正式な受理データまでで，回復は妥当なものを選んでくれればいいです．

The user subsequently confirmed that recovery may be simplified and its design
changed to follow this criterion, and requested a documentation/environment
audit and consideration of generally useful `chasa-recover` shorthand. Those
follow-ups do not make a parser-specific recovery policy a generic library API.

The acceptance/recovery distinction and delegation are already decided. The
primary records the concrete rule before implementation; another request for
the same policy approval is not required. See §5 for the review boundary.

## 1. Compatibility authority

Yulang2 supplies evidence only for formally accepted input and its recorded
accepted products, subject to explicit Yulang3 language decisions. Its recovery
output, diagnostic locations on syntactically malformed input, and accidental
acceptance after recovery do not determine successor recovery.

The existing `grammar/` parser in this workspace is the older Yulang3 parser.
The recently collected `grammar/type_expr.rs` recovery observations are not
Yulang2 observations. Applying the user's recovery-selection delegation to the
replacement also removes reproduction of those malformed outputs as a default
successor completion requirement. Existing observations remain useful historical
tests of the parser that produced them.

An accepted-source control must name its grammar/environment and authoritative
language or recorded acceptance basis. Parser success alone is insufficient:
complete consumption and absence of syntactic recovery, including incomplete
AST slots or untyped recovery nodes, must be established where observable.
Later name/type/semantic diagnostics do not by themselves make syntax invalid.
If a corpus record does not distinguish these phases, classify it as unknown
until its acceptance basis is checked; do not infer it from successor output.

Accepted syntax, grouping, operator behavior, applicable AST projections,
source text, header facts, and public products retain their independently
approved contracts. Yulang2 acceptance is not an oracle for a Yulang3-specific
CST representation that Yulang2 never exposed.

## 2. Supersession and retained contracts

This amendment supersedes only legacy-malformed-output equality and the work
whose sole purpose is to obtain that equality:

- The rewrite plan `2026-09-02-yu-syntax-recursive-descent-rewrite-plan.md`:
  its authority preamble, §2 items 1–3 and adoption-matrix paragraph, the §5
  common acceptance template/coverage ledger, and Gate 9, only where they
  require legacy malformed CST, AST, recovery fields, IDs, or continuation
  results as successor output. Accepted-input contracts remain in force.
- The Gate 3b adoption matrix as inherited by the rewrite: its owner/slot
  inventory, rollback, real embedded execution, and following-owner evidence
  remain required. An owner gate may replace its legacy malformed result with
  a documented, independently reviewed successor result under the user's
  delegation. It may not silently drop the owner/slot or declare it complete.
- `2026-09-07-successor-pv-scalar-frontier-evidence-plan.md` §§3–5: completing
  the remaining legacy matrix and designing a pre-Item scalar observer are no
  longer prerequisites to recovery construction. Collected facts remain
  historical observations, including the leading-BracketRow assertion failure.
- `2026-09-07-successor-pv-payload-admission-capability-amendment.md` and the
  payload-adapter blockage in the wrong-kind-primary-completion amendment:
  matching legacy conditional retry or splitting a scanned `::` solely for
  that match is no longer required. Neither an unreviewed scalar capability
  nor the reverted primary-completion candidate is thereby implemented.
- `2026-09-07-successor-pv-wrong-kind-primary-completion-amendment.md` §2's
  return-before-external-tail rule and §3(2)'s numeric-head/separate-payload
  requirement are superseded only for §4's numeric head with an external Call:
  that Call may remain inside the one successor TagName Error. The numeric
  Call exclusion in the E-extent addendum §§1, 4–5 is superseded to the same
  limited extent. Structured reservation, emitted extent, native PV close,
  frozen/rejection contracts, and nonnumeric/accepted controls remain in force.
  This does not implement the primary-completion route or decide its other
  external-tail cases.
- The P/E structured-extent addenda and shared-delimiter integration block:
  legacy equality, exhaustive legacy-carrier exploration, and numeric apparent
  Call/PV recovery disagreement are not integration vetoes. Their existing
  successor ownership, emitted-extent, ordering, and boundary rules continue
  to govern the bounded gate in §4.
- The optional Yulang2 syntax-recovery diagnostic anchor and corresponding
  comparison step in `2026-08-20-phase2-parser-fixture-schema.md` no longer
  prescribe successor syntax recovery. The schema's Yulang3 phase products
  and internal identity/parity validation remain required. This does not
  modify unrelated semantic diagnostic or whole-compiler corpus contracts.

The typed-output amendment §§3–6, structured reservation and extent-validation
amendments, current-Item ownership, effect-free rejection, frozen-header
reconciliation, source/fence boundaries, and atomic root cutover remain in
force. An existing successor test does not become editable merely because it
contains malformed source: determine whether it asserts one of these retained
invariants or a superseded legacy result before changing it.

## 3. Successor recovery criteria

Recovery is specified by the immediate grammar owner using its current Item
and explicit caller context. Committed malformed input moves forward to a
recognized local continuation or protected caller boundary. Any new concrete
owner policy must state the failing slot, consumed extent, continuation and
termination rule before its expectations are written.

Every such choice must preserve:

1. Source bytes exactly once and a balanced CST; caller-owned closes, layout
   boundaries, fences and accepted companions remain available to their owners.
2. Progress: each recovery iteration consumes an Item/bytes or returns it to
   an enclosing owner. Malformed user source must not itself cause a panic.
3. Truthful typed recovery: Missing is zero-width; Error is nonempty; ranges,
   unexpected facts and expectations describe the actual slot and owned
   extent under the existing sealed emission contracts.
4. Deterministic records and successor fresh/frozen/header-full consistency.
   Frozen IDs are retained within that successor parse/revision contract;
   their numerical equality with another parser version is not required.
5. Effect-free rejection and the existing discard-only behavior for violated
   committed frozen-output contracts. The no-user-input-panic requirement does
   not turn mismatched frozen metadata into an accepted parse result.
6. One-forward ownership and `O(bytes + structural work)`: no replay, retained
   malformed-run cache, post-hoc CST splitting, speculative output, or source
   rescanning introduced solely to copy legacy recovery.

Test selected examples of the chosen rule and its affected boundaries, plus
accepted controls. Exact fields and topology remain appropriate when they
express that rule. Exhaustive old-parser output tables are not a prerequisite.
Existing legacy tests are retained; no blanket deletion or expectation rewrite
is authorized. Public fixtures change only with a recorded owner-level reason
and pre-write specification audit.

## 4. Next bounded gate: shared delimiter integration

Retain the already approved ordinary-horizontal rule: a committed Call,
ParenthesizedGroup or EffectRow owns eligible horizontal trivia at its raw
caller/outer boundary; the raw boundary stays pending. Fresh slots emit the
existing Item-Missing then close-Missing nodes; after-item slots emit the
existing close-Missing node. Preserve owner-specific typed publication, lexical
`else` admission, abstract-boundary handoff and nonhorizontal behavior.

Only `rewrite/type_expr/delimited.rs` and its focused successor tests are
implementation targets. Validate:

- initial, post-comma/semicolon and post-item ownership; matching local close;
  actual outer-close continuation; nonhorizontal and explicit caller controls;
- emitted structured TagName Error extents, nested P/E ancestry, actual PV
  close exclusion, ordered records, fresh/frozen equality and returned Item
  state; include prefix and recursive carriers as reservation controls;
- numeric apparent Call under a malformed PV tag as the selected
  successor-owned structured recovery unit specified below;
- accepted Type/PV controls and the existing RB-T/RB-PV/output checks.

Use the existing P/E extent tables for the chosen coordinates, not as a
requirement to reconstruct every legacy observation. A test must still fail
for wrong extent, swallowed outer close, missing/duplicate record or changed
accepted structure. Integrate only after this bounded proof and the §5
verification pass close. No PV producer, leading-BracketRow admission,
virtual/Yumark policy, new typed EffectRow owner, or public cutover is included.

### Numeric head with a Call: selected successor contract

A numeric Type atom is invalid in the PV tag-name slot. For this bounded
recovery, the numeric head and its adjacent Call form one structured TagName
Error. The Call retains its ordinary argument and close responsibilities; the
native PV `}` terminates that recovery and remains owned by the enclosing PV.
This deliberately avoids a second payload parse or a split of an already
recognized Type expression. It is a selected recovery rule, not acceptance of
a numeric tag and not a claim that current output is an oracle.

All coordinates below are zero-based UTF-8 byte ranges in ordinary root Type
context with no caller stops or inherited outer closes. `N` denotes the
TagName Error, `A` CallArgument Missing, and `C` TypeCall close Missing. Fresh
record IDs are their zero-based position in the listed order.

| phase/control | source | N range | nested Missing records in order | native PV close |
| --- | --- | --- | --- | --- |
| initial | `:{123( }` | `2..7` | A `7..7`, C `7..7` | `7..8` |
| post-comma | `:{123(F, }` | `2..9` | A `9..9`, C `9..9` | `9..10` |
| post-semicolon | `:{123(F; }` | `2..9` | A `9..9`, C `9..9` | `9..10` |
| after item | `:{123(F }` | `2..8` | C `8..8` | `8..9` |
| no gap | `:{123(F}` | `2..7` | C `7..7` | `7..8` |
| matching local close | `:{123(F )}` | `2..9` | none | `9..10` |

For each row:

- N is `Error`, role `Type(PolymorphicVariantTagName)`, with one
  `OtherCharacter` unexpected token and one `Identifier` expectation, both
  covering its entire range. It is first, before every nested record.
- A is `Missing`, role `Type(CallArgument)`, expecting `TypeExpression`.
  C is `Missing`, role `ClosingDelimiter(TypeCall, Parenthesis)`, expecting
  `Punctuation(Close(Parenthesis))`. Missing records have no unexpected facts.
  Every record has its stated site/expectation range, exactly one expectation,
  `COMMITTED_RECOVERY_RULE` sources and primary expectation index zero.
- N contains the Type expression and native `TypeCallTail` beginning at byte
  5. The Call directly owns the eligible horizontal Whitespace and the listed
  Missing sequence. The matching-local row owns its native `)` at `8..9` and
  emits no Missing. There is no separate recovered PV payload or payload-boundary
  record. The actual PV `}` is outside every Error.
- The base source is fully consumed. Appending `::Next` keeps all records and
  their ranges unchanged; the suffix is a path tail of the completed outer PV
  expression, not part of N. Both runs end at EOF, without pending Item or
  remainder, with the root context unchanged and no outstanding reservation.
- Frozen reconciliation preserves exactly that successor tree, exit/context,
  record fields and order while reusing the supplied frozen IDs. A shifted
  test embedding translates all source coordinates uniformly; it must not
  derive record ranges from the CST afterward.

Accepted numeric controls are ordinary root Types `123` and `123(F)`, not PV
tags. Their acceptance basis is the architecture's authoritative standalone
Type grammar (`TypeAtom := Identifier | SigilIdentifier | Number` and
`TypeTightTail := TypePathTail | TypeCallTail`) and the retained legacy
`type_primary_and_path_segments_keep_their_own_surface_categories` control.
Require full consumption, no recovery record or Error/Missing node, a numeric
atom, and a Call containing `F` only in the second control. This gate changes
neither those accepted forms nor the restriction on numeric path segments.

## 5. Execution and review budget

This contract change began as M3 with architect analysis and independent
compiler/recovery and specification review. Two bounded design repairs make
the scoped supersession and numeric witnesses explicit. The authority split
and retained-invariant review closed; the numeric table is the primary's
resolution of the final pre-write finding, not independently certified output.

The user's subsequent instruction is to work directly without subagents. For
this continuation the primary owns design, implementation and verification;
no further agent review or writer is scheduled. This is an explicit operating
override, not a claim that self-review is independent review. The previous
delimiter implementation and P/E pre-write reviews remain evidence for their
unchanged scope. New expected values are derived from §4 before tests are run.

The selected implementation is internal, local, intended behavior on a hot
path. Check the shared owner and structured-PV consequences, run focused
Type/output/RB checks and one package check at closure after checking resource
safety; defer workspace/public certification to its existing phase. Performance
measurement budget is zero samples/processes unless a material work uncertainty
is found. Unresolved accepted-language choices still require a concrete decision
instead of being inferred from recovery output.

After delimiter integration, specify a bounded current-Item PV recovery gate
and continue the existing typed-owner migration. Completion of the remaining
owner ledger, header/full and embedded consistency, and atomic public cutover
still determines completion of the parser replacement.

## 6. Delimiter integration evidence

The §4 private gate is complete on 2026-09-08. Production changes remain in
the shared delimiter owner only. Tests cover its phase-aware horizontal
ownership and unchanged nonhorizontal/fence/caller cases, all selected P/E and
numeric rows, outer `::Next`, shifted recovery coordinates, prefix/recursive
reservation ordering, native closes and accepted controls. The no-gap E row
retains its existing no-Missing handoff; it is not an eligible horizontal row
and does not acquire T4E behavior from this gate.

Primary verification under the user's no-subagent direction:

- `cargo test -p yu-syntax --lib rewrite::tests::type_expr:: -- --test-threads=1`:
  124 passed, including the selected structured carriers and RB controls;
- the same command with `rewrite::tests::output::`: 4 passed;
- the same command with `rewrite::tests::recovery_output::`: 25 passed;
- `cargo check -p yu-syntax` and scoped rustfmt/diff checks: passed.

The existing test binary's declaration filter still has 33 passes and the same
six known failures, now localized to contextual-boundary/continuation behavior
rather than a build or output-harness defect. No declaration expectation was
changed. Their accepted-input cases are the next owning-responsibility repair.
No workspace/public certification or benchmark was run; measurements remain
zero. No new independent implementation review is claimed for this pass.
