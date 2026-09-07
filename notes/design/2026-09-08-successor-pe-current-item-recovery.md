# Parenthesized and EffectRow current-Item recovery

Status: Authoritative; private P/E-owned construction complete

Date: 2026-09-08

Scope: remaining private Parenthesized/EffectRow Item, Separator and Close
recovery in `rewrite/type_expr/delimited.rs`. BracketRow and Call keep their
separate recovery procedures. Aggregate Type/O6/public certification is later.

Approved-by: user through the recovery-selection and simplification delegation
in `2026-09-08-successor-recovery-authority-amendment.md`

Drafted-and-checked-by: primary, under the user's no-subagent instruction

## Selected rules

The accepted Type grammar, the completed ordinary-horizontal boundary rule and
the outer-TypeApply provenance contract remain in force. EffectRow now uses
the same already-approved provenance activation as Parenthesized: standalone
`'[F A]` remains one TypeApply item, while `G '[F A]` has two items separated
by the EffectRow-owned Missing separator. Explicit separators, qualifying
newlines, actual closes and protected caller/outer/fence boundaries have
priority over a Missing separator.

The remaining recovery is selected from current Items:

1. A malformed P/E item is one forward run to a Type NUD, local separator,
   newline, close, explicit caller stop, abstract boundary or EOF. It publishes
   one Item Error. Initial and retry leading belong directly to the P/E owner;
   intermediate malformed Items keep their leading in the Error. On a valid
   retry, continue the same slot without another Item Missing. This supersedes
   only the P/E retry-leading inclusion/eighth-terminal proposal in the T4
   register amendment §3. No new partial-Item capability is required.
2. An actual matching close is consumed. A known outer/caller close is returned
   with a Missing for the current close. An unclaimed mismatched closer is a
   one-token close Error; consume it and retry the delimiter list. A later EOF
   or protected boundary publishes a close Missing there. P/E share this rule;
   there is no EffectRow-specific suppression of that later missing close.
   The same retry handoff as an Item Error applies: caller words stay pending,
   and an admitted retry's leading is emitted directly under P/E before its
   TypeExpression. Actual matching closes still outrank an explicit stop.
3. After a completed item, an otherwise malformed local token enters the same
   Item-error recovery. It does not silently end the accepted delimiter owner.
   Empty-gap valid Type NUDs receive the owner's Missing separator. Inherited
   Type-ML valid NUDs receive it after owner-emitted continuation trivia.
4. Existing empty/open/post-separator Missing-item decisions remain intact.
   Every P/E-created Error/Missing publishes a typed record. Protected leading
   stays pending except for the explicitly approved ordinary-horizontal rule;
   recovery-run handoff excludes the retry/boundary Item's leading from Error.

The old register's local-close Error child is superseded only for P/E: use its
native punctuation kind and concrete unexpected punctuation category. All
other accepted trees, Call typed fields/terminals, BracketRow handling,
structured reservations and effect-free/frozen contracts remain in force.
The unimplemented primary-completion/scalar-equality prerequisites are not
reintroduced. This gate does not broaden NonTypeApply provenance activation.

## Site ledger and pre-write controls

All P/E Missing/Error records have one same-role/range expectation with
`COMMITTED_RECOVERY_RULE` and primary index zero. Missing has no unexpected
facts. Item Error has one OtherCharacter fact over its complete nonempty
emitted run. Close Error has the actual close punctuation fact. Item expects
TypeExpression; Separator expects DelimitedSequenceSeparator; Close expects
the owner's matching punctuation. Existing P close-Missing coordinates remain
unchanged; newly typed E uses inspected-boundary coordinates or the current
Item's remaining-start after any owner emission.

| source | owner / ordered records |
| --- | --- |
| `(,)` / `'[,]` | P/E Item Missing at `1` / `2` |
| `(@ A)` / `'[@ A]` | P/E Item Error `1..2` / `2..3`; space outside Error, same-slot retry |
| `(@ . A)` | P Item Error `1..4`; next space outside Error |
| `(A @ B)` | P Item Error `3..4`; actual `)` retained |
| `(A{})` / `'[A{}]` | P/E Separator Missing at `2` / `3` |
| `G '[F A]` / `G '[F\n  A]` / `G '[F\r\n  A]` | E Separator Missing at `6` / `8` / `9` |
| `(A` / `'[A` | P/E close Missing at `2` / `3` |
| `(])` / `'[)]` | P/E close Error `1..2` / `2..3`; actual matching close accepted |
| `(]` / `'[)` | P/E close Error then close Missing at `2` / `3` |
| `(] A)` / `'[) A]` | close Error `1..2` / `2..3`; retry space directly under P/E |
| `(] else rest` / `'[) else rest`, explicit ELSE stop | close Error `1..2` / `2..3`, close Missing at `2` / `3`; complete space-plus-word Item stays pending |
| `T((A] )` where `]` is unclaimed | inner P close Error at `4..5`; native `)` closes inner P; outer Call close remains Missing at EOF |
| `:{'[F}` | TagName Error `2..5`, then E close Missing `5..5`; native PV close outside Error |

P/E sources with a malformed prefix followed by an explicit caller word/colon
must stop before the complete leading-plus-token Item. UTF-8, block comments,
LF/CRLF, shifted origin, abstract fence, seeded state and distinct frozen-ID
controls derive from the same rule. Previously frozen no-E-record controls
are construction boundaries and gain exactly the newly migrated E records;
they do not justify suppressing a diagnostic.

For `> > (@\n> > ```\nouter`, P's retained close-Missing anchor is `6` (before
the pending newline). For `> > '[@\n> > ```\nouter`, E's newly typed anchor is
the inspected boundary at `8` (next physical line). Neither parser may emit
the abstract boundary Item; its pending newline and outer source are retained.

The site ledger consists of `emit_delimited_item_missing`,
`emit_inherited_separator_missing`, `emit_delimited_close_missing`, the P/E
malformed-item runner and the P/E mismatched-close branch. Shared BracketRow
raw sites remain identifiable and excluded. Each record precedes later
same-owner recovery and follows earlier source work; a surrounding structured
PV Error still reserves its earlier slot before all nested P/E records.

## Verification and cost

M2 private recovery contract; primary-only implementation/checking, one scoped
repair pass initially budgeted. New P/E controls plus existing Type/PV,
TypeDeclaration, output and recovery-output tests, one package check, format
and diff checks. Aggregate embedded/header/public proof remains open.

Constant owner dispatch and forward Item scans preserve linear source work.
Typed recovery allocates its required records only on malformed input. No
rescan, retained source, new library operation or partial-leading terminal is
introduced. Zero timing samples/processes are budgeted.

## Construction result

Completed 2026-09-08 by the primary without subagents or independent review,
as directed by the user. The finite P/E site ledger above is migrated, including
explicit-caller close records, no-gap/inherited E separators and nested PV
reservation ordering. One local post-Error resume operation handles both Item
and mismatched-close recovery; it guards caller words before emitting retry
leading. Call and BracketRow procedures remain separate.

Twelve earlier tests encoded the no-P/E-record construction stage or superseded
unclaimed-P-close handoff. Their assertions were changed only for the selected
rules above; pending Items, source extent, CST parentage, outer continuation,
seeded cursor and distinct frozen-ID assertions remain. Seven additional P/E
tests cover the new cells and their accepted/protected-boundary controls. The
new fence test initially misused the raw-Item leading emitter on a protected
abstract Item, then used P's older anchor for E. Both fixture mistakes were
corrected against the existing boundary API and the documented E anchor;
production behavior was not changed to accommodate them.

- Type filter: 141 passed; TypeDeclaration: 39 passed.
- Output: 4 passed; recovery output: 25 passed.
- `cargo check -p yu-syntax`, scoped rustfmt and diff checks passed.
- Zero benchmark samples/processes. Broader workspace, production Yumark,
  actual embedded/header-full and aggregate O6/public gates remain open.
