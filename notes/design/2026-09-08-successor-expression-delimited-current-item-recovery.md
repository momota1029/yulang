# Expression shared-delimited current-Item recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-08

Approved-by: user through the ongoing successor-recovery selection and
simplification delegation

Drafted-by: primary after independent architecture and regression audits

Scope: the raw recovery constructors in `rewrite/delimited.rs` for
ParenthesizedExpression, CallTail, IndexTail, ProjectionTupleTail and
ProjectionRecordTail.  This includes their common current-Item loop and the
record-projection spread RHS.  Field/Path and Colon/With remain separate O3b
owner gates; Statement, literal and public/root dispatch are not included.

Authority: the current recovery-authority amendment, typed-output amendment
§§3--6, expression-tail handoff addendum §§3--5, and the architecture's
parenthesized, Call, Index and Projection delimiter tables.  The tail handoff
does not choose individual recovery recipes.  This document records those
recipes under the user's standing delegation; accepted Yulang2 data remains
evidence only for accepted forms.

## Owner descriptor and exact records

The common loop receives one private finite descriptor.  It is the only source
of its Item, Separator and close roles; it never reconstructs them from a CST
kind or a generic token mapping.

| owner | Item role | Separator role | explicit separators | closing owner and delimiter |
| --- | --- | --- | --- | --- |
| ParenthesizedExpression | `Expression(Nud)` | `Expression(ParenthesizedSeparator)` | comma only | `ExpressionGroup`, Parenthesis |
| CallTail | `Expression(CallArgument)` | `Expression(CallArgumentSeparator)` | comma, semicolon | `ArgumentList`, Parenthesis |
| IndexTail | `Expression(IndexItem)` | `Expression(IndexSeparator)` | comma, semicolon | `IndexTail`, Bracket |
| ProjectionTupleTail | `Expression(ProjectionTupleItem)` | `Expression(ProjectionTupleSeparator)` | comma, semicolon | `ProjectionTupleTail`, Parenthesis |
| ProjectionRecordTail | `Expression(ProjectionRecordItem)` | `Expression(ProjectionRecordSeparator)` | comma, semicolon | `ProjectionRecordTail`, Brace |

An Item role and `Expression(ProjectionRecordSpreadRhs)` expect
`Expression`.  A Separator role expects `DelimitedSequenceSeparator`.  A
close role is `ClosingDelimiter` and expects the matching close punctuation.
Every record has exactly that singleton expectation, the same site and
expectation range, `COMMITTED_RECOVERY_RULE`, and primary index zero.  Missing
has an empty unexpected array and an Error has exactly one
`OtherCharacter` token fact over its emitted nonempty lexical run.  The
separate unclaimed-wrong-close Error has one native
`Punctuation(Close(actual delimiter))` fact over its one-Item extent.  Existing
role vocabulary is sufficient.

## Boundary capability, phases and continuation

The loop owns the descriptor's local explicit separators and matching close.
ParenthesizedExpression accepts comma but not semicolon.  Its semicolon is one
native-token `Expression(ParenthesizedSeparator)` Error, with its whole current
Item extent (including remaining leading), one `Punctuation(Semicolon)` fact
and `DelimitedSequenceSeparator` expectation.  It consumes exactly that Item,
opens a fresh Item slot, and scans once.  The same rule applies initially,
after an item, repeatedly and before a local close; it creates no Item Missing
by itself.  Call, Index and both Projection owners retain comma/semicolon
acceptance.  It also carries a private inherited-close mask containing only
`)`, `]` and `}` capabilities from
enclosing delimiters.  It must not propagate ordinary caller stop bits: they
can be a colon, brace opener, arrow, line rule or an outer separator and are
intentionally shielded by an accepted nested delimiter.  Nested expression and
lexical Error scans receive local stops plus this close-only mask, so an outer
close survives arbitrary delimiter nesting.  A matching local close always
wins over an equal inherited bit.

The loop distinguishes an initial/post-explicit-separator Item slot from the
post-item separator slot.  A leading or repeated explicit separator emits the
Item Missing before consuming that separator.  An admitted next Item without a
permitted separator emits the Separator Missing at its remaining start and is
retried unchanged.  Accepted ML remains one Item; qualifying newline remains a
valid boundary exactly as in the existing owner rules.  No new separator node,
token, scanner, threshold or ML policy is introduced.

An absent close at abstract boundary, EOF, protected inherited close, or the
existing local boundary emits one close Missing and returns the whole pending
Item unchanged.  Its anchor is the inspected abstract coordinate, otherwise
the current remaining start after only the leading that this owner is permitted
to emit.  Ordinary EOF may emit its remaining leading before anchoring; a
protected close and its leading stay untouched.

For a mismatched close, first test the inherited-close capability.  A protected
outer close follows the close-Missing handoff above; it is never consumed or
included in Error.  An unclaimed mismatched close is one native-token Error in
the local close slot, with `Punctuation(Close(actual delimiter))` evidence and
its actual remaining leading and extent, then the loop reads one next Item in
the same phase.  A later local matching close is still accepted normally;
otherwise the distinct local close Missing follows at the resulting boundary.

Before choosing a recovery, an Item bearing a qualifying local newline after a
completed or recovered Item is a valid implicit separator even when its
payload is non-NUD.  The loop changes to a fresh Item slot without consuming
that Item; its leading stays under the local owner.  This same transition is
applied to an Error-run's returned newline-bearing Item, so it cannot retry the
same non-NUD forever.  A newline after an explicit separator remains part of
that one literal-authoritative boundary and enters the fresh Item slot directly.

For a non-NUD, emit its initial leading directly under the local owner, then
emit one maximal lexical Error run.  In the initial/post-separator phase it
uses the Item role; after an admitted item it uses the Separator role.  It
stops before an admitted NUD, explicit separator, qualifying local newline,
any close, exact record spread marker, EOF, abstract boundary, or inherited
protected close.  Internal leading belongs to Error; retry and boundary leading
remains pending.  The run uses the existing sealed Error-run capability and the
same lexical current-Item scanner as ordinary expression scanning; it never
calls a grammar parser or builder from inside Error.  A following NUD retries
the failed Item or the following Item after a recovered separator,
respectively.  If a run instead ends at a separator or boundary, that Error
already represents its phase's failed slot: consume the separator without an
additional Item Missing, or move directly to close handoff.  A later fresh
separator still opens a fresh Item slot.

Record spread retains its native node.  A missing RHS emits
`Expression(ProjectionRecordSpreadRhs)` Missing while preserving the
separator, close, EOF, fence or protected close Item.  Its malformed RHS uses
the same maximal lexical rule with the spread-RHS role.  Error reaching a
boundary does not add a second RHS Missing.  Nested expression owners choose
their own roles after their NUD is admitted.

All exits retain the exact current Item, successor coordinate, line entry,
baseline, threshold, ML mode, fence and ambient context.  The enclosing tail
still follows its existing three exits: normal scan again, same scanned Item at
the outer threshold, or propagated boundary.  No input replay, retained run
vector, CST-derived range, diagnostic sorting, generic recovery API or new role
vocabulary is permitted.  Static cost remains `O(bytes + structural work)`.

## Required evidence and gate limits

Before writing production code, add failing exact-record witnesses for all five
descriptors: empty and accepted controls; leading/repeated separator; the
three Parenthesized semicolon phases (initial, repeated and terminal); missing
close at EOF and abstract fence; malformed Item retry; Item Error then
separator/boundary; same-position Separator Missing; record spread missing and
malformed RHS; and unclaimed wrong close.  Test a nested protected outer close
with its leading, including after a raw run, plus UTF-8, CRLF, nonzero origin,
line-entry and fence controls.  Include LF and CRLF qualifying-newline Error
witnesses with malformed payload on both sides of the boundary.  Each selected
record needs fresh and frozen
reconciliation assertions.  Keep the existing CST/owner, ML, layout, colon,
tail-handoff and nested-call controls unchanged.

The decisive borrowed-close control is an outer Index close pending through a
nested Parenthesized and Call delimiter.  It must produce the inner local
close Missing while leaving the outer `]`, all of its leading and its Item
identity for IndexTail.  A root-level mismatched close remains unclaimed and
therefore produces the local close Error.  Accepted nested braced/colon/If/
Case/For controls prove that close-only propagation has not leaked ordinary
caller stops into a delimiter.

Use M2: one implementation pass, at most two repair bundles, focused
delimiter/recovery/output tests, a package check and scoped format/diff checks.
Measurement budget is zero samples/processes unless a material uncertainty is
found.  Synchronize task, design index, single ledger and daily record before
the coherent commit.  This is O3b construction only; O4 joint certification,
header/full, Yumark convergence and atomic old-parser removal remain open.

## Construction result

The private common loop now uses the finite descriptor, phase-aware typed
publication and close-only inherited capability. It replaces every raw
Missing/Error construction in `rewrite/delimited.rs`; ordinary Item scanning
and sealed lexical Error scanning share the driver's one total lexical
operation. The initial implementation exposed an optional operator-shaped
probe that advanced whitespace on rejection; restoring its lexical transaction
boundary repaired that implementation defect without changing parser policy.

The initial exact-record module failed before production work with four absent
record/boundary witnesses. After construction it contains nine tests covering
all descriptors, fresh/frozen reconciliation, protected nested outer closes,
UTF-8, CRLF, fences, exact spread markers, internal-run leading and accepted
contextual/ML controls. `delimited_recovery` 9, `owners` 23, `tails` 14,
`normalized` 83 and `recovery_output` 25 passed, as did `cargo check -p
yu-syntax`, scoped format and diff checks.

The former Parenthesized `;` no-recovery assertion now expects its specified
Separator Error. The `a.{..@ ..rest}` assertion now has one, not two, Missing
nodes because the spread-RHS Error already represents that failed slot. Both
are direct consequences of this selected successor contract; their source
literals and ownership assertions remain.

Independent specification review closed the pre-write semicolon and
qualifying-newline gaps. An independent post-diff regression audit found no
blocker. This is private O3b construction, not aggregate certification:
Field/Path and Colon/With recovery, literal/Statement/declaration owners,
RB-E, O4, header/full, Yumark and atomic old-parser removal remain open. No
benchmark samples or processes were used.
