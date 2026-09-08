# CaseLike Separator and Catch-close current-Item recovery

Status: Authoritative; private O3b construction complete

Date: 2026-09-09

Approved-by: user through the recovery-selection delegation in
`2026-09-08-successor-recovery-authority-amendment.md`

Scope: missing inter-arm Separator and Catch braced-block local close only.
This includes centralized CatchBlock completion for every sequence exit because
the existing distributed exits omit the same local-close obligation. Pattern,
Handler, Guard, Arrow, Body and malformed-arm ownership remain unchanged.

Authority: Case/Catch recovery contract, accepted trailing-comma sequence,
E12h/i, typed-output §§3--4, and recovery-authority §§1--3.

## Publication and completion

Missing Separator is one zero-width `CaseLike(Separator)` record, expected
punctuation Comma, no unexpected facts, singleton expectation with
`COMMITTED_RECOVERY_RULE` and primary zero. It is emitted at the next admitted
Pattern Item's remaining start before exactly one same-Item retry. It creates
no synthetic separator wrapper and does not scan a Separator Error.

Missing Catch-local `}` is one zero-width `CaseLike(Block)` record, expected
punctuation close Brace, no unexpected facts, singleton expectation and primary
zero. This supersedes the structural gate's colon expectation for
`CaseLike(Block)` only when Catch's already-accepted `{` opened its local
CatchBlock. It retains E12h's role rather than adding vocabulary.

CatchBlock owns finalization after every completed arm-sequence exit: matching
`}` is emitted and completes the block, including after a trailing comma; any
other complete pending Item produces exactly one local-close Missing and stays
pending for its actual owner. An actual trailing comma has no following
mandatory Arm. Deferred remains Deferred. Child records precede the enclosing
close record, and close is not merged into Arrow/Body's selected union.

## Boundary and preservation

At ordinary EOF CatchBlock emits its existing remaining leading before anchoring
the close Missing at EOF. At abstract fence/EOF, caller close, active stop or
other protected Item, retain the whole Item and leading and anchor at the
inspected coordinate or remaining start. Separator leaves next Pattern leading
for ordinary arm entry. Preserve suffix, origin, line entry, sequence policy
and Case/Catch distinctions: CaseInline and same-line CatchBraced infer a
comma; indented and physical-newline CatchBraced rules remain accepted; Catch
inline remains one arm.

No replay, generic API, new lexical scanner, Error relabeling, accepted-layout
change beyond consuming the already-valid trailing-comma `}`, or duplicate
close publication is allowed.

## Evidence

Retain E12i and E12h. E12i is an unchanged ML/judge control: its historical
literal does not reach a Separator slot in the current accepted path, so it
does not authorize a judge change or invented recovery. Prove exact
fresh/shifted/frozen/seeded records with existing Case and CatchBraced
same-Item separator witnesses; explicit comma, newline, indented,
CatchInline and trailing-comma accepted controls; matching close and EOF,
fence, outer-close/active-stop, CRLF/UTF-8/foreign-prefix close handoff;
child Error/combined Arrow-Body record order; and post-comma boundaries.
Existing normalized Catch handler counts remain unchanged; E12h's count remains
one while gaining an exact typed record.

M2: one implementation pass, compiler/recovery and regression review, at most
one repair bundle. Focused CaseLike/normalized/output tests, package check,
format and diff; benchmark zero absent material uncertainty. Synchronize task,
ledger and daily record before commit.
