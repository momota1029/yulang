# BracedStatementBlock recovery-slot CST draft

Status: Draft; no implementation authorization; continuation prerequisite repaired

Date: 2026-09-10

Drafted-by: primary from the BracedStatementBlock Missing collision investigation

Scope: a proposed CST distinction for existing required Statement, Separator
and terminal Brace-close slots inside BracedStatementBlockExpression. It does
not change accepted Statement grammar, statement admission, lexical retry,
indented/root/declaration sequence ownership, current-Item propagation, parser
records, frozen reconciliation, public diagnostics, API migration or
recovery-ledger retirement.

Governing authority: the Authoritative CST-derived diagnostics amendment,
Error/Invalid topology-ordering addendum and braced Statement sequence
current-Item recovery authority. This Draft records a proven schema gap; it
adds no implementation authority.

## Proven collision

The current direct Rowan controls retain distinct Missing records for required
Statement, Statement Separator and local Brace close, yet all three have the
same occurrence path:

```text
BracedStatementBlockExpression > Missing
```

The focused controls are `{,;}` for required Statement Missing before explicit
separator punctuation, `{use a use b}` for Separator Missing before the next
admitted Statement, and `{  ` for terminal local Brace close Missing at EOF.
They preserve source, exact records/ranges, frozen replay and continuation. No
wrapper or Error spelling identifies the role, so CST-only diagnostics cannot
derive their distinct expectations.

## Candidate decision requiring user approval

Reuse existing `BlockStatementSeparator` for Separator Missing and add one
transparent terminal node:

```text
BracedStatementBlockClose := RBrace | Missing
```

The XML-like structural inventory is:

```text
BracedStatementBlockExpression :=
  LBrace OpeningTrivia
  (Statement | Missing(Statement) | Error+ | OrdinaryOwnedTrivia
   | BlockStatementSeparator)*
  BracedStatementBlockClose

BlockStatementSeparator := existing explicit/newline separator children
                         | Missing(Separator)

BracedStatementBlockClose := RBrace | Missing(CloseBrace)
```

This is not permission to accept arbitrary child order: the existing
required-item → successor/separator → terminal transition table remains the
grammar authority. Required Statement Missing stays direct. One Separator
Missing is inside `BlockStatementSeparator`; one Close Missing is inside the
exactly-one terminal Close node. Existing direct Statement Error remains direct.

Each committed braced block has exactly one `BracedStatementBlockClose`,
containing its accepted local `RBrace` or direct zero-width Close Missing. The
node has no independent diagnostic. Empty/trailing-separator forms add no
Statement Missing. Matching foreign close and protected caller/fence Item remain
outside; no node consumes or emits their leading/payload/suffix.

## Source, leading and handoff contract

Separator Missing is opened only at the existing successor slot and finishes
before the admitted following Statement. Its present separator leading retains
the existing separator owner. An accepted local close's native leading is
Close content only when no separator already owns it; separator-owned leading
remains in `BlockStatementSeparator`. Fresh ordinary-EOF remaining leading
stays direct block content before opening the zero-width Close node. Statement
Error initial leading remains outside Error; Error-internal leading remains
inside; retry/boundary leading retains its existing owner.

No wrapper creates a scan, builder state, source replay, layout decision,
expectation payload, `Invalid`, Error node or generic recovery operation. The
terminal node finishes before every caller continuation. Current records and
frozen reconciliation remain unchanged during this topology gate.

## Alternatives not selected by this draft

- A Close node alone leaves the proved Statement-versus-Separator Missing
  collision unresolved.
- New wrappers for every Statement/role add unneeded accepted-tree topology;
  direct Statement context already supplies its singleton expectation.
- Missing-specific kinds, parser metadata, Error spelling/provenance or
  expectation payloads duplicate diagnostic classification outside the CST.
- `Invalid` conflicts with its restricted structured-recovery meaning.
- Altering global Statement/root/indented recovery exceeds this owner-local
  repair.

## Required approval and construction gate

The prior nested-For continuation defect is repaired separately: a completed
braced For body now makes the enclosing sequence acquire and dispatch its own
successor, so the enclosing local `RBrace` remains owned by this block. That
repair changes no CST topology or SyntaxKind and does not authorize this Draft.

Before implementation, renewed independent specification and compiler/recovery
review must validate this Draft. The user must approve the
`BracedStatementBlockClose` name, one terminal node on every braced block
including accepted `RBrace`, reuse of `BlockStatementSeparator` for Separator
Missing, the leading-containment rule above, and this narrow supersession only:
the accepted local-close ancestry/remaining-leading containment and the
Separator/Close Missing placements for these paths. All other legacy direct
children remain unchanged.

After approval, use M2: append one SyntaxKind without renumbering existing
values; one owner-local implementation/repair bundle; focused evidence for all
three slots, both close paths, accepted/empty/trailing/repeated separators,
Error retry, EOF/UTF-8/CRLF/fence/foreign-close handoff, shifted/frozen records
and all six braced entry routes; one scoped closure review; package check,
format and diff. No benchmark samples/processes are planned unless material
cost uncertainty appears.

Stop if source/records/order/current Item/leading/continuation/Statement
admission changes, if a terminal route lacks exactly one Close child, if a
protected Item enters Close, if an existing kind changes value, or if another
owner needs either structure.
