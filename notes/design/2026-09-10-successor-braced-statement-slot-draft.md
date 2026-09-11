# BracedStatementBlock recovery-slot CST draft

Status: Rejected as unnecessary; bounded ordered-CST decoder proved; no
implementation authorization

Date: 2026-09-10

Drafted-by: primary from the BracedStatementBlock Missing collision investigation

Scope: the historical proposed CST distinction for existing required Statement,
Separator and terminal Brace-close slots inside
BracedStatementBlockExpression. It does
not change accepted Statement grammar, statement admission, lexical retry,
indented/root/declaration sequence ownership, current-Item propagation, parser
records, frozen reconciliation, public diagnostics, API migration or
recovery-ledger retirement. Current evidence rejects the proposed topology;
the retained proposal below is historical rationale, not a pending gate.

Governing authority: the Authoritative CST-derived diagnostics amendment,
Error/Invalid topology-ordering addendum and braced Statement sequence
current-Item recovery authority. The amendment permits complete ordered sibling
grammar as slot identity; the strengthened evidence below disproves the former
claim that immediate ancestry alone required new topology.

## Ancestry-only observation and corrected result

The current direct Rowan controls retain distinct Missing records for required
Statement, Statement Separator and local Brace close, yet all three have the
same occurrence path:

```text
BracedStatementBlockExpression > Missing
```

The focused controls are `{,;}` for required Statement Missing before explicit
separator punctuation, `{use a use b}` for Separator Missing before the next
admitted Statement, and `{  ` for terminal local Brace close Missing at EOF.
They preserve source, exact records/ranges, frozen replay and continuation.
Immediate ancestry alone does collide, but the complete ordered direct children
identify every retained witness without a wrapper, Error spelling or parser
record:

| direct Missing context | derived slot |
| --- | --- |
| next direct child is `BlockStatementSeparator` | required Statement |
| next direct child is `Statement` | Statement Separator |
| no later direct child | local closing Brace |

The `{,;}` tree has each required-Statement Missing immediately before its
explicit separator node. `{use a use b}` has the Separator Missing between its
two direct Statement children. `{  ` has direct whitespace followed by a
terminal Close Missing. The nested-For continuation control additionally keeps
the outer accepted `RBrace` terminal and puts its missing separator between the
two outer Statement children. These facts invalidate the candidate's necessity
claim for the bounded slots.

## Rejected candidate retained for history

Do not implement this candidate from this record. It remains below only to
preserve the reviewed alternative and why it was considered before complete
ordered-child evidence existed.

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

## Disposition

The prior nested-For continuation defect remains repaired separately: a
completed braced For body makes the enclosing sequence acquire and dispatch its
own successor, so the enclosing local `RBrace` remains owned by this block.
The bounded current CST is now cataloged through ordered direct-child context.
No `BracedStatementBlockClose` kind, accepted-close wrapper or Separator-Missing
ancestor change is authorized or required by these witnesses. A future proposal
would need a new complete ordered-context collision or another independent
grammar requirement; immediate `Block > Missing` ancestry is not enough.
